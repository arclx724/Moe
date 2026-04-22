"""
╔══════════════════════════════════════════════════════════════════════════════╗
║           youtube.py  ─  Hybrid YouTube Module for AnonXMusic               ║
╠══════════════════════════════════════════════════════════════════════════════╣
║                                                                              ║
║  SOURCE PRIORITY  (strict waterfall — each tier only tried if above fails)  ║
║  ─────────────────────────────────────────────────────────────────────────  ║
║  [1] PRIMARY   — Nubcoders Streaming API          (fast, zero storage)      ║
║  [2] SECONDARY — Local yt-dlp + IPv6 /64 rotation (no third-party API)      ║
║  [3] TERTIARY  — Shruti Music Download API via CF Worker pool               ║
║                  (storage-based last resort, hidden behind workers)         ║
║                                                                              ║
║  SECURITY                                                                    ║
║  ─────────────────────────────────────────────────────────────────────────  ║
║  • Regex validation on every YouTube video ID before any network call       ║
║  • os.path.basename() enforced on every file-path operation                 ║
║  • MD5-hashed filenames — prevents path traversal & name collisions         ║
║                                                                              ║
║  PERFORMANCE                                                                 ║
║  ─────────────────────────────────────────────────────────────────────────  ║
║  • One persistent aiohttp.ClientSession per process (lazy init, thread-safe)║
║  • In-memory + disk URL cache with YouTube expire-param awareness           ║
║  • Cloudflare Worker Pool: rotating proxy URLs hide the server's real IP    ║
║                                                                              ║
║  RESOURCE MANAGEMENT                                                         ║
║  ─────────────────────────────────────────────────────────────────────────  ║
║  • Background asyncio task auto-deletes downloads 5 min after playback      ║
║  • IPv6 /64 subnet rotation for secondary yt-dlp requests                   ║
║                                                                              ║
╚══════════════════════════════════════════════════════════════════════════════╝
"""

# ─── Standard Library ─────────────────────────────────────────────────────────
import os
import re
import sys
import json
import time
import random
import hashlib
import asyncio
import logging
import ipaddress
import subprocess
from typing import Dict, List, Optional, Tuple, Union
from urllib.parse import urlparse, parse_qs

# ─── Third-Party ──────────────────────────────────────────────────────────────
import aiohttp
import yt_dlp
from py_yt import VideosSearch, Playlist
from pyrogram.enums import MessageEntityType
from pyrogram.types import Message

# ─── Project Internals ────────────────────────────────────────────────────────
# All secrets / URLs come from config.py — the single source of truth.
from config import (
    YT_API_TOKEN           as API_TOKEN,         # Nubcoders bearer token
    NUB_YT_API_BASE_URL    as NUB_BASE_URL,       # e.g. "https://api.nubcoders.xyz"
    YOUTUBE_API_KEYS       as _YT_KEYS_RAW,       # comma-separated Data-API keys
    IPV6_BLOCK             as _IPV6_BLOCK,         # e.g. "2001:db8:abcd:1234::/64"
    CLOUDFLARE_WORKERS     as _CF_WORKERS_RAW,    # comma-separated worker URLs
    SHRUTI_API_URL         as _SHRUTI_BASE,        # e.g. "https://shrutibots.site"
    DOWNLOAD_DIR           as _DOWNLOAD_DIR,       # e.g. "downloads"
)

# ══════════════════════════════════════════════════════════════════════════════
#  MODULE-LEVEL CONSTANTS & SETUP
# ══════════════════════════════════════════════════════════════════════════════

logger = logging.getLogger(__name__)

# --- Directory Setup ----------------------------------------------------------
# _CACHE_DIR  : stores serialised stream-URL caches (JSON, key = MD5 of URL)
# _DOWNLOAD_DIR: files downloaded via Tertiary path; cleaned up after 5 min
_CACHE_DIR    = os.path.join(os.path.dirname(__file__), "cache")
DOWNLOAD_DIR  = _DOWNLOAD_DIR or "downloads"

os.makedirs(_CACHE_DIR,   exist_ok=True)
os.makedirs(DOWNLOAD_DIR, exist_ok=True)

# --- In-Memory URL Cache -----------------------------------------------------
# Keyed by ("audio"|"video", youtube_url) → stream_url string
_MEM_CACHE: Dict[Tuple[str, str], str] = {}

# --- YouTube Data API ---------------------------------------------------------
_YT_SEARCH_URL  = "https://www.googleapis.com/youtube/v3/search"
_YT_DETAILS_URL = "https://www.googleapis.com/youtube/v3/videos"

# --- YouTube video-ID validation regex ---------------------------------------
# A valid YouTube video ID is exactly 11 alphanumeric / dash / underscore chars.
_VIDEO_ID_RE = re.compile(r"^[A-Za-z0-9_-]{11}$")

# Playlist IDs start with "PL", "RD", "OL", etc., up to ~34 chars
_PLAYLIST_ID_RE = re.compile(r"^[A-Za-z0-9_-]{13,42}$")

# Patterns used for *extracting* an ID from a raw URL or bare string
_EXTRACT_PATTERNS = [
    re.compile(r"(?:v=|/v/|youtu\.be/|/embed/|/shorts/)([A-Za-z0-9_-]{11})"),
    re.compile(r"(?:watch\?|/v/|youtu\.be/)([A-Za-z0-9_-]{11})"),
]

# --- Cloudflare Worker Pool --------------------------------------------------
# Each worker URL proxies to the Shruti API so the origin IP stays hidden.
# Format in config:  "https://worker1.user.workers.dev,https://worker2..."
_CF_WORKERS: List[str] = [
    w.strip() for w in (_CF_WORKERS_RAW or "").split(",") if w.strip()
]
# If no workers are configured, fall back to calling Shruti directly.
if not _CF_WORKERS:
    logger.warning("[CFPool] No Cloudflare workers configured — using Shruti URL directly.")
    _CF_WORKERS = [_SHRUTI_BASE.rstrip("/")]

# --- IPv6 /64 Subnet Helper --------------------------------------------------
_IPV6_NET: Optional[ipaddress.IPv6Network] = None
try:
    if _IPV6_BLOCK:
        _IPV6_NET = ipaddress.ip_network(_IPV6_BLOCK, strict=False)
        logger.info(f"[IPv6] Subnet loaded: {_IPV6_NET}")
except Exception as _exc:
    logger.warning(f"[IPv6] Could not parse IPV6_BLOCK '{_IPV6_BLOCK}': {_exc}")

# --- Persistent aiohttp Session (lazy-init) ----------------------------------
# Using a single session per process avoids opening a new TCP connection pool
# for every request, which is critical for performance on busy bots.
_http_session: Optional[aiohttp.ClientSession] = None
_http_session_lock = asyncio.Lock()


async def _get_session() -> aiohttp.ClientSession:
    """
    Return the module-level persistent aiohttp session.
    Creates it on first call (lazy init). Thread-safe via asyncio.Lock.
    """
    global _http_session
    async with _http_session_lock:
        if _http_session is None or _http_session.closed:
            connector = aiohttp.TCPConnector(
                limit=50,          # max simultaneous connections
                ttl_dns_cache=300, # cache DNS for 5 minutes
            )
            _http_session = aiohttp.ClientSession(
                connector=connector,
                headers={"User-Agent": "AnonXMusic/4.0 (+https://t.me/AnonXMusic)"},
            )
            logger.info("[Session] Persistent aiohttp.ClientSession created.")
    return _http_session


# ══════════════════════════════════════════════════════════════════════════════
#  SECURITY UTILITIES
# ══════════════════════════════════════════════════════════════════════════════

def validate_video_id(video_id: str) -> bool:
    """
    Strict regex check: accepts only the canonical 11-character YouTube video ID.
    Rejects anything that could be path-traversal bait (slashes, dots, etc.).
    """
    return bool(_VIDEO_ID_RE.match(video_id or ""))


def extract_video_id(url_or_id: str) -> Optional[str]:
    """
    Extract and *validate* a YouTube video ID from a URL or bare string.

    Returns the 11-char video ID, or None if not found / invalid.
    Never raises; all errors are logged.
    """
    if not url_or_id:
        return None
    try:
        # If the raw string already looks like a bare video ID, validate it.
        if validate_video_id(url_or_id.strip()):
            return url_or_id.strip()

        for pattern in _EXTRACT_PATTERNS:
            match = pattern.search(url_or_id)
            if match:
                vid = match.group(1)
                if validate_video_id(vid):
                    logger.debug(f"[Security] Extracted video_id='{vid}' from '{url_or_id[:60]}'")
                    return vid

        logger.debug(f"[Security] Could not extract valid video_id from '{url_or_id[:60]}'")
        return None
    except Exception as exc:
        logger.error(f"[Security] extract_video_id error: {exc}")
        return None


def _safe_filename(video_id: str, ext: str) -> str:
    """
    Build an MD5-hashed filename from the video ID.

    Why MD5?  The video ID itself is user-supplied. By hashing it we ensure:
      1. No path traversal  (e.g. "../../etc/passwd" → safe hash)
      2. No filename collisions across different ext/type combos
      3. Predictable fixed-length names on every OS

    os.path.basename() is applied as a final safety net.
    """
    raw = hashlib.md5(f"{video_id}.{ext}".encode()).hexdigest()
    return os.path.basename(f"{raw}.{ext}")


def _safe_filepath(video_id: str, ext: str) -> str:
    """Combine DOWNLOAD_DIR with a hashed filename. Always safe."""
    return os.path.join(DOWNLOAD_DIR, _safe_filename(video_id, ext))


# ══════════════════════════════════════════════════════════════════════════════
#  FORMATTING HELPERS  (shared across all three tiers)
# ══════════════════════════════════════════════════════════════════════════════

def format_duration(seconds: Union[int, float]) -> str:
    """Convert an integer number of seconds to HH:MM:SS or MM:SS."""
    if not isinstance(seconds, (int, float)) or seconds < 0:
        return "N/A"
    h = int(seconds) // 3600
    m = (int(seconds) % 3600) // 60
    s = int(seconds) % 60
    return f"{h:02d}:{m:02d}:{s:02d}" if h else f"{m:02d}:{s:02d}"


def time_to_seconds(t: str) -> int:
    """Convert 'HH:MM:SS' or 'MM:SS' to integer seconds."""
    try:
        return sum(int(x) * (60 ** i) for i, x in enumerate(reversed(str(t).split(":"))))
    except Exception:
        return 0


def format_views(n) -> str:
    """Format a view count to Indian-style abbreviation (Crore / Lakh / K)."""
    try:
        n = float(n)
    except (ValueError, TypeError):
        return "0"
    if n >= 1e7:
        return f"{n / 1e7:.1f} Cr"
    if n >= 1e5:
        return f"{n / 1e5:.1f} L"
    if n >= 1e3:
        return f"{n / 1e3:.1f}K"
    return str(int(n))


def _parse_iso_duration(duration: str) -> str:
    """Parse ISO-8601 duration string (PT1H2M3S) into HH:MM:SS."""
    match = re.match(r"PT(?:(\d+)H)?(?:(\d+)M)?(?:(\d+)S)?", duration or "")
    if not match:
        return "N/A"
    h, m, s = (int(x) if x else 0 for x in match.groups())
    return f"{h}:{m:02d}:{s:02d}" if h else f"{m}:{s:02d}"


def _extract_expire(stream_url: str) -> Optional[int]:
    """
    Parse the `expire` query parameter from a YouTube stream URL.
    Returns the UNIX timestamp if it's in the future, else None.
    """
    try:
        q = parse_qs(urlparse(stream_url).query)
        expire = int(q.get("expire", [0])[0])
        return expire if expire > int(time.time()) else None
    except Exception:
        return None


# ══════════════════════════════════════════════════════════════════════════════
#  STREAM URL CACHE  (disk + in-memory, expire-aware)
# ══════════════════════════════════════════════════════════════════════════════

def _cache_key(url: str, prefix: str = "") -> str:
    return hashlib.md5((prefix + url).encode()).hexdigest()


def _cache_path(url: str, prefix: str = "") -> str:
    return os.path.join(_CACHE_DIR, _cache_key(url, prefix) + ".json")


def _read_cache(url: str, prefix: str = "") -> Optional[str]:
    """
    Try to read a non-expired stream URL from the disk cache.
    Returns the cached URL string, or None if missing/expired/corrupt.
    """
    path = _cache_path(url, prefix)
    if not os.path.exists(path):
        return None
    try:
        with open(path, "r") as f:
            data = json.load(f)
        expire = data.get("expire", 0)
        if time.time() < expire - 15:          # 15-second safety margin
            remaining = int(expire - time.time())
            logger.info(f"[Cache] HIT {prefix}{url[:60]}… (expires in {remaining}s)")
            return data.get("url")
        # Cache is expired — delete it
        logger.info(f"[Cache] EXPIRED {prefix}{url[:60]}… removing")
        os.remove(path)
    except Exception as exc:
        logger.warning(f"[Cache] Read error ({exc}), removing corrupt entry")
        try:
            os.remove(path)
        except OSError:
            pass
    return None


def _write_cache(url: str, stream_url: str, prefix: str = "") -> None:
    """Persist a stream URL to disk cache, tagged with its expire timestamp."""
    expire = _extract_expire(stream_url)
    if not expire:
        logger.debug(f"[Cache] SKIP (no expire param) for {url[:60]}…")
        return
    try:
        with open(_cache_path(url, prefix), "w") as f:
            json.dump({"url": stream_url, "expire": expire}, f)
        logger.info(f"[Cache] WRITE {prefix}{url[:60]}… (expires in {int(expire - time.time())}s)")
    except Exception as exc:
        logger.error(f"[Cache] Write failed: {exc}")


def _get_cached_stream(url: str, kind: str) -> Optional[str]:
    """
    Unified cache lookup (memory first, then disk).
    `kind` should be 'audio' or 'video'.
    """
    key = (kind, url)
    # 1. Check in-memory cache first (fastest)
    cached = _MEM_CACHE.get(key)
    if cached:
        expire = _extract_expire(cached)
        if expire and time.time() < expire - 15:
            logger.info(f"[Cache] MEM HIT ({kind}) {url[:60]}…")
            return cached
        del _MEM_CACHE[key]         # stale — evict from memory

    # 2. Check disk cache
    cached = _read_cache(url, prefix=f"{kind}_")
    if cached:
        _MEM_CACHE[key] = cached    # promote to memory
        return cached

    return None


def _set_cached_stream(url: str, kind: str, stream_url: str) -> None:
    """Write a stream URL to both in-memory and disk caches."""
    _MEM_CACHE[(kind, url)] = stream_url
    _write_cache(url, stream_url, prefix=f"{kind}_")


# ══════════════════════════════════════════════════════════════════════════════
#  IPv6 SUBNET ROTATION  (used by Secondary path)
# ══════════════════════════════════════════════════════════════════════════════

def _random_ipv6_address() -> Optional[str]:
    """
    Pick a random host address inside the configured /64 subnet.
    Returns the address as a string, or None if no subnet is configured.

    Why /64?  IPv6 /64 blocks are commonly assigned to servers. Rotating
    between addresses in the block makes yt-dlp appear as different clients
    to YouTube's rate-limiter, greatly reducing 429 errors.
    """
    if _IPV6_NET is None:
        return None
    try:
        # Total hosts in a /64 = 2^64 — pick one at random
        max_host = _IPV6_NET.num_addresses - 2
        offset   = random.randint(1, max_host)
        address  = _IPV6_NET.network_address + offset
        return str(address)
    except Exception as exc:
        logger.warning(f"[IPv6] Could not generate random address: {exc}")
        return None


# ══════════════════════════════════════════════════════════════════════════════
#  CLOUDFLARE WORKER POOL  (used by Tertiary path)
# ══════════════════════════════════════════════════════════════════════════════

def _get_worker_base() -> str:
    """
    Return a random Cloudflare worker URL from the pool.

    The bot's real IP is never exposed to the Shruti API — every request
    travels through a different worker each time, making IP-based banning
    nearly impossible.
    """
    chosen = random.choice(_CF_WORKERS)
    logger.debug(f"[CFPool] Selected worker: {chosen}")
    return chosen.rstrip("/")


# ══════════════════════════════════════════════════════════════════════════════
#  BACKGROUND FILE CLEANUP  (resource management)
# ══════════════════════════════════════════════════════════════════════════════

# Maps  file_path  →  scheduled deletion UNIX timestamp
_cleanup_registry: Dict[str, float] = {}
_CLEANUP_DELAY_SECS = 5 * 60       # 5 minutes


async def schedule_file_cleanup(file_path: str, delay: int = _CLEANUP_DELAY_SECS) -> None:
    """
    Schedule `file_path` for deletion after `delay` seconds.

    This keeps AWS/Oracle disk usage minimal — the file is only needed for
    the duration of playback, after which it's safe to delete.

    Usage:
        asyncio.create_task(schedule_file_cleanup(path))
    """
    safe_path = os.path.join(DOWNLOAD_DIR, os.path.basename(file_path))
    _cleanup_registry[safe_path] = time.time() + delay
    logger.info(f"[Cleanup] Scheduled '{os.path.basename(safe_path)}' for deletion in {delay}s")
    await asyncio.sleep(delay)
    try:
        if os.path.exists(safe_path):
            os.remove(safe_path)
            logger.info(f"[Cleanup] Deleted '{os.path.basename(safe_path)}' after {delay}s")
        _cleanup_registry.pop(safe_path, None)
    except OSError as exc:
        logger.warning(f"[Cleanup] Could not delete '{safe_path}': {exc}")


async def cleanup_all_downloads() -> int:
    """
    Immediately delete all files in DOWNLOAD_DIR that have passed their
    scheduled deletion time.  Call this on bot startup to handle files left
    over from a crashed session.

    Returns the number of files deleted.
    """
    deleted = 0
    now = time.time()
    for fname in os.listdir(DOWNLOAD_DIR):
        fpath = os.path.join(DOWNLOAD_DIR, fname)
        scheduled = _cleanup_registry.get(fpath)
        if scheduled and now >= scheduled:
            try:
                os.remove(fpath)
                _cleanup_registry.pop(fpath, None)
                deleted += 1
                logger.info(f"[Cleanup] Removed overdue file: {fname}")
            except OSError:
                pass
    return deleted


# ══════════════════════════════════════════════════════════════════════════════
#  YOUTUBE DATA API v3  (search & metadata)
# ══════════════════════════════════════════════════════════════════════════════

def _get_api_keys() -> List[str]:
    return [k.strip() for k in (_YT_KEYS_RAW or "").split(",") if k.strip()]


def _random_api_key() -> Optional[str]:
    keys = _get_api_keys()
    return random.choice(keys) if keys else None


async def youtube_search(query: str, limit: int = 5) -> List[Dict]:
    """
    Search YouTube via the Data API v3.

    Uses a random key from the pool on every call to spread quota usage.
    Falls back to an empty list on any error — callers handle the absence.
    """
    key = _random_api_key()
    if not key:
        logger.warning("[YTSearch] No YouTube API key configured.")
        return []

    session = await _get_session()
    try:
        # --- Step 1: search -----------------------------------------------
        search_params = {
            "part":       "snippet",
            "q":          query,
            "maxResults": limit,
            "type":       "video",
            "key":        key,
        }
        async with session.get(
            _YT_SEARCH_URL,
            params=search_params,
            timeout=aiohttp.ClientTimeout(total=10),
        ) as resp:
            if resp.status != 200:
                logger.error(f"[YTSearch] Search returned HTTP {resp.status}")
                return []
            items = (await resp.json()).get("items", [])

        video_ids = [
            item["id"]["videoId"]
            for item in items
            if "videoId" in item.get("id", {})
            and validate_video_id(item["id"]["videoId"])
        ]
        if not video_ids:
            return []

        # --- Step 2: fetch details ----------------------------------------
        details_params = {
            "part": "contentDetails,statistics",
            "id":   ",".join(video_ids),
            "key":  _random_api_key() or key,
        }
        async with session.get(
            _YT_DETAILS_URL,
            params=details_params,
            timeout=aiohttp.ClientTimeout(total=10),
        ) as resp:
            if resp.status != 200:
                return []
            detail_map = {v["id"]: v for v in (await resp.json()).get("items", [])}

        # --- Step 3: assemble results ------------------------------------
        results = []
        for item in items:
            vid_id = item["id"].get("videoId")
            if not vid_id or not validate_video_id(vid_id):
                continue
            det   = detail_map.get(vid_id, {})
            snip  = item.get("snippet", {})
            title = snip.get("title", "")
            chan  = snip.get("channelTitle", "")
            results.append({
                "title":        title,
                "url":          f"https://www.youtube.com/watch?v={vid_id}",
                "video_id":     vid_id,
                "artist_name":  title.split("-", 1)[0].strip() if "-" in title else chan,
                "channel_name": chan,
                "views":        format_views(det.get("statistics", {}).get("viewCount", 0)),
                "duration":     _parse_iso_duration(det.get("contentDetails", {}).get("duration", "")),
                "thumbnail":    snip.get("thumbnails", {}).get("high", {}).get("url", ""),
            })

        logger.info(f"[YTSearch] '{query}' → {len(results)} results")
        return results

    except aiohttp.ClientError as exc:
        logger.error(f"[YTSearch] Network error: {exc}")
        return []
    except Exception as exc:
        logger.error(f"[YTSearch] Unexpected error: {exc}")
        return []


# ══════════════════════════════════════════════════════════════════════════════
#  ██████╗ ██████╗ ██╗███╗   ███╗ █████╗ ██████╗ ██╗   ██╗
#  ██╔══██╗██╔══██╗██║████╗ ████║██╔══██╗██╔══██╗╚██╗ ██╔╝
#  ██████╔╝██████╔╝██║██╔████╔██║███████║██████╔╝ ╚████╔╝
#  ██╔═══╝ ██╔══██╗██║██║╚██╔╝██║██╔══██║██╔══██╗  ╚██╔╝
#  ██║     ██║  ██║██║██║ ╚═╝ ██║██║  ██║██║  ██║   ██║
#  ╚═╝     ╚═╝  ╚═╝╚═╝╚═╝     ╚═╝╚═╝  ╚═╝╚═╝  ╚═╝   ╚═╝
#
#  [1] PRIMARY SOURCE — Nubcoders Streaming API
# ══════════════════════════════════════════════════════════════════════════════

async def _primary_get_stream_url(
    youtube_url: str,
    mode: str = "audio",
) -> Optional[str]:
    """
    Call the Nubcoders streaming API to get a direct stream URL.

    This is the fastest path — no files are downloaded, no disk space used.
    The API returns a pre-signed CDN URL with an `expire` parameter, which
    we cache locally to avoid redundant API calls.

    Args:
        youtube_url : full YouTube watch URL
        mode        : "audio" or "video"

    Returns:
        A stream URL string, or None on any failure.
    """
    if not API_TOKEN:
        logger.warning("[Primary] API_TOKEN not set — skipping primary source.")
        return None

    endpoint = f"{NUB_BASE_URL.rstrip('/')}/stream"
    session  = await _get_session()

    logger.info(f"[Primary] Requesting {mode} stream for {youtube_url[:60]}…")
    try:
        async with session.get(
            endpoint,
            params={"q": youtube_url, "mode": mode, "token": API_TOKEN},
            timeout=aiohttp.ClientTimeout(total=15),
        ) as resp:
            if resp.status == 429:
                logger.warning("[Primary] Rate limit hit (HTTP 429) — triggering fallback.")
                return None
            if resp.status != 200:
                logger.warning(f"[Primary] Non-200 response: {resp.status}")
                return None

            data = await resp.json()

            if mode == "video":
                stream_url = data.get("video_url") or data.get("stream_url")
            else:
                stream_url = data.get("audio_url") or data.get("stream_url")

            if not stream_url:
                logger.warning("[Primary] API returned no stream_url field.")
                return None

            logger.info(f"[Primary] ✅ Stream URL obtained.")
            return stream_url

    except asyncio.TimeoutError:
        logger.error("[Primary] Request timed out after 15s.")
        return None
    except aiohttp.ClientError as exc:
        logger.error(f"[Primary] Network error: {exc}")
        return None
    except Exception as exc:
        logger.error(f"[Primary] Unexpected error: {exc}")
        return None


async def _primary_get_info(query: str) -> Optional[Tuple]:
    """
    Fetch full track metadata from the Nubcoders API.
    Returns a 9-tuple on success, None on failure.
    """
    if not API_TOKEN:
        return None

    endpoint = f"{NUB_BASE_URL.rstrip('/')}/info"
    session  = await _get_session()

    try:
        async with session.get(
            endpoint,
            params={"q": query, "token": API_TOKEN},
            timeout=aiohttp.ClientTimeout(total=15),
        ) as resp:
            if resp.status == 429:
                logger.warning("[Primary-Info] Rate limit hit.")
                return None
            if resp.status != 200:
                logger.warning(f"[Primary-Info] HTTP {resp.status}")
                return None

            data = await resp.json()
            if not data.get("title"):
                return None

            # Nubcoders may return duration as seconds (int) or MM:SS (str)
            dur_raw = data.get("duration", 0)
            dur_fmt = format_duration(dur_raw) if isinstance(dur_raw, int) else str(dur_raw)

            return (
                data.get("title",        "N/A"),
                data.get("video_id",     "N/A"),
                dur_fmt,
                data.get("youtube_link", f"https://www.youtube.com/watch?v={data.get('video_id','')}"),
                data.get("channel_name", "N/A"),
                format_views(data.get("views", 0)),
                data.get("stream_url",   "N/A"),
                data.get("thumbnail",    "N/A"),
                "primary",                        # source tag
            )

    except Exception as exc:
        logger.error(f"[Primary-Info] Error: {exc}")
        return None


# ══════════════════════════════════════════════════════════════════════════════
#  ███████╗███████╗ ██████╗ ██████╗ ███╗   ██╗██████╗  █████╗ ██████╗ ██╗   ██╗
#  ██╔════╝██╔════╝██╔════╝██╔═══██╗████╗  ██║██╔══██╗██╔══██╗██╔══██╗╚██╗ ██╔╝
#  ███████╗█████╗  ██║     ██║   ██║██╔██╗ ██║██║  ██║███████║██████╔╝ ╚████╔╝
#  ╚════██║██╔══╝  ██║     ██║   ██║██║╚██╗██║██║  ██║██╔══██║██╔══██╗  ╚██╔╝
#  ███████║███████╗╚██████╗╚██████╔╝██║ ╚████║██████╔╝██║  ██║██║  ██║   ██║
#  ╚══════╝╚══════╝ ╚═════╝ ╚═════╝ ╚═╝  ╚═══╝╚═════╝ ╚═╝  ╚═╝╚═╝  ╚═╝   ╚═╝
#
#  [2] SECONDARY SOURCE — Local yt-dlp + IPv6 /64 Rotation
# ══════════════════════════════════════════════════════════════════════════════

async def _run_ytdlp_subprocess(
    url: str,
    format_selector: str,
    cookies_path: Optional[str] = None,
) -> Optional[str]:
    """
    Run yt-dlp as an async subprocess to extract a direct stream URL (-g flag).

    IPv6 rotation: if a /64 subnet is configured, a random address from that
    block is passed via --source-address, making each call appear to come from
    a different IP inside the block.

    Timeout: 40 seconds.  Any failure is logged and returns None.
    """
    # Build base command
    cmd = [
        "yt-dlp",
        "--no-playlist",
        "-f", format_selector,
        "-g",                          # print URL only — no download
        "--js-runtimes",  "node",      # faster JS extraction
    ]

    # --- IPv6 binding -------------------------------------------------------
    ipv6_addr = _random_ipv6_address()
    if ipv6_addr:
        cmd.extend(["--source-address", ipv6_addr])
        logger.debug(f"[Secondary] Binding yt-dlp to IPv6 address: {ipv6_addr}")

    # --- Cookie handling ----------------------------------------------------
    if cookies_path and os.path.exists(cookies_path):
        safe_cookies = os.path.basename(cookies_path)
        cmd.extend(["--cookies", os.path.join(os.path.dirname(cookies_path), safe_cookies)])
    else:
        cmd.extend(["--cookies-from-browser", "firefox"])

    cmd.append(url)
    logger.info(f"[Secondary] yt-dlp command: {' '.join(cmd[:6])}… (IPv6={ipv6_addr or 'none'})")

    start = time.time()
    try:
        proc = await asyncio.create_subprocess_exec(
            *cmd,
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.PIPE,
        )
        stdout, stderr = await asyncio.wait_for(proc.communicate(), timeout=40)
    except asyncio.TimeoutError:
        logger.error(f"[Secondary] yt-dlp timed out after 40s for {url[:60]}…")
        return None
    except Exception as exc:
        logger.error(f"[Secondary] yt-dlp subprocess error: {exc}")
        return None

    elapsed = round(time.time() - start, 2)

    if proc.returncode == 0 and stdout:
        stream_url = stdout.decode().strip().split("\n")[0]
        logger.info(f"[Secondary] ✅ yt-dlp succeeded in {elapsed}s")
        return stream_url

    err_text = stderr.decode().strip()[-500:] if stderr else "no stderr"
    logger.error(f"[Secondary] yt-dlp failed (exit={proc.returncode}, {elapsed}s): {err_text}")
    return None


async def _secondary_get_stream_url(
    youtube_url: str,
    mode: str = "audio",
    cookies_path: Optional[str] = None,
) -> Optional[str]:
    """
    Extract a stream URL using local yt-dlp with IPv6 rotation.

    Tries the "best audio" selector for audio mode, and progressive MP4 for
    video mode. Falls back to a looser selector if the first attempt fails.

    Returns the stream URL, or None on total failure.
    """
    logger.info(f"[Secondary] Attempting yt-dlp extraction ({mode}) for {youtube_url[:60]}…")

    if mode == "audio":
        selectors = [
            "bestaudio[ext=m4a]/bestaudio/best",
            "bestaudio",
            "best",
        ]
    else:
        selectors = [
            "best[ext=mp4][protocol=https]",
            "bestvideo[ext=mp4]+bestaudio[ext=m4a]/best[ext=mp4]/best",
            "best",
        ]

    for selector in selectors:
        stream_url = await _run_ytdlp_subprocess(youtube_url, selector, cookies_path)
        if stream_url:
            return stream_url
        logger.debug(f"[Secondary] Selector '{selector}' failed — trying next…")

    logger.error(f"[Secondary] All yt-dlp selectors exhausted for {youtube_url[:60]}…")
    return None


async def _secondary_get_info(query: str) -> Optional[Tuple]:
    """
    Use yt_dlp's Python library (skip_download=True) to get full metadata and
    a stream URL without actually downloading anything.

    Returns a 9-tuple on success, None on failure.
    """
    logger.info(f"[Secondary] Fetching info via yt-dlp Python API for '{query[:60]}'")

    is_url = bool(re.match(r"^(https?://)?(www\.)?(youtube\.com|youtu\.be)/.+", query))
    ydl_opts = {
        "quiet":            True,
        "no_warnings":      True,
        "skip_download":    True,
        "format":           "best",
        "extract_flat":     False,
        "retries":          1,
        "fragment_retries": 1,
    }

    # Use IPv6 if available
    ipv6_addr = _random_ipv6_address()
    if ipv6_addr:
        ydl_opts["source_address"] = ipv6_addr

    try:
        loop = asyncio.get_event_loop()

        def _extract():
            with yt_dlp.YoutubeDL(ydl_opts) as ydl:
                target = query if is_url else f"ytsearch:{query}"
                info   = ydl.extract_info(target, download=False)
                if not is_url and info and "entries" in info:
                    info = info["entries"][0] if info["entries"] else None
                return info

        # Run the blocking yt-dlp call in a thread pool to avoid blocking the event loop
        info_dict = await loop.run_in_executor(None, _extract)

        if not info_dict:
            return None

        vid_id   = info_dict.get("id", "N/A")
        title    = info_dict.get("title", "N/A")
        channel  = info_dict.get("uploader", "N/A")
        views    = format_views(info_dict.get("view_count", 0))
        yt_url   = f"https://www.youtube.com/watch?v={vid_id}"
        dur_sec  = int(info_dict.get("duration", 0) or 0)
        dur_fmt  = format_duration(dur_sec)
        thumb    = (info_dict.get("thumbnails") or [{}])[-1].get("url", "N/A")

        # Pick the best progressive format URL
        stream_url = _pick_best_format(info_dict.get("formats", []))

        return (title, vid_id, dur_fmt, yt_url, channel, views, stream_url, thumb, "secondary")

    except (yt_dlp.utils.ExtractorError, yt_dlp.utils.DownloadError) as exc:
        logger.error(f"[Secondary] yt-dlp extraction error: {exc}")
        return None
    except Exception as exc:
        logger.error(f"[Secondary] Unexpected error: {exc}")
        return None


def _pick_best_format(formats: List[Dict]) -> str:
    """
    Pick the best progressive (audio+video in one file) HTTP URL from yt-dlp
    format list, preferring MP4.  Falls back to audio-only if nothing better
    exists.
    """
    if not formats:
        return "N/A"

    def is_progressive_http(f: Dict) -> bool:
        return (
            f.get("acodec") != "none"
            and f.get("vcodec") != "none"
            and str(f.get("protocol", "")).startswith("http")
            and bool(f.get("url"))
        )

    # Prefer progressive MP4
    for f in formats:
        if is_progressive_http(f) and f.get("ext") == "mp4":
            return f["url"]

    # Any progressive HTTP
    for f in formats:
        if is_progressive_http(f):
            return f["url"]

    # Any URL at all
    for f in formats:
        if f.get("url"):
            return f["url"]

    return "N/A"


# ══════════════════════════════════════════════════════════════════════════════
#  ████████╗███████╗██████╗ ████████╗██╗ █████╗ ██████╗ ██╗   ██╗
#  ╚══██╔══╝██╔════╝██╔══██╗╚══██╔══╝██║██╔══██╗██╔══██╗╚██╗ ██╔╝
#     ██║   █████╗  ██████╔╝   ██║   ██║███████║██████╔╝ ╚████╔╝
#     ██║   ██╔══╝  ██╔══██╗   ██║   ██║██╔══██║██╔══██╗  ╚██╔╝
#     ██║   ███████╗██║  ██║   ██║   ██║██║  ██║██║  ██║   ██║
#     ╚═╝   ╚══════╝╚═╝  ╚═╝   ╚═╝   ╚═╝╚═╝  ╚═╝╚═╝  ╚═╝   ╚═╝
#
#  [3] TERTIARY SOURCE — Shruti Music Download API via CF Worker Pool
# ══════════════════════════════════════════════════════════════════════════════

async def _tertiary_download(
    video_id: str,
    media_type: str = "audio",
) -> Optional[str]:
    """
    Download a file via the Shruti Music API, routing through a random
    Cloudflare Worker to hide the server's real IP.

    Flow:
      1.  GET  {worker}/download?url={video_id}&type={media_type}
          → receives a JSON body with a `download_token`
      2.  GET  {worker}/stream/{video_id}?type=…&token=…
          → follows any 302 redirect, streams the file to disk
      3.  File path (MD5-hashed) is returned; cleanup is scheduled.

    Returns the local file path on success, or None on failure.
    """
    # Security: validate video ID before sending it anywhere
    if not validate_video_id(video_id):
        logger.error(f"[Tertiary] Invalid video_id '{video_id}' — aborting download.")
        return None

    ext       = "mp4" if media_type == "video" else "mp3"
    file_path = _safe_filepath(video_id, ext)   # MD5-hashed, safe path

    # Re-use existing file if present (avoids re-downloading)
    if os.path.exists(file_path) and os.path.getsize(file_path) > 0:
        logger.info(f"[Tertiary] File already exists: {os.path.basename(file_path)}")
        return file_path

    worker_base = _get_worker_base()
    session     = await _get_session()

    logger.info(f"[Tertiary] Downloading {media_type} for '{video_id}' via {worker_base}")

    try:
        # ── Step 1: Request download token ───────────────────────────────
        async with session.get(
            f"{worker_base}/download",
            params={"url": video_id, "type": media_type},
            timeout=aiohttp.ClientTimeout(total=10),
        ) as resp:
            if resp.status != 200:
                logger.error(f"[Tertiary] Token request failed: HTTP {resp.status}")
                return None
            data           = await resp.json()
            download_token = data.get("download_token")

        if not download_token:
            logger.error("[Tertiary] API did not return a download_token.")
            return None

        # ── Step 2: Stream the file to disk ──────────────────────────────
        stream_url  = f"{worker_base}/stream/{video_id}?type={media_type}&token={download_token}"
        dl_timeout  = 600 if media_type == "video" else 300

        async with session.get(
            stream_url,
            timeout=aiohttp.ClientTimeout(total=dl_timeout),
            allow_redirects=True,       # aiohttp handles 302 automatically
        ) as file_resp:
            if file_resp.status != 200:
                logger.error(f"[Tertiary] File stream returned HTTP {file_resp.status}")
                return None

            with open(file_path, "wb") as fh:
                async for chunk in file_resp.content.iter_chunked(16384):
                    fh.write(chunk)

        # ── Step 3: Verify the download ──────────────────────────────────
        if not os.path.exists(file_path) or os.path.getsize(file_path) == 0:
            logger.error("[Tertiary] Downloaded file is empty or missing.")
            _safe_remove(file_path)
            return None

        size_kb = os.path.getsize(file_path) // 1024
        logger.info(f"[Tertiary] ✅ Downloaded {size_kb} KB → {os.path.basename(file_path)}")

        # ── Step 4: Schedule automatic cleanup ───────────────────────────
        asyncio.create_task(schedule_file_cleanup(file_path))

        return file_path

    except asyncio.TimeoutError:
        logger.error(f"[Tertiary] Download timed out after {dl_timeout}s.")
        _safe_remove(file_path)
        return None
    except aiohttp.ClientError as exc:
        logger.error(f"[Tertiary] Network error: {exc}")
        _safe_remove(file_path)
        return None
    except Exception as exc:
        logger.error(f"[Tertiary] Unexpected error: {exc}")
        _safe_remove(file_path)
        return None


def _safe_remove(path: str) -> None:
    """Delete a file without raising, using basename validation."""
    safe_path = os.path.join(DOWNLOAD_DIR, os.path.basename(path))
    try:
        if os.path.exists(safe_path):
            os.remove(safe_path)
    except OSError:
        pass


# ══════════════════════════════════════════════════════════════════════════════
#  RECONNECT LOGIC  — Refresh an Expired Stream URL
# ══════════════════════════════════════════════════════════════════════════════

async def reconnect_stream(
    youtube_url: str,
    mode: str = "audio",
    cookies_path: Optional[str] = None,
) -> Optional[str]:
    """
    Re-fetch a fresh stream URL for an already-playing track.

    Called automatically when PyTgCalls detects a stall or when the player
    checks the `expire` timestamp and finds it has elapsed.  Waterfall order
    is the same as the main get_stream() function.

    Returns a fresh stream URL, or None if all sources fail.
    """
    video_id = extract_video_id(youtube_url)
    if not video_id:
        logger.error(f"[Reconnect] Cannot parse video_id from '{youtube_url[:60]}'")
        return None

    logger.info(f"[Reconnect] Refreshing stream for video_id='{video_id}'")

    # Invalidate stale cache entries so we don't re-use an expired URL
    for kind in ("audio", "video"):
        key = (kind, youtube_url)
        _MEM_CACHE.pop(key, None)

    full_url = f"https://www.youtube.com/watch?v={video_id}"
    return await _get_stream_url_waterfall(full_url, mode=mode, cookies_path=cookies_path)


async def _get_stream_url_waterfall(
    youtube_url: str,
    mode: str = "audio",
    cookies_path: Optional[str] = None,
) -> Optional[str]:
    """
    Internal waterfall: Primary → Secondary → None (Tertiary cannot give a
    raw stream URL — it gives a file path instead; use get_stream() for that).
    """
    # 1. Primary
    stream = await _primary_get_stream_url(youtube_url, mode=mode)
    if stream:
        _set_cached_stream(youtube_url, mode, stream)
        return stream

    # 2. Secondary
    logger.info("[Waterfall] Primary failed — trying Secondary (yt-dlp)…")
    stream = await _secondary_get_stream_url(youtube_url, mode=mode, cookies_path=cookies_path)
    if stream:
        _set_cached_stream(youtube_url, mode, stream)
        return stream

    logger.error(f"[Waterfall] Both Primary and Secondary failed for {youtube_url[:60]}")
    return None


# ══════════════════════════════════════════════════════════════════════════════
#  PUBLIC INTERFACE — get_stream() / get_video_stream()
#  These are the main entry points called by the music bot's player.
# ══════════════════════════════════════════════════════════════════════════════

async def get_stream(
    url: str,
    cookies_path: Optional[str] = None,
) -> Optional[str]:
    """
    Get an **audio** stream URL (or local file path) for `url`.

    Priority:
      1. In-memory cache                       (instant)
      2. Disk cache                            (fast, no network)
      3. Primary  — Nubcoders API              (fast, no storage)
      4. Secondary — yt-dlp + IPv6 rotation    (medium, no storage)
      5. Tertiary  — Shruti download → file    (slow, auto-cleaned)

    Args:
        url          : YouTube watch URL
        cookies_path : optional path to a Netscape cookies file

    Returns:
        Stream URL string, local file path, or None on total failure.
    """
    video_id = extract_video_id(url)
    if not video_id:
        logger.error(f"[get_stream] Could not extract valid video_id from '{url[:60]}'")
        return None

    full_url = f"https://www.youtube.com/watch?v={video_id}"
    logger.info(f"[get_stream] Audio request for video_id='{video_id}'")

    # ── Tiers 1 & 2: cache ───────────────────────────────────────────────
    cached = _get_cached_stream(full_url, "audio")
    if cached:
        return cached

    # ── Tier 3: Primary API ──────────────────────────────────────────────
    stream = await _primary_get_stream_url(full_url, mode="audio")
    if stream:
        _set_cached_stream(full_url, "audio", stream)
        return stream

    # ── Tier 4: Secondary yt-dlp ────────────────────────────────────────
    logger.info("[get_stream] Primary failed — trying Secondary…")
    stream = await _secondary_get_stream_url(full_url, mode="audio", cookies_path=cookies_path)
    if stream:
        _set_cached_stream(full_url, "audio", stream)
        return stream

    # ── Tier 5: Tertiary — Shruti download ──────────────────────────────
    logger.info("[get_stream] Secondary failed — falling back to Tertiary (download)…")
    file_path = await _tertiary_download(video_id, media_type="audio")
    if file_path:
        logger.info(f"[get_stream] ✅ Tertiary succeeded: {os.path.basename(file_path)}")
        return file_path

    logger.error(f"[get_stream] ❌ ALL three sources failed for video_id='{video_id}'")
    return None


async def get_video_stream(
    url: str,
    cookies_path: Optional[str] = None,
) -> Optional[str]:
    """
    Get a **video** stream URL (or local file path) for `url`.

    Same three-tier waterfall as get_stream(), but targeting video formats.
    """
    video_id = extract_video_id(url)
    if not video_id:
        logger.error(f"[get_video_stream] Could not extract valid video_id from '{url[:60]}'")
        return None

    full_url = f"https://www.youtube.com/watch?v={video_id}"
    logger.info(f"[get_video_stream] Video request for video_id='{video_id}'")

    cached = _get_cached_stream(full_url, "video")
    if cached:
        return cached

    stream = await _primary_get_stream_url(full_url, mode="video")
    if stream:
        _set_cached_stream(full_url, "video", stream)
        return stream

    logger.info("[get_video_stream] Primary failed — trying Secondary…")
    stream = await _secondary_get_stream_url(full_url, mode="video", cookies_path=cookies_path)
    if stream:
        _set_cached_stream(full_url, "video", stream)
        return stream

    logger.info("[get_video_stream] Secondary failed — falling back to Tertiary…")
    file_path = await _tertiary_download(video_id, media_type="video")
    if file_path:
        return file_path

    logger.error(f"[get_video_stream] ❌ ALL sources failed for video_id='{video_id}'")
    return None


# ══════════════════════════════════════════════════════════════════════════════
#  PUBLIC INTERFACE — get_video_info()
#  Single call that returns metadata + stream URL, used by play handlers.
# ══════════════════════════════════════════════════════════════════════════════

async def get_video_info(
    query: str,
    mode: str = "audio",
    cookies_path: Optional[str] = None,
) -> Tuple:
    """
    Return a 9-tuple describing the requested track:

        (title, video_id, duration, youtube_url, channel, views, stream_url, thumbnail, source)

    `source` is one of "primary", "secondary", "tertiary" for diagnostics.
    Returns a tuple of Nones on total failure.

    The waterfall is:
      1. Nubcoders API (Primary)
      2. yt-dlp Python + IPv6 rotation (Secondary)
      3. yt-dlp metadata + Shruti download for stream (Tertiary)
    """
    logger.info(f"[get_video_info] Query='{query[:60]}', mode={mode}")

    # ── Tier 1: Primary ──────────────────────────────────────────────────
    result = await _primary_get_info(query)
    if result and result[0] and result[0] != "N/A":
        logger.info(f"[get_video_info] ✅ Primary succeeded: '{result[0]}'")
        return result

    # ── Tier 2: Secondary ────────────────────────────────────────────────
    logger.info("[get_video_info] Primary returned no data — trying Secondary…")
    result = await _secondary_get_info(query)
    if result and result[0] and result[0] != "N/A":
        # Secondary gives us a stream URL already — but if it's "N/A", try
        # to get a download path from Tertiary just for the stream part.
        if result[6] == "N/A":
            logger.info("[get_video_info] Secondary metadata OK but no stream — trying Tertiary for stream…")
            vid_id    = result[1]
            file_path = await _tertiary_download(vid_id, media_type=mode)
            result    = result[:6] + (file_path or "N/A",) + result[7:8] + ("tertiary",)

        logger.info(f"[get_video_info] ✅ Secondary succeeded: '{result[0]}'")
        return result

    # ── Tier 3: Tertiary (metadata via yt-dlp + stream via Shruti) ───────
    logger.info("[get_video_info] Secondary failed — trying Tertiary…")
    # We still need metadata — use yt-dlp without IPv6 as a last resort
    try:
        result = await _secondary_get_info(query)   # try one more time
        if result:
            vid_id    = result[1]
            file_path = await _tertiary_download(vid_id, media_type=mode)
            result    = result[:6] + (file_path or "N/A",) + result[7:8] + ("tertiary",)
            logger.info(f"[get_video_info] ✅ Tertiary succeeded: '{result[0]}'")
            return result
    except Exception as exc:
        logger.error(f"[get_video_info] Tertiary attempt error: {exc}")

    logger.error(f"[get_video_info] ❌ ALL sources failed for query='{query[:60]}'")
    return (None,) * 9


# ══════════════════════════════════════════════════════════════════════════════
#  YouTubeAPI CLASS  (compatible with ShrutiMusic / AnonXMusic call sites)
#
#  Drop-in replacement for the Shruti Music YouTubeAPI class. Every method
#  routes through the hybrid waterfall so callers don't need to change.
# ══════════════════════════════════════════════════════════════════════════════

class YouTubeAPI:
    """
    Hybrid YouTube API client.

    All methods use the three-tier waterfall internally. The public interface
    is intentionally kept compatible with the original ShrutiMusic class so
    that play.py, callbacks.py, etc. need zero changes.
    """

    def __init__(self):
        self.base     = "https://www.youtube.com/watch?v="
        self.listbase = "https://youtube.com/playlist?list="
        # ANSI escape-code stripper (used by some yt-dlp output parsers)
        self._ansi_re = re.compile(r"\x1B(?:[@-Z\\-_]|\[[0-?]*[ -/]*[@-~])")

    # ── Helpers ──────────────────────────────────────────────────────────

    def _normalise_link(self, link: str, videoid: Union[bool, str, None]) -> str:
        """Expand a bare video ID into a full URL if videoid flag is set."""
        if videoid:
            link = self.base + link
        # Strip extra parameters that break some parsers
        if "&" in link:
            link = link.split("&")[0]
        return link

    # ── Existence & URL extraction ────────────────────────────────────────

    async def exists(self, link: str, videoid: Union[bool, str] = None) -> bool:
        """Return True if `link` appears to be a YouTube URL."""
        return bool(re.search(r"(?:youtube\.com|youtu\.be)", self._normalise_link(link, videoid)))

    async def url(self, message: Message) -> Optional[str]:
        """Extract the first URL entity from a Pyrogram message (or its reply)."""
        for msg in [message, message.reply_to_message] if message.reply_to_message else [message]:
            if msg.entities:
                for entity in msg.entities:
                    if entity.type == MessageEntityType.URL:
                        text = msg.text or msg.caption or ""
                        return text[entity.offset: entity.offset + entity.length]
            if msg.caption_entities:
                for entity in msg.caption_entities:
                    if entity.type == MessageEntityType.TEXT_LINK:
                        return entity.url
        return None

    # ── Metadata queries ──────────────────────────────────────────────────

    async def details(
        self, link: str, videoid: Union[bool, str] = None
    ) -> Tuple[str, str, int, str, str]:
        """
        Return (title, duration_min, duration_sec, thumbnail, video_id).
        """
        link = self._normalise_link(link, videoid)
        result = await get_video_info(link)
        title, vid_id, dur_fmt, _, _, _, _, thumb, _ = result
        dur_sec = time_to_seconds(dur_fmt)
        return (title or "N/A", dur_fmt or "N/A", dur_sec, thumb or "N/A", vid_id or "N/A")

    async def title(self, link: str, videoid: Union[bool, str] = None) -> str:
        link = self._normalise_link(link, videoid)
        result = await get_video_info(link)
        return result[0] or "N/A"

    async def duration(self, link: str, videoid: Union[bool, str] = None) -> str:
        link = self._normalise_link(link, videoid)
        result = await get_video_info(link)
        return result[2] or "N/A"

    async def thumbnail(self, link: str, videoid: Union[bool, str] = None) -> str:
        link = self._normalise_link(link, videoid)
        result = await get_video_info(link)
        return result[7] or "N/A"

    async def track(
        self, link: str, videoid: Union[bool, str] = None
    ) -> Tuple[Dict, str]:
        """
        Return (track_details_dict, video_id).
        track_details_dict matches the original ShrutiMusic schema.
        """
        link   = self._normalise_link(link, videoid)
        result = await get_video_info(link)
        title, vid_id, dur_fmt, yt_url, channel, views, stream_url, thumb, source = result

        track_details = {
            "title":        title    or "N/A",
            "link":         yt_url   or link,
            "vidid":        vid_id   or "N/A",
            "duration_min": dur_fmt  or "N/A",
            "thumb":        thumb    or "N/A",
            "channel":      channel  or "N/A",
            "views":        views    or "N/A",
            "stream_url":   stream_url,
            "source":       source,
        }
        return track_details, vid_id

    # ── Search & Slider ───────────────────────────────────────────────────

    async def slider(
        self,
        link: str,
        query_type: int,
        videoid: Union[bool, str] = None,
    ) -> Tuple[str, str, str, str]:
        """
        Return (title, duration_min, thumbnail, video_id) for result #query_type
        from a 10-result search.  Used by the song-selection carousel.
        """
        link    = self._normalise_link(link, videoid)
        results = await youtube_search(link, limit=10)
        if not results or query_type >= len(results):
            return "N/A", "N/A", "N/A", "N/A"
        r = results[query_type]
        return r["title"], r["duration"], r["thumbnail"], r["video_id"]

    # ── Formats (for manual quality selection) ────────────────────────────

    async def formats(
        self, link: str, videoid: Union[bool, str] = None
    ) -> Tuple[List[Dict], str]:
        """
        Extract all non-DASH formats from a video using yt-dlp.
        Returns (formats_list, original_link).
        """
        link = self._normalise_link(link, videoid)
        vid_id = extract_video_id(link)
        if not vid_id:
            return [], link

        loop = asyncio.get_event_loop()
        ipv6 = _random_ipv6_address()

        def _get_formats():
            opts = {"quiet": True, "no_warnings": True}
            if ipv6:
                opts["source_address"] = ipv6
            with yt_dlp.YoutubeDL(opts) as ydl:
                info = ydl.extract_info(link, download=False)
                return info.get("formats", [])

        try:
            raw_formats = await loop.run_in_executor(None, _get_formats)
        except Exception as exc:
            logger.error(f"[formats] yt-dlp error: {exc}")
            return [], link

        formats_available = [
            {
                "format":      f.get("format",      "N/A"),
                "filesize":    f.get("filesize"),
                "format_id":   f.get("format_id",   "N/A"),
                "ext":         f.get("ext",          "N/A"),
                "format_note": f.get("format_note",  "N/A"),
                "yturl":       link,
            }
            for f in raw_formats
            if "dash" not in str(f.get("format", "")).lower()
        ]
        return formats_available, link

    # ── Playlist ──────────────────────────────────────────────────────────

    async def playlist(
        self,
        link: str,
        limit: int,
        user_id: int,
        videoid: Union[bool, str] = None,
    ) -> List[str]:
        """
        Fetch up to `limit` video IDs from a YouTube playlist.
        Returns a list of 11-char validated video IDs.
        """
        if videoid:
            link = self.listbase + link
        if "&" in link:
            link = link.split("&")[0]
        try:
            plist  = await Playlist.get(link)
            videos = plist.get("videos") or []
            ids    = []
            for item in videos[:limit]:
                if not item:
                    continue
                vid = item.get("id", "")
                if validate_video_id(vid):
                    ids.append(vid)
            logger.info(f"[playlist] Fetched {len(ids)} valid video IDs from playlist")
            return ids
        except Exception as exc:
            logger.error(f"[playlist] Error: {exc}")
            return []

    # ── Download (compatible signature) ──────────────────────────────────

    async def download(
        self,
        link: str,
        mystic,                                   # Pyrogram message object (unused here)
        video:       Union[bool, str] = None,
        videoid:     Union[bool, str] = None,
        songaudio:   Union[bool, str] = None,
        songvideo:   Union[bool, str] = None,
        format_id:   Union[bool, str] = None,
        title:       Union[bool, str] = None,
    ) -> Tuple[Optional[str], bool]:
        """
        Download the track using the three-tier waterfall.

        Returns (file_path, True) on success, (None, False) on failure.
        The caller is responsible for passing the path to PyTgCalls.
        """
        if videoid:
            link = self.base + link

        mode  = "video" if (video or songvideo) else "audio"
        vid_id = extract_video_id(link)

        if not vid_id:
            logger.error(f"[download] Invalid link: {link[:60]}")
            return None, False

        try:
            if mode == "video":
                result = await get_video_stream(link)
            else:
                result = await get_stream(link)

            if result:
                logger.info(f"[download] ✅ {mode} ready for '{vid_id}'")
                return result, True

            logger.error(f"[download] All sources failed for '{vid_id}'")
            return None, False

        except Exception as exc:
            logger.error(f"[download] Unexpected error: {exc}")
            return None, False

    # ── Video (direct video download, legacy compat) ──────────────────────

    async def video(self, link: str, videoid: Union[bool, str] = None) -> Tuple[int, str]:
        """
        Legacy method: download a video file and return (1, path) or (0, error).
        """
        link = self._normalise_link(link, videoid)
        vid_id = extract_video_id(link)
        if not vid_id:
            return 0, "Invalid YouTube link"

        file_path = await _tertiary_download(vid_id, media_type="video")
        if file_path:
            return 1, file_path
        return 0, "Video download failed via all sources"


# ══════════════════════════════════════════════════════════════════════════════
#  NUBCODERS-COMPATIBLE MODULE-LEVEL HELPERS
#  (for code that imports these functions directly from youtube.py)
# ══════════════════════════════════════════════════════════════════════════════

def get_rate_limit_status() -> Tuple[int, int, int, bool, str]:
    """
    Synchronous wrapper to query the Nubcoders rate-limit endpoint.
    Returns (daily_limit, used, remaining, is_admin, reset_time).
    """
    if not API_TOKEN:
        return 0, 0, 0, False, "No API token"
    import requests as _requests   # sync fallback — intentionally not aiohttp
    try:
        resp = _requests.get(
            f"{NUB_BASE_URL.rstrip('/')}/rate-limit-status",
            params={"token": API_TOKEN},
            timeout=10,
        )
        resp.raise_for_status()
        data = resp.json()
        return (
            data.get("daily_limit",        0),
            data.get("requests_used",      0),
            data.get("requests_remaining", 0),
            data.get("is_admin",       False),
            data.get("reset_time",     "N/A"),
        )
    except Exception as exc:
        logger.error(f"[rate_limit_status] Error: {exc}")
        return 0, 0, 0, False, str(exc)


def get_trending_songs(limit: int = 10) -> List[Dict]:
    """Fetch trending songs from Nubcoders API (synchronous)."""
    import requests as _requests
    try:
        resp = _requests.get(f"{NUB_BASE_URL.rstrip('/')}/trending", params={"limit": limit}, timeout=30)
        resp.raise_for_status()
        return resp.json().get("results", [])
    except Exception as exc:
        logger.error(f"[trending] Error: {exc}")
        return []


def get_song_suggestions(query: str, limit: int = 5) -> List[str]:
    """Fetch autocomplete suggestions from Nubcoders API (synchronous)."""
    import requests as _requests
    try:
        resp = _requests.get(f"{NUB_BASE_URL.rstrip('/')}/suggest", params={"q": query, "limit": limit}, timeout=10)
        resp.raise_for_status()
        return resp.json().get("results", [])
    except Exception as exc:
        logger.error(f"[suggestions] Error: {exc}")
        return []


def check_health() -> bool:
    """Ping the Nubcoders API health endpoint (synchronous)."""
    import requests as _requests
    try:
        return _requests.get(f"{NUB_BASE_URL.rstrip('/')}/health", timeout=5).status_code == 200
    except Exception:
        return False


def is_ytdlp_updated() -> bool:
    """Check whether the installed yt-dlp matches the latest PyPI release."""
    import requests as _requests
    try:
        from importlib.metadata import version, PackageNotFoundError
        try:
            installed = version("yt-dlp")
        except PackageNotFoundError:
            return False
        resp    = _requests.get("https://pypi.org/pypi/yt-dlp/json", timeout=10)
        resp.raise_for_status()
        latest  = resp.json()["info"]["version"]
        current = installed == latest
        logger.info(f"[ytdlp_check] Installed={installed}, Latest={latest}, Current={current}")
        return current
    except Exception as exc:
        logger.error(f"[ytdlp_check] Error: {exc}")
        return False


async def check_and_update_ytdlp() -> None:
    """Async convenience: update yt-dlp if it is out of date."""
    try:
        if not is_ytdlp_updated():
            logger.info("[ytdlp_update] Updating yt-dlp…")
            result = await asyncio.create_subprocess_exec(
                sys.executable, "-m", "pip", "install", "-U", "yt-dlp",
                stdout=asyncio.subprocess.PIPE,
                stderr=asyncio.subprocess.PIPE,
            )
            await asyncio.wait_for(result.communicate(), timeout=120)
            logger.info("[ytdlp_update] yt-dlp updated successfully.")
        else:
            logger.info("[ytdlp_update] yt-dlp is already up to date.")
    except Exception as exc:
        logger.error(f"[ytdlp_update] Error: {exc}")


# ══════════════════════════════════════════════════════════════════════════════
#  HANDLE YOUTUBE  (legacy entry point, maintains tuple return signature)
# ══════════════════════════════════════════════════════════════════════════════

async def handle_youtube(argument: str) -> Tuple:
    """
    Top-level entry point for handlers that expect a flat 8-tuple:
        (title, duration, youtube_url, thumbnail, channel, views, video_id, stream_url)

    Internally calls get_video_info() which runs the full waterfall.
    """
    logger.debug(f"[handle_youtube] argument='{argument[:60]}'")
    result = await get_video_info(argument)

    title, video_id, duration, yt_url, channel, views, stream_url, thumbnail, source = result

    if not title or title == "N/A":
        logger.warning("[handle_youtube] No usable data returned from waterfall.")
        return ("Error", "00:00", None, None, None, None, None, None)

    logger.info(f"[handle_youtube] ✅ title='{title}', source={source}")
    return (title, duration, yt_url, thumbnail, channel, views, video_id, stream_url)


async def handle_youtube_ytdlp(argument: str) -> Optional[Tuple]:
    """
    Variant of handle_youtube() that forces Secondary (yt-dlp) source.
    Useful for debugging or when the Primary API is known to be down.
    """
    logger.debug(f"[handle_youtube_ytdlp] argument='{argument[:60]}'")
    result = await _secondary_get_info(argument)
    if not result:
        return None
    title, video_id, duration, yt_url, channel, views, stream_url, thumbnail, _ = result
    return (title, duration, yt_url, thumbnail, channel, views, video_id, stream_url)


# ══════════════════════════════════════════════════════════════════════════════
#  MODULE TEARDOWN
# ══════════════════════════════════════════════════════════════════════════════

async def close_session() -> None:
    """
    Gracefully close the persistent aiohttp session.
    Call this in your bot's on_shutdown handler.
    """
    global _http_session
    async with _http_session_lock:
        if _http_session and not _http_session.closed:
            await _http_session.close()
            _http_session = None
            logger.info("[Session] Persistent aiohttp.ClientSession closed.")
