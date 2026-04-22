"""
╔══════════════════════════════════════════════════════════════════════════════╗
║              youtube.py  ─  Hybrid YouTube Module for AnonXMusic            ║
╠══════════════════════════════════════════════════════════════════════════════╣
║                                                                              ║
║  SOURCE PRIORITY  (strict waterfall — each tier only tried if above fails)  ║
║  ─────────────────────────────────────────────────────────────────────────  ║
║  [1]   PRIMARY    — Stream API           (fast, zero storage)               ║
║  [1.5] PY_YT      — py_yt metadata       (not blocked on VPS)               ║
║  [2]   SECONDARY  — Local yt-dlp + IPv6 /64 rotation                       ║
║  [3]   TERTIARY   — Download API via Cloudflare Worker pool                 ║
║                     (storage-based last resort, hidden IP)                  ║
║                                                                              ║
║  SECURITY                                                                    ║
║  ─────────────────────────────────────────────────────────────────────────  ║
║  • Strict Regex validation on every YouTube ID before any network call      ║
║  • os.path.basename() enforced on every file-path operation                 ║
║  • MD5-hashed filenames — prevents path traversal & name collisions         ║
║                                                                              ║
║  PERFORMANCE                                                                 ║
║  ─────────────────────────────────────────────────────────────────────────  ║
║  • One persistent aiohttp.ClientSession per process (lazy init)             ║
║  • In-memory + disk URL cache with YouTube expire-param awareness           ║
║  • Cloudflare Worker Pool: rotating proxy URLs hide the server real IP      ║
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
# All secrets / URLs come from config.py — single source of truth.
from config import (
    YT_API_TOKEN        as _STREAM_API_TOKEN,   # Bearer token for Stream API
    NUB_YT_API_BASE_URL as _STREAM_API_BASE,    # Stream API base URL
    YOUTUBE_API_KEYS    as _YT_KEYS_RAW,        # Comma-separated YouTube Data API keys
    IPV6_BLOCK          as _IPV6_BLOCK,         # e.g. "2001:db8:abcd::/64"
    CLOUDFLARE_WORKERS  as _CF_WORKERS_RAW,     # Comma-separated Cloudflare worker URLs
    SHRUTI_API_URL      as _DOWNLOAD_API_BASE,  # Download API base URL
    DOWNLOAD_DIR        as _DOWNLOAD_DIR,       # Local download folder path
)

# ══════════════════════════════════════════════════════════════════════════════
#  MODULE-LEVEL CONSTANTS & SETUP
# ══════════════════════════════════════════════════════════════════════════════

logger = logging.getLogger(__name__)

# ─── Directories ──────────────────────────────────────────────────────────────
# _CACHE_DIR   : disk cache for serialised stream-URL JSON objects
# DOWNLOAD_DIR : files downloaded via Tertiary path; auto-cleaned after 5 min
_CACHE_DIR   = os.path.join(os.path.dirname(__file__), "cache")
DOWNLOAD_DIR = _DOWNLOAD_DIR or "downloads"

os.makedirs(_CACHE_DIR,   exist_ok=True)
os.makedirs(DOWNLOAD_DIR, exist_ok=True)

# ─── In-Memory URL Cache ──────────────────────────────────────────────────────
# Dict key: ("audio"|"video", youtube_url)  →  stream_url string
_MEM_CACHE: Dict[Tuple[str, str], str] = {}

# ─── YouTube Data API v3 endpoints ────────────────────────────────────────────
_YT_SEARCH_URL  = "https://www.googleapis.com/youtube/v3/search"
_YT_DETAILS_URL = "https://www.googleapis.com/youtube/v3/videos"

# ─── YouTube video-ID validation regex ────────────────────────────────────────
# Exactly 11 alphanumeric / dash / underscore characters — nothing else accepted.
_VIDEO_ID_RE = re.compile(r"^[A-Za-z0-9_-]{11}$")

# Patterns for *extracting* an ID from a raw URL string
_EXTRACT_PATTERNS = [
    re.compile(r"(?:v=|/v/|youtu\.be/|/embed/|/shorts/)([A-Za-z0-9_-]{11})"),
    re.compile(r"(?:watch\?|/v/|youtu\.be/)([A-Za-z0-9_-]{11})"),
]

# ─── Cloudflare Worker Pool ────────────────────────────────────────────────────
# Each worker proxies requests to the Download API, keeping the server IP hidden.
# Config format: "https://worker1.user.workers.dev,https://worker2.user.workers.dev"
_CF_WORKERS: List[str] = [
    w.strip() for w in (_CF_WORKERS_RAW or "").split(",") if w.strip()
]
if not _CF_WORKERS:
    # No workers configured — fall back to calling the Download API directly
    logger.warning("[CFPool] No Cloudflare workers configured — using Download API URL directly.")
    _CF_WORKERS = [_DOWNLOAD_API_BASE.rstrip("/")]

# ─── IPv6 /64 Subnet ──────────────────────────────────────────────────────────
_IPV6_NET: Optional[ipaddress.IPv6Network] = None
try:
    if _IPV6_BLOCK:
        _IPV6_NET = ipaddress.ip_network(_IPV6_BLOCK, strict=False)
        logger.info(f"[IPv6] Subnet loaded: {_IPV6_NET}")
except Exception as _exc:
    logger.warning(f"[IPv6] Could not parse IPV6_BLOCK='{_IPV6_BLOCK}': {_exc}")

# ─── Cleanup Delay ────────────────────────────────────────────────────────────
_CLEANUP_DELAY_SECS = 5 * 60   # delete downloaded files 5 minutes after playback

# ─── Persistent aiohttp Session (lazy-init) ───────────────────────────────────
_http_session: Optional[aiohttp.ClientSession] = None
_http_session_lock = asyncio.Lock()


async def _get_session() -> aiohttp.ClientSession:
    """
    Return the module-level persistent aiohttp.ClientSession.
    Created on the first call; thread-safe via asyncio.Lock.
    One session per process = one TCP connection pool = much faster.
    """
    global _http_session
    async with _http_session_lock:
        if _http_session is None or _http_session.closed:
            connector = aiohttp.TCPConnector(limit=50, ttl_dns_cache=300)
            _http_session = aiohttp.ClientSession(
                connector=connector,
                headers={"User-Agent": "AnonXMusic/4.0 (Telegram Bot)"},
            )
            logger.info("[Session] Persistent aiohttp.ClientSession created.")
    return _http_session


# ══════════════════════════════════════════════════════════════════════════════
#  SECURITY UTILITIES
# ══════════════════════════════════════════════════════════════════════════════

def validate_video_id(video_id: str) -> bool:
    """
    Strict regex check: accepts ONLY the canonical 11-character YouTube video ID.
    Rejects anything that could be path-traversal bait (slashes, dots, etc.).
    Runs before EVERY network call that uses a video ID.
    """
    return bool(_VIDEO_ID_RE.match(video_id or ""))


def extract_video_id(url_or_id: str) -> Optional[str]:
    """
    Extract and validate a YouTube video ID from a URL or bare string.
    Returns the 11-char video ID, or None if not found / fails validation.
    Never raises — all errors are logged.
    """
    if not url_or_id:
        return None
    try:
        # Check if the raw string is already a bare video ID
        if validate_video_id(url_or_id.strip()):
            return url_or_id.strip()

        for pattern in _EXTRACT_PATTERNS:
            match = pattern.search(url_or_id)
            if match:
                vid = match.group(1)
                if validate_video_id(vid):
                    logger.debug(f"[Security] Extracted video_id='{vid}'")
                    return vid

        logger.debug(f"[Security] No valid video_id in '{url_or_id[:60]}'")
        return None
    except Exception as exc:
        logger.error(f"[Security] extract_video_id error: {exc}")
        return None


def _safe_filename(video_id: str, ext: str) -> str:
    """
    Build an MD5-hashed filename from the video ID + extension.

    Why MD5?
      1. User-supplied IDs could be used to create files with tricky names —
         hashing eliminates that entirely.
      2. Guaranteed fixed-length names, no OS-level filename issues.
      3. os.path.basename() applied as final safety net.
    """
    raw = hashlib.md5(f"{video_id}.{ext}".encode()).hexdigest()
    return os.path.basename(f"{raw}.{ext}")


def _safe_filepath(video_id: str, ext: str) -> str:
    """Combine DOWNLOAD_DIR with a hashed, safe filename."""
    return os.path.join(DOWNLOAD_DIR, _safe_filename(video_id, ext))


# ══════════════════════════════════════════════════════════════════════════════
#  FORMATTING HELPERS
# ══════════════════════════════════════════════════════════════════════════════

def format_duration(seconds: Union[int, float]) -> str:
    """Convert integer seconds → 'HH:MM:SS' or 'MM:SS'."""
    if not isinstance(seconds, (int, float)) or seconds < 0:
        return "N/A"
    h = int(seconds) // 3600
    m = (int(seconds) % 3600) // 60
    s = int(seconds) % 60
    return f"{h:02d}:{m:02d}:{s:02d}" if h else f"{m:02d}:{s:02d}"


def time_to_seconds(t: str) -> int:
    """Convert 'HH:MM:SS' or 'MM:SS' → integer seconds."""
    try:
        return sum(int(x) * (60 ** i) for i, x in enumerate(reversed(str(t).split(":"))))
    except Exception:
        return 0


def format_views(n) -> str:
    """Format a raw view count to Indian abbreviation style (Cr / L / K)."""
    try:
        n = float(str(n).replace(",", "").split()[0])
    except (ValueError, TypeError, IndexError):
        return "0"
    if n >= 1e7:
        return f"{n / 1e7:.1f} Cr"
    if n >= 1e5:
        return f"{n / 1e5:.1f} L"
    if n >= 1e3:
        return f"{n / 1e3:.1f}K"
    return str(int(n))


def _parse_iso_duration(duration: str) -> str:
    """Parse ISO-8601 duration string (e.g. 'PT1H2M3S') into 'HH:MM:SS'."""
    match = re.match(r"PT(?:(\d+)H)?(?:(\d+)M)?(?:(\d+)S)?", duration or "")
    if not match:
        return "N/A"
    h, m, s = (int(x) if x else 0 for x in match.groups())
    return f"{h}:{m:02d}:{s:02d}" if h else f"{m}:{s:02d}"


def _extract_expire(stream_url: str) -> Optional[int]:
    """
    Parse the `expire` query param from a YouTube CDN stream URL.
    Returns the UNIX timestamp if still in the future, else None.
    """
    try:
        q      = parse_qs(urlparse(stream_url).query)
        expire = int(q.get("expire", [0])[0])
        return expire if expire > int(time.time()) else None
    except Exception:
        return None


# ══════════════════════════════════════════════════════════════════════════════
#  STREAM URL CACHE  (memory + disk, expire-aware)
# ══════════════════════════════════════════════════════════════════════════════

def _cache_key(url: str, prefix: str = "") -> str:
    return hashlib.md5((prefix + url).encode()).hexdigest()


def _cache_path(url: str, prefix: str = "") -> str:
    return os.path.join(_CACHE_DIR, _cache_key(url, prefix) + ".json")


def _read_cache(url: str, prefix: str = "") -> Optional[str]:
    """Read a non-expired stream URL from disk cache. Returns None if missing/expired."""
    path = _cache_path(url, prefix)
    if not os.path.exists(path):
        return None
    try:
        with open(path, "r") as f:
            data = json.load(f)
        expire = data.get("expire", 0)
        if time.time() < expire - 15:
            logger.info(f"[Cache] DISK HIT {prefix}{url[:55]}… (expires in {int(expire - time.time())}s)")
            return data.get("url")
        logger.info(f"[Cache] EXPIRED — removing {url[:55]}…")
        os.remove(path)
    except Exception as exc:
        logger.warning(f"[Cache] Read error ({exc}), removing corrupt entry.")
        try:
            os.remove(path)
        except OSError:
            pass
    return None


def _write_cache(url: str, stream_url: str, prefix: str = "") -> None:
    """Persist a stream URL to disk, tagged with its YouTube expire timestamp."""
    expire = _extract_expire(stream_url)
    if not expire:
        logger.debug("[Cache] SKIP write — no expire param in stream URL.")
        return
    try:
        with open(_cache_path(url, prefix), "w") as f:
            json.dump({"url": stream_url, "expire": expire}, f)
        logger.info(f"[Cache] WRITE {prefix}{url[:55]}… (expires in {int(expire - time.time())}s)")
    except Exception as exc:
        logger.error(f"[Cache] Write failed: {exc}")


def _get_cached_stream(url: str, kind: str) -> Optional[str]:
    """
    Unified cache lookup: memory first (fastest), then disk.
    `kind` must be 'audio' or 'video'.
    """
    key    = (kind, url)
    cached = _MEM_CACHE.get(key)
    if cached:
        expire = _extract_expire(cached)
        if expire and time.time() < expire - 15:
            logger.info(f"[Cache] MEM HIT ({kind}) {url[:55]}…")
            return cached
        del _MEM_CACHE[key]  # stale — evict

    cached = _read_cache(url, prefix=f"{kind}_")
    if cached:
        _MEM_CACHE[key] = cached  # promote to memory
        return cached

    return None


def _set_cached_stream(url: str, kind: str, stream_url: str) -> None:
    """Write stream URL to both memory and disk caches."""
    _MEM_CACHE[(kind, url)] = stream_url
    _write_cache(url, stream_url, prefix=f"{kind}_")


# ══════════════════════════════════════════════════════════════════════════════
#  IPv6 /64 SUBNET ROTATION
# ══════════════════════════════════════════════════════════════════════════════

def _random_ipv6_address() -> Optional[str]:
    """
    Pick a random host address inside the configured /64 subnet.

    How it helps: yt-dlp uses this address as the source IP for outbound
    requests. Rotating within the /64 block makes each extraction look like
    a different client to YouTube's rate-limiter, greatly reducing 429s.
    Returns None if no subnet configured (feature silently skipped).
    """
    if _IPV6_NET is None:
        return None
    try:
        max_host = _IPV6_NET.num_addresses - 2
        offset   = random.randint(1, max_host)
        address  = _IPV6_NET.network_address + offset
        return str(address)
    except Exception as exc:
        logger.warning(f"[IPv6] Could not generate random address: {exc}")
        return None


# ══════════════════════════════════════════════════════════════════════════════
#  CLOUDFLARE WORKER POOL
# ══════════════════════════════════════════════════════════════════════════════

def _get_worker_base() -> str:
    """
    Return a randomly chosen Cloudflare Worker URL from the pool.

    Every Tertiary-path request is routed through a different worker, so the
    Download API server never sees the bot's real VPS IP address. This makes
    IP-based blocking essentially impossible.
    """
    chosen = random.choice(_CF_WORKERS)
    logger.debug(f"[CFPool] Selected worker: {chosen}")
    return chosen.rstrip("/")


# ══════════════════════════════════════════════════════════════════════════════
#  BACKGROUND FILE CLEANUP
# ══════════════════════════════════════════════════════════════════════════════

_cleanup_registry: Dict[str, float] = {}


async def schedule_file_cleanup(file_path: str, delay: int = _CLEANUP_DELAY_SECS) -> None:
    """
    Schedule a downloaded file for deletion after `delay` seconds.

    Keeps disk usage near-zero on VPS/cloud: the file only exists during the
    playback window, then disappears automatically.

    Usage (fire-and-forget):
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
    Delete all overdue files in DOWNLOAD_DIR immediately.
    Call on bot startup to handle leftovers from a previous crashed session.
    Returns the number of files deleted.
    """
    deleted = 0
    now     = time.time()
    for fname in os.listdir(DOWNLOAD_DIR):
        fpath     = os.path.join(DOWNLOAD_DIR, fname)
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
#  YOUTUBE DATA API v3  (search + metadata)
# ══════════════════════════════════════════════════════════════════════════════

def _get_api_keys() -> List[str]:
    return [k.strip() for k in (_YT_KEYS_RAW or "").split(",") if k.strip()]


def _random_api_key() -> Optional[str]:
    keys = _get_api_keys()
    return random.choice(keys) if keys else None


async def youtube_search(query: str, limit: int = 5) -> List[Dict]:
    """
    Search YouTube via the Data API v3.
    Uses a random key from the pool on every call to distribute quota.
    Returns an empty list on any error.
    """
    key = _random_api_key()
    if not key:
        logger.warning("[YTSearch] No YouTube Data API key configured.")
        return []

    session = await _get_session()
    try:
        # Step 1 — search
        async with session.get(
            _YT_SEARCH_URL,
            params={"part": "snippet", "q": query, "maxResults": limit,
                    "type": "video", "key": key},
            timeout=aiohttp.ClientTimeout(total=10),
        ) as resp:
            if resp.status != 200:
                logger.error(f"[YTSearch] HTTP {resp.status}")
                return []
            items = (await resp.json()).get("items", [])

        video_ids = [
            item["id"]["videoId"]
            for item in items
            if "videoId" in item.get("id", {}) and validate_video_id(item["id"]["videoId"])
        ]
        if not video_ids:
            return []

        # Step 2 — fetch details (duration, views)
        async with session.get(
            _YT_DETAILS_URL,
            params={"part": "contentDetails,statistics",
                    "id": ",".join(video_ids),
                    "key": _random_api_key() or key},
            timeout=aiohttp.ClientTimeout(total=10),
        ) as resp:
            if resp.status != 200:
                return []
            detail_map = {v["id"]: v for v in (await resp.json()).get("items", [])}

        # Step 3 — assemble results
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
                "duration":     _parse_iso_duration(
                    det.get("contentDetails", {}).get("duration", "")),
                "thumbnail":    snip.get("thumbnails", {}).get("high", {}).get("url", ""),
            })

        logger.info(f"[YTSearch] '{query[:50]}' → {len(results)} results")
        return results

    except aiohttp.ClientError as exc:
        logger.error(f"[YTSearch] Network error: {exc}")
        return []
    except Exception as exc:
        logger.error(f"[YTSearch] Unexpected error: {exc}")
        return []


# ══════════════════════════════════════════════════════════════════════════════
#  ████████╗██╗███████╗██████╗      ██╗
#  ╚══██╔══╝██║██╔════╝██╔══██╗    ███║
#     ██║   ██║█████╗  ██████╔╝    ╚██║
#     ██║   ██║██╔══╝  ██╔══██╗     ██║
#     ██║   ██║███████╗██║  ██║     ██║
#     ╚═╝   ╚═╝╚══════╝╚═╝  ╚═╝     ╚═╝
#
#  [1] PRIMARY SOURCE — Stream API  (fast, zero storage)
# ══════════════════════════════════════════════════════════════════════════════

async def _primary_get_stream_url(youtube_url: str, mode: str = "audio") -> Optional[str]:
    """
    Call the Stream API to obtain a direct CDN stream URL.

    Fastest path — no files touch the disk. The API returns a pre-signed URL
    with an `expire` param which we cache locally.

    Args:
        youtube_url : full YouTube watch URL
        mode        : "audio" or "video"

    Returns:
        A direct stream URL string, or None on any failure / rate-limit.
    """
    if not _STREAM_API_TOKEN:
        logger.warning("[Primary] STREAM_API_TOKEN not set — skipping.")
        return None

    session = await _get_session()
    logger.info(f"[Primary] Requesting {mode} stream for {youtube_url[:55]}…")

    try:
        async with session.get(
            f"{_STREAM_API_BASE.rstrip('/')}/stream",
            params={"q": youtube_url, "mode": mode, "token": _STREAM_API_TOKEN},
            timeout=aiohttp.ClientTimeout(total=15),
        ) as resp:
            if resp.status == 429:
                logger.warning("[Primary] Rate limit hit (HTTP 429) — triggering fallback.")
                return None
            if resp.status != 200:
                logger.warning(f"[Primary] HTTP {resp.status} — triggering fallback.")
                return None

            data       = await resp.json()
            stream_url = (
                data.get("video_url") or data.get("stream_url")
                if mode == "video"
                else data.get("audio_url") or data.get("stream_url")
            )

            if not stream_url:
                logger.warning("[Primary] API returned no stream_url field.")
                return None

            logger.info("[Primary] ✅ Stream URL obtained.")
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
    Fetch full track metadata from the Stream API.
    Returns a 9-tuple on success, None on failure.

    Tuple layout (shared across all tiers):
        (title, video_id, duration, youtube_url, channel, views, stream_url, thumbnail, source)
    """
    if not _STREAM_API_TOKEN:
        return None

    session = await _get_session()
    try:
        async with session.get(
            f"{_STREAM_API_BASE.rstrip('/')}/info",
            params={"q": query, "token": _STREAM_API_TOKEN},
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

            dur_raw = data.get("duration", 0)
            dur_fmt = format_duration(dur_raw) if isinstance(dur_raw, int) else str(dur_raw)
            vid_id  = data.get("video_id", "")

            return (
                data.get("title",        "N/A"),
                vid_id,
                dur_fmt,
                data.get("youtube_link", f"https://www.youtube.com/watch?v={vid_id}"),
                data.get("channel_name", "N/A"),
                format_views(data.get("views", 0)),
                data.get("stream_url",   "N/A"),
                data.get("thumbnail",    "N/A"),
                "primary",
            )

    except Exception as exc:
        logger.error(f"[Primary-Info] Error: {exc}")
        return None


# ══════════════════════════════════════════════════════════════════════════════
#  ████████╗██╗███████╗██████╗      ██╗    ███████╗
#  ╚══██╔══╝██║██╔════╝██╔══██╗    ███║    ██╔════╝
#     ██║   ██║█████╗  ██████╔╝    ╚██║    ███████╗
#     ██║   ██║██╔══╝  ██╔══██╗     ██║    ╚════██║
#     ██║   ██║███████╗██║  ██║     ██║    ███████║
#     ╚═╝   ╚═╝╚══════╝╚═╝  ╚═╝     ╚═╝    ╚══════╝
#
#  [1.5] PY_YT METADATA — Not blocked by YouTube on VPS
#        Provides title / duration / thumbnail when Primary is down.
#        Stream URL is always "N/A" here — paired with Tertiary for the file.
# ══════════════════════════════════════════════════════════════════════════════

async def _pyyt_get_info(query: str) -> Optional[Tuple]:
    """
    Fetch track metadata via the py_yt library (VideosSearch).

    Why this exists:
      yt-dlp's metadata extraction hits YouTube directly and gets blocked on
      most VPS/cloud IPs. py_yt uses a different scraping approach that
      YouTube does NOT block, making it the reliable metadata fallback on servers.

    NOTE: This function returns metadata ONLY — stream_url field is always "N/A".
    The caller pairs this result with _tertiary_download() to get the actual file.

    Returns a 9-tuple on success, None on any error.
    """
    try:
        logger.info(f"[PyYT] Fetching metadata for '{query[:55]}'…")

        results = VideosSearch(query, limit=1)
        data    = (await results.next())["result"]

        if not data:
            logger.warning("[PyYT] No results returned.")
            return None

        r = data[0]

        title   = r.get("title", "N/A")
        vid_id  = r.get("id", "N/A")
        dur_fmt = r.get("duration") or "N/A"
        yt_url  = r.get("link", f"https://www.youtube.com/watch?v={vid_id}")
        channel = r.get("channel", {}).get("name", "N/A")

        # py_yt returns viewCount as {"text": "1,234,567 views"}
        view_raw = "0"
        if r.get("viewCount") and r["viewCount"].get("text"):
            view_raw = r["viewCount"]["text"].replace(",", "").split()[0]
        views = format_views(view_raw)

        thumb = r.get("thumbnails", [{}])[0].get("url", "N/A")

        # Security: validate extracted ID before returning
        if not validate_video_id(vid_id):
            logger.warning(f"[PyYT] vid_id='{vid_id}' failed validation — discarding.")
            return None

        logger.info(f"[PyYT] ✅ Metadata: '{title}' | id='{vid_id}' | dur='{dur_fmt}'")
        # stream_url slot is "N/A" — Tertiary fills it in the caller
        return (title, vid_id, dur_fmt, yt_url, channel, views, "N/A", thumb, "pyyt")

    except Exception as exc:
        logger.error(f"[PyYT] Error: {exc}")
        return None


# ══════════════════════════════════════════════════════════════════════════════
#  ████████╗██╗███████╗██████╗      ██████╗
#  ╚══██╔══╝██║██╔════╝██╔══██╗     ╚════██╗
#     ██║   ██║█████╗  ██████╔╝      █████╔╝
#     ██║   ██║██╔══╝  ██╔══██╗     ██╔═══╝
#     ██║   ██║███████╗██║  ██║     ███████╗
#     ╚═╝   ╚═╝╚══════╝╚═╝  ╚═╝     ╚══════╝
#
#  [2] SECONDARY SOURCE — Local yt-dlp + IPv6 /64 Rotation
#      Only reached if Primary AND py_yt (Tier 1.5) both fail.
# ══════════════════════════════════════════════════════════════════════════════

async def _run_ytdlp_subprocess(
    url: str,
    format_selector: str,
    cookies_path: Optional[str] = None,
) -> Optional[str]:
    """
    Run yt-dlp as an async subprocess using -g flag (print URL, no download).

    IPv6 rotation: binds to a random address in the /64 block via
    --source-address so each call looks like a different client to YouTube.
    Timeout: 40 seconds.
    """
    cmd = ["yt-dlp", "--no-playlist", "-f", format_selector, "-g", "--js-runtimes", "node"]

    ipv6_addr = _random_ipv6_address()
    if ipv6_addr:
        cmd.extend(["--source-address", ipv6_addr])
        logger.debug(f"[Secondary] IPv6 binding: {ipv6_addr}")

    if cookies_path and os.path.exists(cookies_path):
        safe_cookies = os.path.basename(cookies_path)
        cmd.extend(["--cookies", os.path.join(os.path.dirname(cookies_path), safe_cookies)])
    else:
        cmd.extend(["--cookies-from-browser", "firefox"])

    cmd.append(url)
    logger.info(f"[Secondary] yt-dlp cmd (IPv6={ipv6_addr or 'none'}): {' '.join(cmd[:5])}…")

    start = time.time()
    try:
        proc = await asyncio.create_subprocess_exec(
            *cmd,
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.PIPE,
        )
        stdout, stderr = await asyncio.wait_for(proc.communicate(), timeout=40)
    except asyncio.TimeoutError:
        logger.error("[Secondary] yt-dlp timed out after 40s.")
        return None
    except Exception as exc:
        logger.error(f"[Secondary] subprocess error: {exc}")
        return None

    elapsed = round(time.time() - start, 2)
    if proc.returncode == 0 and stdout:
        stream_url = stdout.decode().strip().split("\n")[0]
        logger.info(f"[Secondary] ✅ yt-dlp succeeded ({elapsed}s)")
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
    Extract a direct stream URL via local yt-dlp with IPv6 rotation.
    Tries multiple format selectors from best to most permissive.
    """
    logger.info(f"[Secondary] yt-dlp stream extraction ({mode})…")

    selectors = (
        ["bestaudio[ext=m4a]/bestaudio/best", "bestaudio", "best"]
        if mode == "audio"
        else ["best[ext=mp4][protocol=https]", "bestvideo+bestaudio/best", "best"]
    )

    for selector in selectors:
        url = await _run_ytdlp_subprocess(youtube_url, selector, cookies_path)
        if url:
            return url
        logger.debug(f"[Secondary] Selector '{selector}' failed — trying next…")

    logger.error("[Secondary] All yt-dlp format selectors exhausted.")
    return None


async def _secondary_get_info(query: str) -> Optional[Tuple]:
    """
    Use yt_dlp Python library (skip_download=True) to get metadata + stream URL.
    The blocking extraction runs in a thread executor to avoid blocking asyncio.
    """
    logger.info(f"[Secondary] yt-dlp Python API for '{query[:55]}'…")
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

        # Run blocking yt-dlp call in thread pool — never blocks the event loop
        info_dict = await loop.run_in_executor(None, _extract)
        if not info_dict:
            return None

        vid_id     = info_dict.get("id", "N/A")
        title      = info_dict.get("title", "N/A")
        channel    = info_dict.get("uploader", "N/A")
        views      = format_views(info_dict.get("view_count", 0))
        yt_url     = f"https://www.youtube.com/watch?v={vid_id}"
        dur_sec    = int(info_dict.get("duration", 0) or 0)
        dur_fmt    = format_duration(dur_sec)
        thumb      = (info_dict.get("thumbnails") or [{}])[-1].get("url", "N/A")
        stream_url = _pick_best_format(info_dict.get("formats", []))

        return (title, vid_id, dur_fmt, yt_url, channel, views, stream_url, thumb, "secondary")

    except (yt_dlp.utils.ExtractorError, yt_dlp.utils.DownloadError) as exc:
        logger.error(f"[Secondary] yt-dlp extraction error: {exc}")
        return None
    except Exception as exc:
        logger.error(f"[Secondary] Unexpected error: {exc}")
        return None


def _pick_best_format(formats: List[Dict]) -> str:
    """Select best progressive HTTP URL from yt-dlp format list, preferring MP4."""
    if not formats:
        return "N/A"

    def is_progressive_http(f: Dict) -> bool:
        return (
            f.get("acodec") != "none"
            and f.get("vcodec") != "none"
            and str(f.get("protocol", "")).startswith("http")
            and bool(f.get("url"))
        )

    for f in formats:
        if is_progressive_http(f) and f.get("ext") == "mp4":
            return f["url"]
    for f in formats:
        if is_progressive_http(f):
            return f["url"]
    for f in formats:
        if f.get("url"):
            return f["url"]
    return "N/A"


# ══════════════════════════════════════════════════════════════════════════════
#  ████████╗██╗███████╗██████╗      ██████╗
#  ╚══██╔══╝██║██╔════╝██╔══██╗     ╚════██╗
#     ██║   ██║█████╗  ██████╔╝         ██╔╝
#     ██║   ██║██╔══╝  ██╔══██╗        ██╔╝
#     ██║   ██║███████╗██║  ██║        ██║
#     ╚═╝   ╚═╝╚══════╝╚═╝  ╚═╝        ╚═╝
#
#  [3] TERTIARY SOURCE — Download API via Cloudflare Worker Pool
#      Storage-based last resort. File auto-deleted 5 minutes after use.
# ══════════════════════════════════════════════════════════════════════════════

async def _tertiary_download(video_id: str, media_type: str = "audio") -> Optional[str]:
    """
    Download a file via the Download API, routing through a random Cloudflare
    Worker to keep the VPS's real IP completely hidden.

    Flow:
      1. GET {worker}/download?url={video_id}&type={media_type}
         → receives JSON with a `download_token`
      2. GET {worker}/stream/{video_id}?type=…&token=…
         → streams file to disk (aiohttp follows 302 redirects automatically)
      3. Returns the local MD5-hashed file path.
      4. Background asyncio task scheduled to delete the file in 5 minutes.

    Security: video_id regex-validated before any network call.
    Safety:   file path is MD5-hashed; os.path.basename() applied throughout.
    """
    if not validate_video_id(video_id):
        logger.error(f"[Tertiary] Invalid video_id '{video_id}' — aborting.")
        return None

    ext       = "mp4" if media_type == "video" else "mp3"
    file_path = _safe_filepath(video_id, ext)

    # Reuse existing file to avoid redundant network calls
    if os.path.exists(file_path) and os.path.getsize(file_path) > 0:
        logger.info(f"[Tertiary] File already exists: {os.path.basename(file_path)}")
        return file_path

    worker_base = _get_worker_base()
    session     = await _get_session()
    dl_timeout  = 600 if media_type == "video" else 300

    logger.info(f"[Tertiary] Downloading {media_type} for '{video_id}' via CF worker…")

    try:
        # Step 1 — request download token
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
            logger.error("[Tertiary] No download_token in API response.")
            return None

        # Step 2 — stream file to disk (aiohttp follows 302 automatically)
        stream_url = f"{worker_base}/stream/{video_id}?type={media_type}&token={download_token}"
        async with session.get(
            stream_url,
            timeout=aiohttp.ClientTimeout(total=dl_timeout),
            allow_redirects=True,
        ) as file_resp:
            if file_resp.status != 200:
                logger.error(f"[Tertiary] File stream HTTP {file_resp.status}")
                return None
            with open(file_path, "wb") as fh:
                async for chunk in file_resp.content.iter_chunked(16384):
                    fh.write(chunk)

        # Step 3 — verify integrity
        if not os.path.exists(file_path) or os.path.getsize(file_path) == 0:
            logger.error("[Tertiary] Downloaded file is empty or missing.")
            _safe_remove(file_path)
            return None

        size_kb = os.path.getsize(file_path) // 1024
        logger.info(f"[Tertiary] ✅ Downloaded {size_kb} KB → {os.path.basename(file_path)}")

        # Step 4 — schedule auto-cleanup after 5 minutes
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
    """Delete a file safely — basename-validated, never raises."""
    safe_path = os.path.join(DOWNLOAD_DIR, os.path.basename(path))
    try:
        if os.path.exists(safe_path):
            os.remove(safe_path)
    except OSError:
        pass


# ══════════════════════════════════════════════════════════════════════════════
#  RECONNECT LOGIC — Refresh an Expired Stream URL
# ══════════════════════════════════════════════════════════════════════════════

async def reconnect_stream(
    youtube_url: str,
    mode: str = "audio",
    cookies_path: Optional[str] = None,
) -> Optional[str]:
    """
    Re-fetch a fresh stream URL for a track that has stalled or whose CDN URL
    has expired. Call this from your PyTgCalls error/stall handler.

    Invalidates stale cached entries first, then re-runs the full waterfall.
    Returns a fresh stream URL/path, or None if all sources fail.
    """
    video_id = extract_video_id(youtube_url)
    if not video_id:
        logger.error(f"[Reconnect] Cannot parse video_id from '{youtube_url[:55]}'")
        return None

    logger.info(f"[Reconnect] Refreshing {mode} stream for video_id='{video_id}'")

    # Invalidate stale cache entries
    for kind in ("audio", "video"):
        _MEM_CACHE.pop((kind, youtube_url), None)

    full_url = f"https://www.youtube.com/watch?v={video_id}"

    # Try Primary first
    stream = await _primary_get_stream_url(full_url, mode=mode)
    if stream:
        _set_cached_stream(full_url, mode, stream)
        return stream

    # py_yt metadata + Tertiary
    logger.info("[Reconnect] Primary failed — trying py_yt + Tertiary…")
    meta = await _pyyt_get_info(full_url)
    if meta:
        file_path = await _tertiary_download(video_id, media_type=mode)
        if file_path:
            return file_path

    # Last resort — Secondary (yt-dlp)
    logger.info("[Reconnect] Falling back to Secondary (yt-dlp)…")
    stream = await _secondary_get_stream_url(full_url, mode=mode, cookies_path=cookies_path)
    if stream:
        _set_cached_stream(full_url, mode, stream)
        return stream

    logger.error(f"[Reconnect] ❌ All sources failed for video_id='{video_id}'")
    return None


# ══════════════════════════════════════════════════════════════════════════════
#  PUBLIC ENTRY POINTS — get_stream() / get_video_stream()
# ══════════════════════════════════════════════════════════════════════════════

async def get_stream(url: str, cookies_path: Optional[str] = None) -> Optional[str]:
    """
    Get an **audio** stream URL or local file path for the given YouTube URL.

    Full waterfall:
      Cache → [1] Primary → [1.5] py_yt + Tertiary → [2] yt-dlp → [3] Tertiary

    Returns a stream URL string, a local file path, or None on total failure.
    """
    video_id = extract_video_id(url)
    if not video_id:
        logger.error(f"[get_stream] Could not extract valid video_id from '{url[:55]}'")
        return None

    full_url = f"https://www.youtube.com/watch?v={video_id}"
    logger.info(f"[get_stream] Audio request for video_id='{video_id}'")

    # Cache check
    cached = _get_cached_stream(full_url, "audio")
    if cached:
        return cached

    # [1] Primary API
    stream = await _primary_get_stream_url(full_url, mode="audio")
    if stream:
        _set_cached_stream(full_url, "audio", stream)
        return stream

    # [1.5] py_yt metadata + Tertiary download
    logger.info("[get_stream] Primary failed — trying py_yt + Tertiary…")
    meta = await _pyyt_get_info(full_url)
    if meta:
        file_path = await _tertiary_download(video_id, media_type="audio")
        if file_path:
            logger.info("[get_stream] ✅ py_yt + Tertiary succeeded.")
            return file_path

    # [2] Secondary (yt-dlp subprocess)
    logger.info("[get_stream] py_yt path failed — trying Secondary (yt-dlp)…")
    stream = await _secondary_get_stream_url(full_url, mode="audio", cookies_path=cookies_path)
    if stream:
        _set_cached_stream(full_url, "audio", stream)
        return stream

    # [3] Tertiary alone (no metadata needed, just the file)
    logger.info("[get_stream] Secondary failed — Tertiary direct download…")
    file_path = await _tertiary_download(video_id, media_type="audio")
    if file_path:
        return file_path

    logger.error(f"[get_stream] ❌ ALL sources failed for video_id='{video_id}'")
    return None


async def get_video_stream(url: str, cookies_path: Optional[str] = None) -> Optional[str]:
    """
    Get a **video** stream URL or local file path. Same waterfall as get_stream().
    """
    video_id = extract_video_id(url)
    if not video_id:
        logger.error(f"[get_video_stream] Could not extract valid video_id from '{url[:55]}'")
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

    logger.info("[get_video_stream] Primary failed — trying py_yt + Tertiary…")
    meta = await _pyyt_get_info(full_url)
    if meta:
        file_path = await _tertiary_download(video_id, media_type="video")
        if file_path:
            return file_path

    logger.info("[get_video_stream] Trying Secondary (yt-dlp)…")
    stream = await _secondary_get_stream_url(full_url, mode="video", cookies_path=cookies_path)
    if stream:
        _set_cached_stream(full_url, "video", stream)
        return stream

    logger.info("[get_video_stream] Secondary failed — Tertiary fallback…")
    file_path = await _tertiary_download(video_id, media_type="video")
    if file_path:
        return file_path

    logger.error(f"[get_video_stream] ❌ ALL sources failed for video_id='{video_id}'")
    return None


# ══════════════════════════════════════════════════════════════════════════════
#  get_video_info() — metadata + stream in one call
# ══════════════════════════════════════════════════════════════════════════════

async def get_video_info(
    query: str,
    mode: str = "audio",
    cookies_path: Optional[str] = None,
) -> Tuple:
    """
    Return a 9-tuple describing the requested track:
        (title, video_id, duration, youtube_url, channel, views, stream_url, thumbnail, source)

    `source` is one of "primary" / "pyyt" / "secondary" / "tertiary" — useful
    for diagnostics to know which tier served the request.

    Full waterfall with detailed logging:
      [1]   Primary API         — fastest, full metadata + stream URL
      [1.5] py_yt + Tertiary    — metadata via py_yt (VPS-safe), file via Download API
      [2]   yt-dlp Python API   — metadata + stream URL (may be blocked on some VPS)
      [3]   py_yt + Tertiary    — last-resort retry of Tier 1.5
    """
    logger.info(f"[get_video_info] Query='{query[:55]}', mode={mode}")

    # ── [1] Primary API ──────────────────────────────────────────────────
    result = await _primary_get_info(query)
    if result and result[0] and result[0] != "N/A":
        logger.info(f"[get_video_info] ✅ Tier 1 (Primary): '{result[0]}'")
        return result

    # ── [1.5] py_yt metadata + Tertiary for stream URL ───────────────────
    logger.info("[get_video_info] Tier 1 failed — trying Tier 1.5 (py_yt + Tertiary)…")
    result = await _pyyt_get_info(query)
    if result and result[0] and result[0] != "N/A":
        vid_id    = result[1]
        file_path = await _tertiary_download(vid_id, media_type=mode)
        # Splice file_path into the stream_url slot (index 6), update source tag
        result = result[:6] + (file_path or "N/A",) + result[7:8] + ("tertiary",)
        logger.info(f"[get_video_info] ✅ Tier 1.5 (py_yt + Tertiary): '{result[0]}'")
        return result

    # ── [2] Secondary yt-dlp ─────────────────────────────────────────────
    logger.info("[get_video_info] Tier 1.5 failed — trying Tier 2 (yt-dlp)…")
    result = await _secondary_get_info(query)
    if result and result[0] and result[0] != "N/A":
        # If yt-dlp gave us no stream URL, supplement with Tertiary
        if result[6] == "N/A":
            logger.info("[get_video_info] yt-dlp metadata OK but no stream — Tertiary for stream…")
            vid_id    = result[1]
            file_path = await _tertiary_download(vid_id, media_type=mode)
            result    = result[:6] + (file_path or "N/A",) + result[7:8] + ("tertiary",)
        logger.info(f"[get_video_info] ✅ Tier 2 (Secondary): '{result[0]}'")
        return result

    # ── [3] Last resort — retry py_yt + Tertiary ─────────────────────────
    logger.info("[get_video_info] Tier 2 failed — final attempt Tier 3 (py_yt + Tertiary)…")
    try:
        result = await _pyyt_get_info(query)
        if result:
            vid_id    = result[1]
            file_path = await _tertiary_download(vid_id, media_type=mode)
            result    = result[:6] + (file_path or "N/A",) + result[7:8] + ("tertiary",)
            logger.info(f"[get_video_info] ✅ Tier 3 (last resort): '{result[0]}'")
            return result
    except Exception as exc:
        logger.error(f"[get_video_info] Tier 3 error: {exc}")

    logger.error(f"[get_video_info] ❌ ALL tiers failed for query='{query[:55]}'")
    return (None,) * 9


# ══════════════════════════════════════════════════════════════════════════════
#  YouTubeAPI CLASS  (AnonXMusic-compatible call sites)
# ══════════════════════════════════════════════════════════════════════════════

class YouTubeAPI:
    """
    Drop-in YouTube API client for AnonXMusic.
    All methods internally use the hybrid waterfall.
    Public method signatures are kept fully compatible with the original class
    so play.py, callbacks.py, start.py etc. need zero changes.
    """

    def __init__(self):
        self.base     = "https://www.youtube.com/watch?v="
        self.listbase = "https://youtube.com/playlist?list="
        self._ansi_re = re.compile(r"\x1B(?:[@-Z\\-_]|\[[0-?]*[ -/]*[@-~])")

    def _normalise(self, link: str, videoid: Union[bool, str, None]) -> str:
        """Expand bare video ID to full URL if needed; strip extra params."""
        if videoid:
            link = self.base + link
        if "&" in link:
            link = link.split("&")[0]
        return link

    # ── Existence & URL extraction ────────────────────────────────────────

    async def exists(self, link: str, videoid: Union[bool, str] = None) -> bool:
        return bool(re.search(r"(?:youtube\.com|youtu\.be)", self._normalise(link, videoid)))

    async def url(self, message: Message) -> Optional[str]:
        """Extract first URL entity from a Pyrogram message (or its reply)."""
        for msg in ([message, message.reply_to_message]
                    if message.reply_to_message else [message]):
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

    async def details(self, link: str, videoid: Union[bool, str] = None):
        """Return (title, duration_min, duration_sec, thumbnail, video_id)."""
        link    = self._normalise(link, videoid)
        result  = await get_video_info(link)
        title, vid_id, dur_fmt, _, _, _, _, thumb, _ = result
        dur_sec = time_to_seconds(dur_fmt)
        return (title or "N/A", dur_fmt or "N/A", dur_sec, thumb or "N/A", vid_id or "N/A")

    async def title(self, link: str, videoid: Union[bool, str] = None) -> str:
        return (await get_video_info(self._normalise(link, videoid)))[0] or "N/A"

    async def duration(self, link: str, videoid: Union[bool, str] = None) -> str:
        return (await get_video_info(self._normalise(link, videoid)))[2] or "N/A"

    async def thumbnail(self, link: str, videoid: Union[bool, str] = None) -> str:
        return (await get_video_info(self._normalise(link, videoid)))[7] or "N/A"

    async def track(self, link: str, videoid: Union[bool, str] = None) -> Tuple[Dict, str]:
        """Return (track_details_dict, video_id)."""
        link   = self._normalise(link, videoid)
        result = await get_video_info(link)
        title, vid_id, dur_fmt, yt_url, channel, views, stream_url, thumb, source = result
        track_details = {
            "title":        title      or "N/A",
            "link":         yt_url     or link,
            "vidid":        vid_id     or "N/A",
            "duration_min": dur_fmt    or "N/A",
            "thumb":        thumb      or "N/A",
            "channel":      channel    or "N/A",
            "views":        views      or "N/A",
            "stream_url":   stream_url,
            "source":       source,
        }
        return track_details, vid_id

    # ── Search & Slider ───────────────────────────────────────────────────

    async def slider(
        self, link: str, query_type: int, videoid: Union[bool, str] = None
    ) -> Tuple[str, str, str, str]:
        """Return (title, duration, thumbnail, video_id) for result #query_type."""
        link    = self._normalise(link, videoid)
        results = await youtube_search(link, limit=10)
        if not results or query_type >= len(results):
            return "N/A", "N/A", "N/A", "N/A"
        r = results[query_type]
        return r["title"], r["duration"], r["thumbnail"], r["video_id"]

    # ── Format listing ────────────────────────────────────────────────────

    async def formats(self, link: str, videoid: Union[bool, str] = None) -> Tuple[List[Dict], str]:
        """Extract all non-DASH formats via yt-dlp Python API."""
        link   = self._normalise(link, videoid)
        vid_id = extract_video_id(link)
        if not vid_id:
            return [], link

        loop = asyncio.get_event_loop()
        ipv6 = _random_ipv6_address()

        def _get():
            opts = {"quiet": True, "no_warnings": True}
            if ipv6:
                opts["source_address"] = ipv6
            with yt_dlp.YoutubeDL(opts) as ydl:
                return ydl.extract_info(link, download=False).get("formats", [])

        try:
            raw = await loop.run_in_executor(None, _get)
        except Exception as exc:
            logger.error(f"[formats] yt-dlp error: {exc}")
            return [], link

        return (
            [
                {
                    "format":      f.get("format",     "N/A"),
                    "filesize":    f.get("filesize"),
                    "format_id":   f.get("format_id",  "N/A"),
                    "ext":         f.get("ext",         "N/A"),
                    "format_note": f.get("format_note", "N/A"),
                    "yturl":       link,
                }
                for f in raw
                if "dash" not in str(f.get("format", "")).lower()
            ],
            link,
        )

    # ── Playlist ──────────────────────────────────────────────────────────

    async def playlist(
        self, link: str, limit: int, user_id: int, videoid: Union[bool, str] = None
    ) -> List[str]:
        """Fetch up to `limit` validated video IDs from a YouTube playlist."""
        if videoid:
            link = self.listbase + link
        if "&" in link:
            link = link.split("&")[0]
        try:
            plist  = await Playlist.get(link)
            videos = plist.get("videos") or []
            ids    = [
                item["id"] for item in videos[:limit]
                if item and validate_video_id(item.get("id", ""))
            ]
            logger.info(f"[playlist] {len(ids)} valid video IDs fetched.")
            return ids
        except Exception as exc:
            logger.error(f"[playlist] Error: {exc}")
            return []

    # ── Download ──────────────────────────────────────────────────────────

    async def download(
        self,
        link: str,
        mystic,
        video:     Union[bool, str] = None,
        videoid:   Union[bool, str] = None,
        songaudio: Union[bool, str] = None,
        songvideo: Union[bool, str] = None,
        format_id: Union[bool, str] = None,
        title:     Union[bool, str] = None,
    ) -> Tuple[Optional[str], bool]:
        """
        Download via the hybrid waterfall.
        Returns (file_path_or_stream_url, True) on success, (None, False) on failure.
        """
        if videoid:
            link = self.base + link

        mode   = "video" if (video or songvideo) else "audio"
        vid_id = extract_video_id(link)
        if not vid_id:
            logger.error(f"[download] Invalid link: {link[:55]}")
            return None, False

        try:
            result = await (get_video_stream(link) if mode == "video" else get_stream(link))
            if result:
                logger.info(f"[download] ✅ {mode} ready for '{vid_id}'")
                return result, True
            logger.error(f"[download] All sources failed for '{vid_id}'")
            return None, False
        except Exception as exc:
            logger.error(f"[download] Unexpected error: {exc}")
            return None, False

    async def video(self, link: str, videoid: Union[bool, str] = None) -> Tuple[int, str]:
        """Legacy direct video download. Returns (1, path) or (0, error)."""
        link   = self._normalise(link, videoid)
        vid_id = extract_video_id(link)
        if not vid_id:
            return 0, "Invalid YouTube link"
        path = await _tertiary_download(vid_id, media_type="video")
        return (1, path) if path else (0, "Video download failed via all sources")


# ══════════════════════════════════════════════════════════════════════════════
#  MODULE-LEVEL UTILITY FUNCTIONS
# ══════════════════════════════════════════════════════════════════════════════

def get_rate_limit_status() -> Tuple[int, int, int, bool, str]:
    """Query Stream API rate-limit status (synchronous)."""
    if not _STREAM_API_TOKEN:
        return 0, 0, 0, False, "No API token configured"
    import requests as _req
    try:
        resp = _req.get(
            f"{_STREAM_API_BASE.rstrip('/')}/rate-limit-status",
            params={"token": _STREAM_API_TOKEN},
            timeout=10,
        )
        resp.raise_for_status()
        d = resp.json()
        return (d.get("daily_limit", 0), d.get("requests_used", 0),
                d.get("requests_remaining", 0), d.get("is_admin", False),
                d.get("reset_time", "N/A"))
    except Exception as exc:
        logger.error(f"[rate_limit_status] Error: {exc}")
        return 0, 0, 0, False, str(exc)


def get_trending_songs(limit: int = 10) -> List[Dict]:
    """Fetch trending songs from Stream API (synchronous)."""
    import requests as _req
    try:
        resp = _req.get(
            f"{_STREAM_API_BASE.rstrip('/')}/trending",
            params={"limit": limit},
            timeout=30,
        )
        resp.raise_for_status()
        return resp.json().get("results", [])
    except Exception as exc:
        logger.error(f"[trending] Error: {exc}")
        return []


def get_song_suggestions(query: str, limit: int = 5) -> List[str]:
    """Fetch search autocomplete suggestions from Stream API (synchronous)."""
    import requests as _req
    try:
        resp = _req.get(
            f"{_STREAM_API_BASE.rstrip('/')}/suggest",
            params={"q": query, "limit": limit},
            timeout=10,
        )
        resp.raise_for_status()
        return resp.json().get("results", [])
    except Exception as exc:
        logger.error(f"[suggestions] Error: {exc}")
        return []


def check_health() -> bool:
    """Ping the Stream API health endpoint (synchronous)."""
    import requests as _req
    try:
        return _req.get(f"{_STREAM_API_BASE.rstrip('/')}/health", timeout=5).status_code == 200
    except Exception:
        return False


def is_ytdlp_updated() -> bool:
    """Check if installed yt-dlp matches the latest PyPI version."""
    import requests as _req
    try:
        from importlib.metadata import version, PackageNotFoundError
        try:
            installed = version("yt-dlp")
        except PackageNotFoundError:
            return False
        latest  = _req.get("https://pypi.org/pypi/yt-dlp/json", timeout=10).json()["info"]["version"]
        current = installed == latest
        logger.info(f"[ytdlp_check] Installed={installed}, Latest={latest}, Current={current}")
        return current
    except Exception as exc:
        logger.error(f"[ytdlp_check] Error: {exc}")
        return False


async def check_and_update_ytdlp() -> None:
    """Async: update yt-dlp if it is outdated."""
    try:
        if not is_ytdlp_updated():
            logger.info("[ytdlp_update] Updating yt-dlp…")
            proc = await asyncio.create_subprocess_exec(
                sys.executable, "-m", "pip", "install", "-U", "yt-dlp",
                stdout=asyncio.subprocess.PIPE,
                stderr=asyncio.subprocess.PIPE,
            )
            await asyncio.wait_for(proc.communicate(), timeout=120)
            logger.info("[ytdlp_update] Update complete.")
        else:
            logger.info("[ytdlp_update] yt-dlp is already up to date.")
    except Exception as exc:
        logger.error(f"[ytdlp_update] Error: {exc}")


# ══════════════════════════════════════════════════════════════════════════════
#  LEGACY ENTRY POINTS  (flat 8-tuple signature for existing handlers)
# ══════════════════════════════════════════════════════════════════════════════

async def handle_youtube(argument: str) -> Tuple:
    """
    Top-level entry point for handlers expecting an 8-tuple:
        (title, duration, youtube_url, thumbnail, channel, views, video_id, stream_url)
    """
    logger.debug(f"[handle_youtube] argument='{argument[:55]}'")
    result = await get_video_info(argument)
    title, video_id, duration, yt_url, channel, views, stream_url, thumbnail, source = result

    if not title or title == "N/A":
        logger.warning("[handle_youtube] No usable data returned.")
        return ("Error", "00:00", None, None, None, None, None, None)

    logger.info(f"[handle_youtube] ✅ '{title}' (source={source})")
    return (title, duration, yt_url, thumbnail, channel, views, video_id, stream_url)


async def handle_youtube_ytdlp(argument: str) -> Optional[Tuple]:
    """
    Variant that forces Tier 2 (yt-dlp) source — useful for debugging.
    """
    logger.debug(f"[handle_youtube_ytdlp] argument='{argument[:55]}'")
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
    Call this in your bot's on_shutdown / stop handler to release connections.
    """
    global _http_session
    async with _http_session_lock:
        if _http_session and not _http_session.closed:
            await _http_session.close()
            _http_session = None
            logger.info("[Session] Persistent aiohttp.ClientSession closed.")
