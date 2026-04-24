import asyncio
import os
import re
import hmac
import hashlib
import time
from typing import Union

import yt_dlp
from pyrogram.enums import MessageEntityType
from pyrogram.types import Message
from py_yt import VideosSearch, Playlist
from ShrutiMusic.utils.formatters import time_to_seconds
import aiohttp
from ShrutiMusic import LOGGER

# ─── load from .env ───────────────────────────────────────────────────────
WORKER_URL    = os.environ.get("WORKER_URL", "").rstrip("/")
WORKER_SECRET = os.environ.get("WORKER_SECRET", "")

if not WORKER_URL or not WORKER_SECRET:
    LOGGER(__name__).warning("WORKER_URL ya WORKER_SECRET .env mein set nahi hai!")
# ─────────────────────────────────────────────────────────────────────────────

DOWNLOAD_DIR = "downloads"

# ✅ Sirf yeh characters allowed hain video_id mein — kuch bhi extra = reject
_SAFE_VIDEO_ID = re.compile(r'^[A-Za-z0-9_\-]{3,20}$')


def _sanitize_video_id(raw: str) -> Union[str, None]:
    """
    video_id ko sanitize karta hai.
    Path traversal (../) ya shell injection possible nahi hoga.
    Invalid ID milne par None return karta hai.
    """
    if not raw:
        return None
    # URL se video_id nikalo
    if 'v=' in raw:
        raw = raw.split('v=')[-1].split('&')[0]
    elif 'youtu.be/' in raw:
        raw = raw.split('youtu.be/')[-1].split('?')[0]
    raw = raw.strip()
    if not _SAFE_VIDEO_ID.match(raw):
        LOGGER(__name__).warning(f"Unsafe video_id rejected: {raw!r}")
        return None
    return raw


def _sanitize_link(link: str) -> Union[str, None]:
    """
    YouTube link validate karta hai.
    Sirf youtube.com aur youtu.be URLs allowed hain.
    """
    if not link or not isinstance(link, str):
        return None
    link = link.strip()
    if not re.search(r'(?:youtube\.com|youtu\.be)', link):
        LOGGER(__name__).warning(f"Non-YouTube link rejected: {link!r}")
        return None
    # Shell-injectable characters remove
    if re.search(r'[;&|`$<>]', link):
        LOGGER(__name__).warning(f"Suspicious characters in link: {link!r}")
        return None
    return link


def _sign_request(video_id: str = "", media_type: str = "") -> dict:
    """
    video_id + media_type + exp sab sign hota hai.
    Koi bhi param intercept karke badal nahi sakta — sig mismatch hoga.
    """
    exp = str(int(time.time()) + 300)
    data = f"{video_id}:{media_type}:{exp}:{WORKER_SECRET}"
    sig = hmac.new(
        WORKER_SECRET.encode(),
        data.encode(),
        hashlib.sha256
    ).hexdigest()
    return {"exp": exp, "sig": sig}


async def download_song(link: str) -> str:
    # ✅ video_id sanitize pehle
    video_id = _sanitize_video_id(link)
    if not video_id:
        return None

    os.makedirs(DOWNLOAD_DIR, exist_ok=True)

    # ✅ os.path.join ke baad bhi check — path traversal double-check
    file_path = os.path.realpath(os.path.join(DOWNLOAD_DIR, f"{video_id}.mp3"))
    if not file_path.startswith(os.path.realpath(DOWNLOAD_DIR)):
        LOGGER(__name__).warning(f"Path traversal attempt blocked: {video_id}")
        return None

    if os.path.exists(file_path):
        return file_path

    try:
        async with aiohttp.ClientSession() as session:
            auth = _sign_request(video_id, "audio")
            params = {"url": video_id, "type": "audio", **auth}

            async with session.get(
                f"{WORKER_URL}/download",
                params=params,
                timeout=aiohttp.ClientTimeout(total=7)
            ) as response:
                if response.status != 200:
                    return None

                data = await response.json()
                download_token = data.get("download_token")

                if not download_token:
                    return None

                auth2 = _sign_request(video_id, "audio")
                stream_url = (
                    f"{WORKER_URL}/stream/{video_id}"
                    f"?type=audio&token={download_token}"
                    f"&url={video_id}&exp={auth2['exp']}&sig={auth2['sig']}"
                )

                async with session.get(
                    stream_url,
                    timeout=aiohttp.ClientTimeout(total=300)
                ) as file_response:
                    if file_response.status == 302:
                        redirect_url = file_response.headers.get('Location')
                        if redirect_url:
                            async with session.get(redirect_url) as final_response:
                                if final_response.status != 200:
                                    return None
                                with open(file_path, "wb") as f:
                                    async for chunk in final_response.content.iter_chunked(16384):
                                        f.write(chunk)
                                if os.path.exists(file_path) and os.path.getsize(file_path) > 0:
                                    return file_path
                                return None
                    elif file_response.status == 200:
                        with open(file_path, "wb") as f:
                            async for chunk in file_response.content.iter_chunked(16384):
                                f.write(chunk)
                        if os.path.exists(file_path) and os.path.getsize(file_path) > 0:
                            return file_path
                        return None
                    else:
                        return None

    except Exception:
        if os.path.exists(file_path):
            try:
                os.remove(file_path)
            except:
                pass
        return None


async def download_video(link: str) -> str:
    # ✅ video_id sanitize pehle
    video_id = _sanitize_video_id(link)
    if not video_id:
        return None

    os.makedirs(DOWNLOAD_DIR, exist_ok=True)

    file_path = os.path.realpath(os.path.join(DOWNLOAD_DIR, f"{video_id}.mp4"))
    if not file_path.startswith(os.path.realpath(DOWNLOAD_DIR)):
        LOGGER(__name__).warning(f"Path traversal attempt blocked: {video_id}")
        return None

    if os.path.exists(file_path):
        return file_path

    try:
        async with aiohttp.ClientSession() as session:
            auth = _sign_request(video_id, "video")
            params = {"url": video_id, "type": "video", **auth}

            async with session.get(
                f"{WORKER_URL}/download",
                params=params,
                timeout=aiohttp.ClientTimeout(total=7)
            ) as response:
                if response.status != 200:
                    return None

                data = await response.json()
                download_token = data.get("download_token")

                if not download_token:
                    return None

                auth2 = _sign_request(video_id, "video")
                stream_url = (
                    f"{WORKER_URL}/stream/{video_id}"
                    f"?type=video&token={download_token}"
                    f"&url={video_id}&exp={auth2['exp']}&sig={auth2['sig']}"
                )

                async with session.get(
                    stream_url,
                    timeout=aiohttp.ClientTimeout(total=600)
                ) as file_response:
                    if file_response.status == 302:
                        redirect_url = file_response.headers.get('Location')
                        if redirect_url:
                            async with session.get(redirect_url) as final_response:
                                if final_response.status != 200:
                                    return None
                                with open(file_path, "wb") as f:
                                    async for chunk in final_response.content.iter_chunked(16384):
                                        f.write(chunk)
                                if os.path.exists(file_path) and os.path.getsize(file_path) > 0:
                                    return file_path
                                return None
                    elif file_response.status == 200:
                        with open(file_path, "wb") as f:
                            async for chunk in file_response.content.iter_chunked(16384):
                                f.write(chunk)
                        if os.path.exists(file_path) and os.path.getsize(file_path) > 0:
                            return file_path
                        return None
                    else:
                        return None

    except Exception:
        if os.path.exists(file_path):
            try:
                os.remove(file_path)
            except:
                pass
        return None


class YouTubeAPI:
    def __init__(self):
        self.base = "https://www.youtube.com/watch?v="
        self.regex = r"(?:youtube\.com|youtu\.be)"
        self.status = "https://www.youtube.com/oembed?url="
        self.listbase = "https://youtube.com/playlist?list="
        self.reg = re.compile(r"\x1B(?:[@-Z\\-_]|\[[0-?]*[ -/]*[@-~])")

    async def exists(self, link: str, videoid: Union[bool, str] = None):
        if videoid:
            link = self.base + link
        return bool(re.search(self.regex, link))

    async def url(self, message_1: Message) -> Union[str, None]:
        messages = [message_1]
        if message_1.reply_to_message:
            messages.append(message_1.reply_to_message)
        for message in messages:
            if message.entities:
                for entity in message.entities:
                    if entity.type == MessageEntityType.URL:
                        text = message.text or message.caption
                        url = text[entity.offset: entity.offset + entity.length]
                        # ✅ /play command se aaya link validate karo
                        return _sanitize_link(url)
            elif message.caption_entities:
                for entity in message.caption_entities:
                    if entity.type == MessageEntityType.TEXT_LINK:
                        return _sanitize_link(entity.url)
        return None

    async def details(self, link: str, videoid: Union[bool, str] = None):
        if videoid:
            link = self.base + link
        if "&" in link:
            link = link.split("&")[0]
        # ✅ link validate karo
        link = _sanitize_link(link)
        if not link:
            return None, None, 0, None, None
        results = VideosSearch(link, limit=1)
        for result in (await results.next())["result"]:
            title = result["title"]
            duration_min = result["duration"]
            thumbnail = result["thumbnails"][0]["url"].split("?")[0]
            vidid = result["id"]
            duration_sec = int(time_to_seconds(duration_min)) if duration_min else 0
        return title, duration_min, duration_sec, thumbnail, vidid

    async def title(self, link: str, videoid: Union[bool, str] = None):
        if videoid:
            link = self.base + link
        if "&" in link:
            link = link.split("&")[0]
        link = _sanitize_link(link)
        if not link:
            return None
        results = VideosSearch(link, limit=1)
        for result in (await results.next())["result"]:
            return result["title"]

    async def duration(self, link: str, videoid: Union[bool, str] = None):
        if videoid:
            link = self.base + link
        if "&" in link:
            link = link.split("&")[0]
        link = _sanitize_link(link)
        if not link:
            return None
        results = VideosSearch(link, limit=1)
        for result in (await results.next())["result"]:
            return result["duration"]

    async def thumbnail(self, link: str, videoid: Union[bool, str] = None):
        if videoid:
            link = self.base + link
        if "&" in link:
            link = link.split("&")[0]
        link = _sanitize_link(link)
        if not link:
            return None
        results = VideosSearch(link, limit=1)
        for result in (await results.next())["result"]:
            return result["thumbnails"][0]["url"].split("?")[0]

    async def video(self, link: str, videoid: Union[bool, str] = None):
        if videoid:
            link = self.base + link
        if "&" in link:
            link = link.split("&")[0]
        # ✅ link validate
        link = _sanitize_link(link)
        if not link:
            return 0, "Invalid link"
        try:
            downloaded_file = await download_video(link)
            if downloaded_file:
                return 1, downloaded_file
            else:
                return 0, "Video download failed"
        except Exception as e:
            return 0, f"Video download error: {e}"

    async def playlist(self, link, limit, user_id, videoid: Union[bool, str] = None):
        if videoid:
            link = self.listbase + link
        if "&" in link:
            link = link.split("&")[0]
        # ✅ playlist link validate
        if not link or not re.search(r'youtube\.com/playlist', link):
            return []
        try:
            plist = await Playlist.get(link)
        except:
            return []

        videos = plist.get("videos") or []
        ids = []
        for data in videos[:limit]:
            if not data:
                continue
            vid = data.get("id")
            # ✅ playlist ke har video_id ko bhi sanitize karo
            if not vid or not _SAFE_VIDEO_ID.match(str(vid)):
                continue
            ids.append(vid)
        return ids

    async def track(self, link: str, videoid: Union[bool, str] = None):
        if videoid:
            link = self.base + link
        if "&" in link:
            link = link.split("&")[0]
        link = _sanitize_link(link)
        if not link:
            return {}, None
        results = VideosSearch(link, limit=1)
        for result in (await results.next())["result"]:
            title = result["title"]
            duration_min = result["duration"]
            vidid = result["id"]
            yturl = result["link"]
            thumbnail = result["thumbnails"][0]["url"].split("?")[0]
        track_details = {
            "title": title,
            "link": yturl,
            "vidid": vidid,
            "duration_min": duration_min,
            "thumb": thumbnail,
        }
        return track_details, vidid

    async def formats(self, link: str, videoid: Union[bool, str] = None):
        if videoid:
            link = self.base + link
        if "&" in link:
            link = link.split("&")[0]
        # ✅ yt_dlp ko koi bhi raw link dena dangerous — pehle validate karo
        link = _sanitize_link(link)
        if not link:
            return [], None
        ytdl_opts = {"quiet": True}
        ydl = yt_dlp.YoutubeDL(ytdl_opts)
        with ydl:
            formats_available = []
            r = ydl.extract_info(link, download=False)
            for format in r["formats"]:
                try:
                    if "dash" not in str(format["format"]).lower():
                        formats_available.append(
                            {
                                "format": format["format"],
                                "filesize": format.get("filesize"),
                                "format_id": format["format_id"],
                                "ext": format["ext"],
                                "format_note": format["format_note"],
                                "yturl": link,
                            }
                        )
                except:
                    continue
        return formats_available, link

    async def slider(self, link: str, query_type: int, videoid: Union[bool, str] = None):
        if videoid:
            link = self.base + link
        if "&" in link:
            link = link.split("&")[0]
        link = _sanitize_link(link)
        if not link:
            return None, None, None, None
        a = VideosSearch(link, limit=10)
        result = (await a.next()).get("result")
        title = result[query_type]["title"]
        duration_min = result[query_type]["duration"]
        vidid = result[query_type]["id"]
        thumbnail = result[query_type]["thumbnails"][0]["url"].split("?")[0]
        return title, duration_min, thumbnail, vidid

    async def download(
        self,
        link: str,
        mystic,
        video: Union[bool, str] = None,
        videoid: Union[bool, str] = None,
        songaudio: Union[bool, str] = None,
        songvideo: Union[bool, str] = None,
        format_id: Union[bool, str] = None,
        title: Union[bool, str] = None,
    ) -> str:
        if videoid:
            link = self.base + link

        try:
            if video:
                downloaded_file = await download_video(link)
            else:
                downloaded_file = await download_song(link)

            if downloaded_file:
                return downloaded_file, True
            else:
                return None, False
        except Exception:
            return None, False
