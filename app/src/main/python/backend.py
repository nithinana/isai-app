"""
YouTube Music API powered by yt-dlp + FastAPI (Render Deployment Ready).

Endpoints:
  GET /search?q=...&type=songs|albums|artists|playlists&limit=20
  GET /album/{browse_id}              Album + tracks
  GET /artist/{channel_id}            Artist: top songs, albums, singles
  GET /home                           Tamil / India home feed (songs, playlists, albums, artists)
  GET /track/{video_id}               Track metadata
  GET /stream/{video_id}              Direct audio URL (expires after a few hours)
  GET /sources/{video_id}?probe=false List every source (client + format) with a network stream link each
  GET /stream/{video_id}?client=&fmt= Pin a specific source from /sources
  GET /download/{video_id}?fmt=mp3    Download audio file (needs ffmpeg for conversion)
  GET /playlist/{playlist_id}         Playlist / album track list
  GET /mood?name=Relax                Mood feeds
  GET /lyrics/{video_id}?title=&artist=&album=&isrc=&source=auto|unison|lrcred
                                      Synced lyrics (Unison + lrc.red), parsed into timed lines
  GET /import?url=...                 Import a PUBLIC / unlisted YouTube playlist (all tracks)
  GET /charts/countries               Countries available for charts
  GET /charts/{code}                  Chart playlists + top songs + top artists (ZZ = global)
  GET /cookies/refresh                Re-run the Google sign-in now and rewrite cookies.txt
  GET /health                         Health check & ffmpeg status

Automatic cookie sync (merged from ka.py / yt-dlp-Cookie-Sync):
  Set GOOGLE_EMAIL and GOOGLE_PASSWORD (env vars, never hard-code them). On startup and then
  every COOKIE_REFRESH_HOURS (default 6) a Playwright browser signs in, grabs the YouTube
  cookies and atomically rewrites cookies.txt (or $YTDLP_COOKIES). base_opts() re-reads that
  file on every request, so fresh cookies are used with no restart.
  Optional: COOKIE_HEADLESS=true|false (default true), COOKIE_BROWSER_CHANNEL (e.g. chrome).

Deployment on Render (Docker runtime, so ffmpeg + node are available):
  Dockerfile and requirements.txt sit next to this file. Render sets $PORT.
  Health check path: /health

Why this differs from the localhost version:
  * YouTube audio URLs are locked to the IP that requested them. On localhost the
    server and browser share an IP, on Render they don't, so /stream hands back a
    URL on THIS server (/audio/{id}) which proxies the bytes (Range supported).
  * Datacenter IPs get bot-checked more, so set cookies / PO token / proxy via env.
  * If ffmpeg is missing, /download falls back to the native format instead of 500.
"""
import sys
import io
import os
import re
import shutil
import tempfile
import threading
import time
from contextlib import asynccontextmanager
from concurrent.futures import ThreadPoolExecutor
from functools import lru_cache, wraps
from typing import Optional
from urllib.error import HTTPError
from urllib.parse import quote, urlencode
from urllib.request import ProxyHandler, Request as UrlRequest, build_opener, urlopen
import asyncio
import yt_dlp

try:
    from PIL import Image, ImageChops
except ImportError:  # covers still work, just without auto-cropping
    Image = ImageChops = None

from fastapi import Depends, FastAPI, Header, HTTPException, Query, Request
from fastapi.middleware.cors import CORSMiddleware
from fastapi.responses import FileResponse, RedirectResponse, Response, StreamingResponse
from starlette.background import BackgroundTask

if sys.platform == "win32":
    asyncio.set_event_loop_policy(asyncio.WindowsSelectorEventLoopPolicy())

API_KEY = os.getenv("API_KEY")  # optional: set X-API-Key header in Render env vars
MUSIC_URL = "https://music.youtube.com"
VIDEO_ID_RE = re.compile(r"^[\w-]{11}$")
PLAYLIST_ID_RE = re.compile(r"^[\w-]{10,64}$")
MUSIC_SONGS_FILTER = "EgWKAQIIAWoMEA4QChADEAQQCRAF"  # YT Music "Songs" filter
ALLOWED_FORMATS = {"mp3", "m4a", "opus", "flac", "wav", "best"}
STREAM_CHUNK_SIZE = 256 * 1024  # 256 KB buffer for faster byte streaming


# ---- Automatic cookie sync (merged from ka.py) ---------------------------------------
GOOGLE_EMAIL = os.getenv("GOOGLE_EMAIL")
GOOGLE_PASSWORD = os.getenv("GOOGLE_PASSWORD")
COOKIE_SYNC_ENABLED = bool(GOOGLE_EMAIL and GOOGLE_PASSWORD)
COOKIE_REFRESH_HOURS = float(os.getenv("COOKIE_REFRESH_HOURS", "6"))
COOKIE_HEADLESS = os.getenv("COOKIE_HEADLESS", "true").lower() != "false"
COOKIE_BROWSER_CHANNEL = os.getenv("COOKIE_BROWSER_CHANNEL") or None  # e.g. "chrome"
COOKIE_PATH = os.getenv("YTDLP_COOKIES") or os.path.join(os.path.dirname(os.path.abspath(__file__)), "cookies.txt")

_cookie_lock = threading.Lock()
_cookie_state: dict = {"last_ok": None, "last_error": None, "count": 0}


def _cookies_to_netscape(cookies: list) -> str:
    """Convert Playwright's cookie dicts to the Netscape format yt-dlp reads."""
    lines = ["# Netscape HTTP Cookie File", "# https://curl.haxx.se/docs/http-cookies.html",
             "# Generated by the built-in cookie sync. Edit at your own risk.", ""]
    for c in cookies:
        domain = c["domain"]
        expires = int(c["expires"]) if c.get("expires", -1) and c["expires"] > 0 else 0
        lines.append("\t".join([
            ("#HttpOnly_" if c.get("httpOnly") else "") + domain,
            "TRUE" if domain.startswith(".") else "FALSE",
            c["path"],
            "TRUE" if c.get("secure") else "FALSE",
            str(expires),
            c["name"],
            c["value"],
        ]))
    return "\n".join(lines) + "\n"


async def _fetch_google_cookies() -> list:
    """Sign in to Google with Playwright and return the cookie jar after visiting YouTube."""
    from playwright.async_api import async_playwright

    async with async_playwright() as pw:
        print("[cookie-sync] opening browser...", flush=True)
        launch = dict(headless=COOKIE_HEADLESS, args=[
            "--disable-blink-features=AutomationControlled",
            "--no-sandbox",
            "--disable-dev-shm-usage",
        ])
        if COOKIE_BROWSER_CHANNEL:
            launch["channel"] = COOKIE_BROWSER_CHANNEL
        browser = await pw.chromium.launch(**launch)
        try:
            context = await browser.new_context()
            page = await context.new_page()

            print("[cookie-sync] signing in...", flush=True)
            await page.goto("https://accounts.google.com/signin/v2/identifier")
            await page.get_by_role("textbox").fill(GOOGLE_EMAIL)
            await page.get_by_text("Next").click()
            await page.wait_for_timeout(10000)

            await page.get_by_role("textbox").fill(GOOGLE_PASSWORD)
            await page.get_by_text("Next").click()
            await page.wait_for_timeout(10000)

            print("[cookie-sync] visiting YouTube for cookie extraction...", flush=True)
            await page.goto("https://www.youtube.com/")
            await page.wait_for_timeout(5000)
            return await context.cookies()
        finally:
            await browser.close()


def _cookie_sync_blocking() -> int:
    """Runs in a worker thread with its own event loop (Playwright needs a Proactor loop on
    Windows, but the main loop is forced to the Selector policy above)."""
    loop = asyncio.ProactorEventLoop() if sys.platform == "win32" else asyncio.new_event_loop()
    try:
        cookies = loop.run_until_complete(_fetch_google_cookies())
    finally:
        loop.close()

    names = {c["name"] for c in cookies}
    if "SID" not in names and "__Secure-1PSID" not in names:
        raise RuntimeError("sign-in did not produce Google auth cookies (captcha / 2FA / blocked login?)")

    # Atomic replace so yt-dlp never reads a half-written file; old cookies survive a failed run.
    tmp = COOKIE_PATH + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        f.write(_cookies_to_netscape(cookies))
    os.replace(tmp, COOKIE_PATH)
    return len(cookies)


async def refresh_cookies() -> dict:
    if not COOKIE_SYNC_ENABLED:
        raise RuntimeError("Set GOOGLE_EMAIL and GOOGLE_PASSWORD to enable cookie sync")
    if not _cookie_lock.acquire(blocking=False):
        return {"status": "already_running"}
    try:
        count = await asyncio.to_thread(_cookie_sync_blocking)
        _cookie_state.update(last_ok=time.time(), last_error=None, count=count)
        print(f"[cookie-sync] wrote {count} cookies to {COOKIE_PATH}", flush=True)
        return {"status": "ok", "cookies": count}
    except Exception as e:
        _cookie_state["last_error"] = f"{type(e).__name__}: {e}"
        print(f"[cookie-sync] FAILED: {_cookie_state['last_error']}", flush=True)
        raise
    finally:
        _cookie_lock.release()


async def _cookie_sync_loop():
    while True:
        try:
            await refresh_cookies()
        except Exception:
            pass  # already logged; keep the previous cookies and retry next cycle
        await asyncio.sleep(max(COOKIE_REFRESH_HOURS, 0.1) * 3600)


@asynccontextmanager
async def lifespan(_app):
    task = asyncio.create_task(_cookie_sync_loop()) if COOKIE_SYNC_ENABLED else None
    if not COOKIE_SYNC_ENABLED:
        print("[cookie-sync] disabled (GOOGLE_EMAIL / GOOGLE_PASSWORD not set)", flush=True)
    yield
    if task:
        task.cancel()


app = FastAPI(title="YouTube Music API", version="1.0.0", lifespan=lifespan)

# Enables CORS for frontend apps or direct browser access
app.add_middleware(
    CORSMiddleware,
    allow_origins=["*"],
    allow_methods=["GET"],
    allow_headers=["*"],
    expose_headers=["Content-Disposition"],
)


# ---- Frontend (index.html) embedded by merge_isai.py ----
_EMBEDDED_HTML_B64 = (
    "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"
    "D1A0ItUciEikOi1rZOUHH2GsTk++OD35jdOT3zo9+e3Tk989Pfm905M/OD35w9OTPzo9+a9OT/7r05N/fHryT05P/rvTk392evLP"
    "T0/+x9OT//n05E9PT/6305N/eXryf5ye/J+nJ//X6cn/fXry/5ye/OvTk393evIXpyf/8fTkr09P/ub0i5+efnFy+sUXp1/8xukX"
    "v3X6xW+ffvE7p1/87ukXv3f6xe+ffvEHp1/84ekXf3z6BX3r909P/sHpyT88Pfnj05M/OT35R6cn/83pyX97evJPT0/++9OT/+H0"
    "5F+cnvwvpyf/6+nJ/3568q9OT/7N6cm/Pz35y9OTvzo9+bPTk397evLnpyf/4fTkP51+8Q9Pv/ij0y/+xMst+IPnrGOkM38eJcQe"
    "7cXRXhrtzaM9GugsKnGYpVE5j0oO5Z/FtKLTaEY3ZhxDSVMxTYl9ItIPLnsUR/R4Zx4BIziLJnE0SaPJPJok0SSLjuLoaB4dZbQ1"
    "oiIl+SECil0WHeBcpdW9G0e7abQ7j3YTIGN+Hkc0sZ/Po8+T6HOkltWfQ/gN0vEQ9dOoP8ec97Moj6M8jfJ5lCdRTlWm0UES7c9b"
    "vTIfp7N2K/K9IX/wRAz2TDl+8NGW25YDsy1/8AR6z5s0QMTshOp4LMAaHRqpQFQknBWuDTPclZU7q2Jfu7a1vNuFyv1WM8fYQKCu"
    "rXS87Oiiw+waNgKXJYfCeQo51UzO2Tu+cO5OJcLfJFt40eNQ//JHtD/aoMNGj3iRHq9FxeYKtmqxHlROZILVZnRbP1+sG9FNnbqS"
    "3H0STc1cfE7mOB68bU3rFxvrY3ZUxfcRnOxGYTL2gbjQ0Qb9nwSGl9spsZJ1PjJ449f/ykWOMkvKncLlptcwZjSb6tLQaj4cW6df"
    "/HpLpVm6/s2WGuvo+u+32PIWHW8ORoHO98j/uA8BTrSbbyXToc5LKpAmeXuzRbsP9Q7kzyviFIiVHYznQ+KrpBe35W073pdWMbZH"
    "0Vrj/dYR5vrIROuxIOPuLer1vvb65MT1+oRHIJVrbwROeAQSuf6dRaOx74+GJohuSadbB2jOfsfLVCQ9xcOmPu0Hvdk/ox/YAtjY"
    "YVsE6zQ4M3lpDEbrbr9Zuw1/pOg0sM11JfG9oyIdU2Opkd8vkmSvrsr9sRKi1lf/KorffPVnUf/NV/862n/z1b+Jdt989W+j4Zuv"
    "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"
    "e1HPZ0/u/D+iAXf0"
)


@lru_cache(maxsize=1)
def _embedded_html() -> bytes:
    import base64, zlib
    return zlib.decompress(base64.b64decode("".join(_EMBEDDED_HTML_B64)))


@app.get("/", include_in_schema=False)
def gui():
    return Response(_embedded_html(), media_type="text/html; charset=utf-8",
                    headers={"Cache-Control": "no-cache"})


def ttl_cache(ttl: int = 900, maxsize: int = 500):
    """In-memory cache for instant repeat responses."""
    def deco(fn):
        store: dict = {}

        @wraps(fn)
        def wrapper(*a, **kw):
            key = (a, tuple(sorted(kw.items())))
            hit = store.get(key)
            if hit and time.time() - hit[0] < ttl:
                return hit[1]
            val = fn(*a, **kw)  # exceptions are not cached
            store[key] = (time.time(), val)
            if len(store) > maxsize:
                store.pop(next(iter(store)))
            return val
        return wrapper
    return deco


def require_key(x_api_key: Optional[str] = Header(default=None)):
    if API_KEY and x_api_key != API_KEY:
        raise HTTPException(401, "Invalid or missing X-API-Key")


# ---- Embedded YouTube cookies --------------------------------------------------
_EMBEDDED_COOKIES_B64 = (
    ""
)


def _write_embedded_cookies() -> Optional[str]:
    import base64
    import zlib
    raw = "".join(_EMBEDDED_COOKIES_B64.split())
    if not raw:
        return None
    try:
        text = zlib.decompress(base64.b64decode(raw)).decode("utf-8")
        path = os.path.join(tempfile.gettempdir(), "yt_embedded_cookies.txt")
        with open(path, "w", encoding="utf-8") as f:
            f.write(text)
        return path
    except Exception:
        return None


EMBEDDED_COOKIE_FILE = _write_embedded_cookies()


def _js_runtimes() -> dict:
    """yt-dlp needs deno >= 2 or node >= 20 to solve YouTube's n-challenge.
    An old node (e.g. Ubuntu's v12) makes every format vanish -> 'Requested format is not available'."""
    import subprocess
    found = {}
    for name in ("deno", "node", "bun"):
        path = shutil.which(name) or next((p for p in (
            os.path.expanduser(f"~/.deno/bin/{name}"), f"/usr/local/bin/{name}") if os.path.exists(p)), None)
        if not path:
            continue
        try:
            out = subprocess.run([path, "--version"], capture_output=True, text=True, timeout=5).stdout
            major = int(re.search(r"(\d+)\.", out).group(1))
        except Exception:
            continue
        if (name == "node" and major < 22) or (name == "deno" and major < 2):
            print(f"[js-runtime] ignoring {name} {out.strip()} (too old)", flush=True)
            continue
        found[name] = {"path": path}
    if not found:
        print("[js-runtime] NO usable JS runtime (need deno>=2 or node>=22)", flush=True)
    return found


def base_opts(**extra) -> dict:
    """Configures yt-dlp with player clients, PO Tokens, and cookie authentication."""
    # android/ios clients need PO tokens now and ignore cookies, so by default let
    # yt-dlp pick its own clients (tv / web_safari with cookies). Override via env.
    clients = [c for c in os.getenv("YTDLP_PLAYER_CLIENT", "").split(",") if c]
    youtube_args = {}
    if clients:
        youtube_args["player_client"] = clients

    po_token = os.getenv("YTDLP_PO_TOKEN")
    visitor_data = os.getenv("YTDLP_VISITOR_DATA")
    if po_token:
        youtube_args["po_token"] = [po_token]
    if visitor_data:
        youtube_args["visitor_data"] = [visitor_data]

    opts = {
        "quiet": True,
        "no_warnings": True,
        "noplaylist": True,
        "skip_download": True,
        "socket_timeout": 10,       # Reduced from 20s to fail fast
        "retries": 1,              # Reduced from 2 to avoid blocking requests
        "extractor_retries": 1,
        "ignoreerrors": True,   # extract()/_resolve_audio() override this to False
        "no_check_certificate": True,
        "extractor_args": {
            "youtube": youtube_args,
        },
    }

    runtimes = _js_runtimes()
    if runtimes:
        opts["js_runtimes"] = runtimes
    remote = os.getenv("YTDLP_REMOTE_COMPONENTS", "ejs:github")
    if remote:
        opts["remote_components"] = [c for c in remote.split(",") if c]

    cookie_file = os.getenv("YTDLP_COOKIES") or os.path.join(os.path.dirname(os.path.abspath(__file__)), "cookies.txt")
    if os.path.exists(cookie_file):
        # Use the real file directly (same as the yt-dlp CLI). A /tmp copy goes stale
        # because yt-dlp rewrites it on close, so mtime checks never refresh it.
        opts["cookiefile"] = cookie_file

    if not opts.get("cookiefile") and EMBEDDED_COOKIE_FILE:
        opts["cookiefile"] = EMBEDDED_COOKIE_FILE

    cookie_text = os.getenv("YTDLP_COOKIES_TEXT")
    if cookie_text and not opts.get("cookiefile"):
        clean_cookies = cookie_text.replace("\\n", "\n")
        tmp_cookie = os.path.join(tempfile.gettempdir(), "render_yt_cookies.txt")
        try:
            with open(tmp_cookie, "w", encoding="utf-8") as f:
                f.write(clean_cookies)
            opts["cookiefile"] = tmp_cookie
        except Exception:
            pass

    if os.getenv("YTDLP_COOKIES_FROM_BROWSER"):
        browser_spec = os.getenv("YTDLP_COOKIES_FROM_BROWSER").split(":")
        opts["cookiesfrombrowser"] = tuple(browser_spec)

    proxy = os.getenv("YTDLP_PROXY")
    if proxy:
        opts["proxy"] = proxy

    opts.update(extra)
    return opts


def check_video_id(video_id: str) -> str:
    if not VIDEO_ID_RE.match(video_id):
        raise HTTPException(400, "Invalid video id")
    return video_id


CLIENT_FALLBACKS = [c for c in os.getenv(
    "YTDLP_CLIENT_FALLBACKS", "tv,web_safari;mweb;web;default"
).split(";") if c]
_RETRY_HINTS = ("reloaded", "Sign in to confirm", "not a bot", "player response", "n challenge", "Requested format")


def extract(url: str, opts: dict, download: bool = False) -> dict:
    import copy

    current = ",".join(opts.get("extractor_args", {}).get("youtube", {}).get("player_client", []))
    attempts = [None] + [c for c in CLIENT_FALLBACKS if c != current]
    last = None
    started = time.time()
    for clients in attempts:
        if last and time.time() - started > 70:
            break
        o = copy.deepcopy(opts)
        o["ignoreerrors"] = False  # otherwise errors return None and fallbacks never run
        if clients:
            o.setdefault("extractor_args", {}).setdefault("youtube", {})["player_client"] = clients.split(",")
        try:
            with yt_dlp.YoutubeDL(o) as ydl:
                res = ydl.extract_info(url, download=download)
            if res:
                return res
            last = "no result"
        except yt_dlp.utils.DownloadError as e:
            last = re.sub(r"\x1b\[[0-9;]*m", "", str(e))
            if not any(h in last for h in _RETRY_HINTS):
                break
    raise HTTPException(502, f"yt-dlp error: {last}")


def thumb(info: dict) -> Optional[str]:
    if info.get("thumbnail"):
        return info["thumbnail"]
    thumbs = info.get("thumbnails") or []
    return thumbs[-1]["url"] if thumbs else None


def track_summary(info: dict) -> dict:
    artist = (
        info.get("artist")
        or (", ".join(info["artists"]) if info.get("artists") else None)
        or info.get("uploader")
        or info.get("channel")
    )
    if artist:
        artist = re.sub(r"\s*-\s*Topic$", "", artist)
    vid = info.get("id")
    return {
        "id": vid,
        "title": info.get("track") or info.get("title"),
        "artist": artist,
        "album": info.get("album"),
        "duration": info.get("duration"),
        "thumbnail": thumb(info) or f"https://i.ytimg.com/vi/{vid}/hqdefault.jpg",
        "url": f"{MUSIC_URL}/watch?v={vid}",
    }


# ---- ytmusicapi (search, albums, artists, curated playlists) ------------------
try:
    from ytmusicapi import YTMusic
except ImportError:
    YTMusic = None

_ytm_client = None
ID_RE = re.compile(r"^[\w-]{5,80}$")
SEARCH_TYPES = {"songs", "albums", "artists", "playlists"}
_BAD_VIDEO_TYPES = ("MUSIC_VIDEO_TYPE_OMV", "MUSIC_VIDEO_TYPE_UGC")


def ytm():
    global _ytm_client
    if YTMusic is None:
        raise HTTPException(501, "ytmusicapi is not installed. Run: pip install ytmusicapi")
    if _ytm_client is None:
        try:
            _ytm_client = YTMusic(language="en", location="IN")
        except Exception:
            _ytm_client = YTMusic()
    return _ytm_client


def ytm_call(method: str, *args, **kw):
    try:
        return getattr(ytm(), method)(*args, **kw)
    except HTTPException:
        raise
    except Exception as e:
        raise HTTPException(502, f"YouTube Music error: {e}")


def check_id(x: str) -> str:
    if not ID_RE.match(x):
        raise HTTPException(400, "Invalid id")
    return x


def _best_thumb(thumbs):
    if not thumbs:
        return None
    return max(thumbs, key=lambda t: (t.get("width") or 0)).get("url")


def _artist_names(x: dict):
    names = []
    arts = x.get("artists")
    if isinstance(arts, list):
        names = [a.get("name") for a in arts if isinstance(a, dict) and a.get("name")]
    elif isinstance(arts, str):
        names = [arts]
    if not names and isinstance(x.get("artist"), str):
        names = [x["artist"]]
    return ", ".join(names) or None


def _secs(x: dict):
    if x.get("duration_seconds") is not None:
        return x["duration_seconds"]
    d = x.get("duration")
    if isinstance(d, (int, float)):
        return int(d)
    if isinstance(d, str) and re.fullmatch(r"(\d+:){1,2}\d+", d):
        n = 0
        for part in d.split(":"):
            n = n * 60 + int(part)
        return n
    return None


def _artist_list(x: dict):
    arts = x.get("artists")
    if not isinstance(arts, list):
        return []
    return [{"name": a["name"], "id": a.get("id")} for a in arts if isinstance(a, dict) and a.get("name")]


def _track(x: dict, thumb=None, artist=None, album=None, album_id=None):
    vid = x.get("videoId")
    if not vid or x.get("isAvailable") is False:
        return None
    alb = x.get("album")
    aid = alb.get("id") if isinstance(alb, dict) else None
    alb = alb.get("name") if isinstance(alb, dict) else (alb or album)
    t = {
        "id": vid,
        "title": x.get("title"),
        "artist": _artist_names(x) or artist,
        "artists": _artist_list(x),
        "album": alb,
        "album_id": aid or album_id,
        "duration": _secs(x),
        "thumbnail": _best_thumb(x.get("thumbnails")) or thumb,
        "url": f"{MUSIC_URL}/watch?v={vid}",
    }
    if x.get("isExplicit"):
        t["explicit"] = True        # shown as the "E" badge in the app
    return t


def _audio_only(items):
    keep = [x for x in items if x.get("videoType") not in _BAD_VIDEO_TYPES]
    return keep or items


def _entity(x: dict, kind: str):
    if kind == "artist":
        id_, title, sub = x.get("browseId"), x.get("artist") or x.get("title"), "Artist"
    elif kind == "album":
        id_, title = x.get("browseId"), x.get("title")
        sub = " · ".join(str(p) for p in (x.get("type"), _artist_names(x), x.get("year")) if p)
    else:
        id_, title = x.get("browseId") or x.get("playlistId"), x.get("title")
        author = x.get("author")
        author = author if isinstance(author, str) else None
        sub = author or (str(x["itemCount"]) + " songs" if x.get("itemCount") else None)
        if id_ and id_.startswith("VL"):
            id_ = id_[2:]
    if not id_ or not title:
        return None
    return {"kind": kind, "id": id_, "title": title, "artist": sub, "thumbnail": _best_thumb(x.get("thumbnails"))}


def _search_songs_ytdlp(q: str, limit: int):
    info = extract(f"ytsearch{limit}:{q}", base_opts(extract_flat=True))
    return [track_summary(e) for e in (info.get("entries") or []) if e and e.get("id")][:limit]


@app.get("/search", dependencies=[Depends(require_key)])
@ttl_cache(ttl=600, maxsize=500)
def search(
    q: str = Query(..., min_length=1),
    type: str = Query("songs", description="songs, albums, artists or playlists"),
    limit: int = Query(20, ge=1, le=50),
):
    """Search YouTube Music for songs, albums, artists or playlists."""
    if type not in SEARCH_TYPES:
        raise HTTPException(400, f"type must be one of {sorted(SEARCH_TYPES)}")
    if YTMusic is None:
        if type != "songs":
            raise HTTPException(501, "Album/artist/playlist search needs ytmusicapi: pip install ytmusicapi")
        return {"query": q, "type": type, "results": _search_songs_ytdlp(q, limit)}
    raw = ytm_call("search", q, filter=type, limit=limit, ignore_spelling=True)
    if type == "songs":
        results = [t for t in map(_track, _audio_only(raw)) if t]
    else:
        kind = {"albums": "album", "artists": "artist", "playlists": "playlist"}[type]
        results = [e for e in (_entity(x, kind) for x in raw) if e]
    return {"query": q, "type": type, "results": results}


@app.get("/album/{browse_id}", dependencies=[Depends(require_key)])
@ttl_cache(ttl=1800, maxsize=500)
def album(browse_id: str):
    check_id(browse_id)
    a = ytm_call("get_album", browse_id)
    thumb = _best_thumb(a.get("thumbnails"))
    artist = _artist_names(a)
    arts = _artist_list(a)
    tracks = []
    for x in _audio_only(a.get("tracks") or []):
        t = _track(x, thumb=thumb, artist=artist, album=a.get("title"), album_id=browse_id)
        if t:
            t["thumbnail"] = thumb or t["thumbnail"]
            t["artists"] = t["artists"] or arts
            t["album_id"] = browse_id
            tracks.append(t)

    more = []
    if arts and arts[0].get("id"):
        def _fetch_more():
            try:
                ar = ytm().get_artist(arts[0]["id"])
                results = []
                for key in ("albums", "singles"):
                    for x in (ar.get(key) or {}).get("results") or []:
                        e = _entity(x, "album")
                        if e and e["id"] != browse_id:
                            results.append(e)
                return results
            except Exception:
                return []

        with ThreadPoolExecutor(max_workers=1) as executor:
            more = executor.submit(_fetch_more).result(timeout=3.0) or []

    return {
        "kind": "album", "id": browse_id, "title": a.get("title"), "type": a.get("type"), "year": a.get("year"),
        "subtitle": " · ".join(str(p) for p in (artist, a.get("year"), a.get("type")) if p),
        "artists": arts, "thumbnail": thumb, "tracks": tracks, "more": more[:16],
    }


@app.get("/artist/{channel_id}", dependencies=[Depends(require_key)])
@ttl_cache(ttl=1800, maxsize=500)
def artist(channel_id: str):
    check_id(channel_id)
    a = ytm_call("get_artist", channel_id)
    block = a.get("songs") or {}
    raw = block.get("results") or []
    bid = block.get("browseId")
    if bid:
        try:
            full = ytm().get_playlist(bid[2:] if bid.startswith("VL") else bid, limit=50)
            if full.get("tracks"):
                raw = full["tracks"]
        except Exception:
            pass

    def ents(key):
        return [e for e in (_entity(x, "album") for x in ((a.get(key) or {}).get("results") or [])) if e]

    return {
        "kind": "artist",
        "id": channel_id,
        "name": a.get("name"),
        "subtitle": (str(a["subscribers"]) + " subscribers") if a.get("subscribers") else "Artist",
        "thumbnail": _best_thumb(a.get("thumbnails")),
        "description": a.get("description"),
        "views": a.get("views"),
        "songs": [t for t in map(_track, _audio_only(raw)) if t],
        "albums": ents("albums"),
        "singles": ents("singles"),
    }


@app.get("/track/{video_id}", dependencies=[Depends(require_key)])
def track(video_id: str):
    """Full metadata for a track."""
    check_video_id(video_id)
    info = extract(f"https://www.youtube.com/watch?v={video_id}", base_opts())
    return {
        **track_summary(info),
        "release_year": info.get("release_year"),
        "genre": info.get("genre"),
        "view_count": info.get("view_count"),
        "like_count": info.get("like_count"),
        "description": info.get("description"),
    }


AUDIO_FORMAT = "bestaudio[protocol^=http][protocol!*=m3u8]/bestaudio/best/ba*/b"
_audio_cache: dict = {}
CHUNK = 10 * 1024 * 1024  # googlevideo max ranged chunk
_FMT_RE = re.compile(r"^[\w\-\.\+]{1,60}$")
_CLIENT_RE = re.compile(r"^[\w,]{1,60}$")


def _akey(video_id: str, client: Optional[str] = None, fmt: Optional[str] = None) -> tuple:
    return (video_id, client or "", fmt or "")


def _check_src(client: Optional[str], fmt: Optional[str]):
    if client and not _CLIENT_RE.match(client):
        raise HTTPException(400, "Invalid client")
    if fmt and not _FMT_RE.match(fmt):
        raise HTTPException(400, "Invalid fmt")


_AUDIO_TTL = 1500

AUDIO_CLIENTS = [c for c in os.getenv(
    "YTDLP_AUDIO_CLIENTS", "tv;android_vr;mweb;web_safari;web,mweb,tv"
).split(";") if c]


def _upstream_opener():
    proxy = os.getenv("YTDLP_PROXY")
    return build_opener(ProxyHandler({"http": proxy, "https": proxy})) if proxy else build_opener()


def _probe(url: str, headers: dict) -> bool:
    h = {k: v for k, v in headers.items() if k.lower() not in ("accept-encoding", "range", "host")}
    h.setdefault("User-Agent", "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36")
    h["Range"] = f"bytes=0-{CHUNK - 1}"
    try:
        with _upstream_opener().open(UrlRequest(url, headers=h), timeout=12) as r:
            r.read(2)
        return True
    except Exception:
        return False


_good_client = os.getenv("YTDLP_FAST_CLIENT") or None  # last client that produced a playable URL


def _fast_resolve(url: str, clients: str):
    """Try ONLY the last-known-good client. Returns a playable, non-HLS info dict or None."""
    opts = base_opts(format=AUDIO_FORMAT, ignoreerrors=False)
    if clients != "default":
        opts["extractor_args"]["youtube"]["player_client"] = clients.split(",")
        if clients.split(",")[0] == "android_vr":
            opts.pop("cookiefile", None)
    try:
        with yt_dlp.YoutubeDL(opts) as ydl:
            info = ydl.extract_info(url, download=False)
    except yt_dlp.utils.DownloadError:
        return None
    if not info or not info.get("url"):
        return None
    if "m3u8" in (info.get("protocol") or "") or ".m3u8" in info["url"]:
        return None
    return info if _probe(info["url"], info.get("http_headers") or {}) else None


# ---- Direct InnerTube resolver (token-free client, tried BEFORE yt-dlp) ---------------
# One POST to /youtubei/v1/player instead of a full yt-dlp extraction. If it fails
# (client blocked, format changed, URL capped) we fall straight through to yt-dlp.
# Disable with INNERTUBE_DIRECT=0. Client identity is overridable via env because
# YouTube re-pins these every few months.
import json as _json

_IT_BASE = os.getenv("INNERTUBE_BASE", "https://www.youtube.com/youtubei/v1")
_IT_CLIENT_ID = os.getenv("INNERTUBE_CLIENT_ID", "101")
_IT_UA = os.getenv(
    "INNERTUBE_UA",
    "com.google.ios.youtube/0.1 (RealityDevice14,1; U; CPU iOS 17_0 like Mac OS X)",
)
_IT_CLIENT = {
    "clientName": os.getenv("INNERTUBE_CLIENT_NAME", "VISIONOS"),
    "clientVersion": os.getenv("INNERTUBE_CLIENT_VERSION", "0.1"),
    "deviceMake": "Apple",
    "deviceModel": "RealityDevice14,1",
    "osName": "visionOS",
    "osVersion": "1.3.21O771",
    "hl": "en",
    "gl": "IN",
}
_IT_PREFER = os.getenv("INNERTUBE_PREFER", "")  # "mp4" or "webm" to bias the format pick
_it_state = {"visitor": None, "vt": 0.0, "fails": 0, "off_until": 0.0}


def _it_post(path: str, body: dict, headers: dict, timeout: int = 6) -> dict:
    req = UrlRequest(
        f"{_IT_BASE}/{path}?prettyPrint=false",
        data=_json.dumps(body).encode(),
        headers={"Content-Type": "application/json", **headers},
        method="POST",
    )
    with _upstream_opener().open(req, timeout=timeout) as r:
        return _json.loads(r.read().decode("utf-8", "replace"))


def _it_visitor() -> Optional[str]:
    env = os.getenv("YTDLP_VISITOR_DATA")
    if env:
        return env
    if _it_state["visitor"] and time.time() - _it_state["vt"] < 6 * 3600:
        return _it_state["visitor"]
    try:
        data = _it_post(
            "visitor_id",
            {"context": {"client": {"clientName": "WEB", "clientVersion": "2.20260101.00.00", "hl": "en", "gl": "IN"}}},
            {"User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36"},
        )
        vd = (data.get("responseContext") or {}).get("visitorData")
    except Exception:
        vd = None
    if vd:
        _it_state["visitor"], _it_state["vt"] = vd, time.time()
    return vd


def _it_pick(fmts):
    best, best_key = None, None
    for f in fmts or []:
        mt = f.get("mimeType") or ""
        if not mt.startswith("audio/") or not f.get("url"):
            continue
        at = f.get("audioTrack")
        if at and not at.get("audioIsDefault", True):
            continue  # skip dubbed / alternate-language tracks
        key = (1 if (_IT_PREFER and _IT_PREFER in mt) else 0, f.get("bitrate") or 0)
        if best_key is None or key > best_key:
            best, best_key = f, key
    return best


def _it_probe(url: str, size: int) -> bool:
    # Probe PAST the ~1 MB cold-start allowance: a token-less client answers 206 at
    # offset 0 and only 403s further in, so an offset-0 probe can't catch it.
    off = 2_000_000 if size > 2_200_000 else 0
    h = {"User-Agent": _IT_UA, "Range": f"bytes={off}-{off + 1}"}
    try:
        with _upstream_opener().open(UrlRequest(url, headers=h), timeout=6) as r:
            r.read(2)
        return True
    except Exception:
        return False


def _innertube_resolve(video_id: str) -> Optional[dict]:
    """Direct InnerTube /player call. Returns an _audio_cache-shaped entry or None."""
    if os.getenv("INNERTUBE_DIRECT", "1") == "0" or time.time() < _it_state["off_until"]:
        return None
    t0 = time.time()
    try:
        vd = _it_visitor()
        client = dict(_IT_CLIENT)
        headers = {
            "User-Agent": _IT_UA,
            "X-YouTube-Client-Name": _IT_CLIENT_ID,
            "X-YouTube-Client-Version": client["clientVersion"],
            "Origin": "https://www.youtube.com",
        }
        if vd:
            client["visitorData"] = vd
            headers["X-Goog-Visitor-Id"] = vd
        data = _it_post(
            "player",
            {"context": {"client": client}, "videoId": video_id, "contentCheckOk": True, "racyCheckOk": True},
            headers,
        )
        status = (data.get("playabilityStatus") or {}).get("status")
        if status != "OK":
            raise RuntimeError(f"playability={status}")
        f = _it_pick((data.get("streamingData") or {}).get("adaptiveFormats"))
        if not f:
            raise RuntimeError("no direct audio url")
        size = int(f.get("contentLength") or 0)
        if not _it_probe(f["url"], size):
            raise RuntimeError("stream probe failed")
    except Exception as e:
        _it_state["fails"] += 1
        if _it_state["fails"] >= 3:  # circuit breaker: stop wasting latency while it's broken
            _it_state["fails"], _it_state["off_until"] = 0, time.time() + 600
            print("[resolve] innertube direct disabled for 10 min after 3 failures", flush=True)
        print(f"[resolve] {video_id}: innertube direct failed ({e}); falling back to yt-dlp", flush=True)
        return None
    _it_state["fails"] = 0
    vdet = data.get("videoDetails") or {}
    mt = f.get("mimeType") or ""
    codec = re.search(r'codecs="([^"]+)"', mt)
    info = {
        "id": video_id,
        "title": vdet.get("title"),
        "channel": vdet.get("author"),
        "duration": int(vdet["lengthSeconds"]) if str(vdet.get("lengthSeconds") or "").isdigit() else None,
        "thumbnails": (vdet.get("thumbnail") or {}).get("thumbnails"),
    }
    print(f"[resolve] {video_id}: innertube direct ok itag={f.get('itag')} in {time.time() - t0:.2f}s", flush=True)
    return {
        "t": time.time(),
        "url": f["url"],
        "headers": {"User-Agent": _IT_UA},
        "protocol": "https",
        "meta": {
            **track_summary(info),
            "ext": "m4a" if "mp4" in mt else "webm",
            "abr": round((f.get("averageBitrate") or f.get("bitrate") or 0) / 1000) or None,
            "acodec": codec.group(1) if codec else None,
            "vcodec": "none",
            "format_id": str(f.get("itag")),
            "protocol": "https",
            "has_video": False,
            "filesize": size or None,
        },
    }


def _resolve_audio(video_id: str, force: bool = False, client: Optional[str] = None, fmt: Optional[str] = None) -> dict:
    key = _akey(video_id, client, fmt)
    pinned = bool(client or fmt)
    hit = _audio_cache.get(key)
    if hit and not force and time.time() - hit["t"] < _AUDIO_TTL:
        return hit
    if not pinned and not force:
        direct = _innertube_resolve(video_id)
        if direct:
            _audio_cache[key] = direct
            if len(_audio_cache) > 200:
                _audio_cache.pop(next(iter(_audio_cache)))
            return direct
    url = f"https://www.youtube.com/watch?v={video_id}"
    audio_only = playable_mixed = any_info = None
    last, started = None, time.time()
    simple = not pinned
    global _good_client
    used = None
    fast = _fast_resolve(url, _good_client) if (simple and _good_client and not force) else None
    if fast:
        if fast.get("vcodec") in (None, "none"):
            audio_only = fast
        else:
            playable_mixed = fast
        any_info, used = fast, _good_client
        print(f"[resolve] {video_id}: fast path client={_good_client}", flush=True)
    elif simple:
        # Default extraction can succeed yet hand back URLs that 403 (e.g. web_embedded
        # needs a PO token). So probe it, and fall through to other clients if it's dead.
        try:
            any_info = extract(url, base_opts(format=AUDIO_FORMAT))
        except HTTPException as e:
            last = str(e.detail)
            any_info = None
        if any_info and any_info.get("url"):
            if _probe(any_info["url"], any_info.get("http_headers") or {}):
                if any_info.get("vcodec") in (None, "none"):
                    audio_only = any_info
                    used = "default"
                else:
                    playable_mixed = any_info
            print(f"[resolve] {video_id}: default clients probe_ok={bool(audio_only or playable_mixed)}", flush=True)
    for clients in ([client] if client else ([] if (audio_only or fast) else AUDIO_CLIENTS)):
        if time.time() - started > 60:
            break
        opts = base_opts(format=fmt or AUDIO_FORMAT, ignoreerrors=False)
        opts["extractor_args"]["youtube"]["player_client"] = clients.split(",")
        if clients.split(",")[0] == "android_vr":
            opts.pop("cookiefile", None)
        try:
            with yt_dlp.YoutubeDL(opts) as ydl:
                info = ydl.extract_info(url, download=False)
        except yt_dlp.utils.DownloadError as e:
            last = re.sub(r"\x1b\[[0-9;]*m", "", str(e))
            continue
        if not info or not info.get("url"):
            continue
        any_info = any_info or info
        is_audio = info.get("vcodec") in (None, "none")
        ok = True if pinned else _probe(info["url"], info.get("http_headers"))
        print(f"[resolve] {video_id}: client={clients} format={info.get('format_id')} audio_only={is_audio} playable={ok}", flush=True)
        if pinned:
            audio_only = info
            break
        if ok and is_audio:
            audio_only = info
            used = clients
            break
        if ok:
            # Prefer a plain progressive mp4 (e.g. itag 18) over a heavy HLS video playlist.
            hls = "m3u8" in (info.get("protocol") or "") or ".m3u8" in info["url"]
            prev_hls = bool(playable_mixed) and ("m3u8" in (playable_mixed.get("protocol") or "") or ".m3u8" in playable_mixed["url"])
            if not playable_mixed or (prev_hls and not hls):
                playable_mixed = info
            if not hls:
                used = clients
                break
    if simple and used:
        _good_client = used
    info = audio_only or playable_mixed or (any_info if pinned else None)
    if info is None:
        raise HTTPException(502, f"yt-dlp error: {last or 'no playable audio found'}")
    entry = {
        "t": time.time(),
        "url": info.get("url"),
        "headers": info.get("http_headers") or {},
        "protocol": info.get("protocol") or "",
        "meta": {
            **track_summary(info),
            "ext": info.get("ext"),
            "abr": info.get("abr"),
            "acodec": info.get("acodec"),
            "vcodec": info.get("vcodec"),
            "format_id": info.get("format_id"),
            "protocol": info.get("protocol"),
            "has_video": (info.get("vcodec") not in (None, "none")),
            "filesize": info.get("filesize") or info.get("filesize_approx"),
        },
    }
    _audio_cache[key] = entry
    if len(_audio_cache) > 200:
        _audio_cache.pop(next(iter(_audio_cache)))
    return entry


def _public_base(request: Request) -> str:
    env = os.getenv("PUBLIC_URL") or os.getenv("RENDER_EXTERNAL_URL")
    if env:
        return env.rstrip("/")
    h = request.headers
    scheme = (h.get("x-forwarded-proto") or request.url.scheme).split(",")[0].strip()
    host = (h.get("x-forwarded-host") or h.get("host") or request.url.netloc).split(",")[0].strip()
    return f"{scheme}://{host}"


def _audio_link(request: Request, video_id: str, client: Optional[str] = None, fmt: Optional[str] = None) -> str:
    q = {}
    if client:
        q["client"] = client
    if fmt:
        q["fmt"] = fmt
    if API_KEY:
        q["key"] = API_KEY
    return f"{_public_base(request)}/audio/{video_id}" + (f"?{urlencode(q, quote_via=quote)}" if q else "")


@app.get("/stream/{video_id}", dependencies=[Depends(require_key)])
def stream(
    video_id: str,
    request: Request,
    client: Optional[str] = Query(default=None, description="pin a player client, see /sources"),
    fmt: Optional[str] = Query(default=None, description="pin a format_id, see /sources"),
):
    """Playable audio URL. Proxied through this server so it works from any client IP."""
    check_video_id(video_id)
    _check_src(client, fmt)
    e = _resolve_audio(video_id, client=client, fmt=fmt)
    if not e["url"]:
        raise HTTPException(502, "No playable audio stream found for this track")
    if os.getenv("DIRECT_STREAM") == "1":
        audio_url = e["url"]
    else:
        audio_url = _audio_link(request, video_id, client, fmt)
    return {**e["meta"], "audio_url": audio_url, "sources_url": f"{_public_base(request)}/sources/{video_id}"}


def _list_client_formats(video_id: str, clients: str) -> dict:
    opts = base_opts(ignore_no_formats_error=True)
    opts["extractor_args"]["youtube"]["player_client"] = clients.split(",")
    if clients.split(",")[0] == "android_vr":
        opts.pop("cookiefile", None)
    try:
        with yt_dlp.YoutubeDL(opts) as ydl:
            info = ydl.extract_info(f"https://www.youtube.com/watch?v={video_id}", download=False) or {}
    except yt_dlp.utils.DownloadError as e:
        return {"client": clients, "error": re.sub(r"\x1b\[[0-9;]*m", "", str(e)).strip(), "formats": []}
    return {"client": clients, "info": info, "formats": info.get("formats") or []}


@app.get("/sources/{video_id}", dependencies=[Depends(require_key)])
def sources(
    video_id: str,
    request: Request,
    probe: bool = Query(False, description="test each source against YouTube and report playable true/false (slower)"),
    audio_only: bool = Query(False, description="hide sources that contain video"),
    direct: bool = Query(False, description="also include the raw googlevideo URL (IP-locked to this server)"),
):
    """Every audio/video source YouTube exposes for this id, per player client."""
    check_video_id(video_id)
    started = time.time()
    with ThreadPoolExecutor(max_workers=min(len(AUDIO_CLIENTS), 6) or 1) as ex:
        results = list(ex.map(lambda c: _list_client_formats(video_id, c), AUDIO_CLIENTS))

    out, errors, meta, seen = [], {}, None, set()
    for r in results:
        if r.get("error"):
            errors[r["client"]] = r["error"]
        if r.get("info") and not meta:
            meta = track_summary(r["info"])
        for f in r["formats"]:
            url = f.get("url")
            proto = f.get("protocol") or ""
            vc, ac = f.get("vcodec") or "none", f.get("acodec") or "none"
            if not url or (vc == "none" and ac == "none"):
                continue
            kind = "audio" if vc == "none" else ("video" if ac == "none" else "muxed")
            if audio_only and kind != "audio":
                continue
            sid = f"{r['client']}:{f.get('format_id')}"
            if sid in seen:
                continue
            seen.add(sid)
            item = {
                "id": sid,
                "client": r["client"],
                "format_id": f.get("format_id"),
                "kind": kind,
                "ext": f.get("ext"),
                "acodec": None if ac == "none" else ac,
                "vcodec": None if vc == "none" else vc,
                "abr": f.get("abr"),
                "tbr": f.get("tbr"),
                "asr": f.get("asr"),
                "height": f.get("height"),
                "quality": f.get("format_note"),
                "language": f.get("language"),
                "protocol": proto,
                "filesize": f.get("filesize") or f.get("filesize_approx"),
                "stream_url": _audio_link(request, video_id, r["client"], f.get("format_id")),
                "_url": url,
                "_headers": f.get("http_headers"),
            }
            if direct:
                item["direct_url"] = url
            out.append(item)

    if probe:
        def run(it):
            if "m3u8" in it["protocol"]:
                it["playable"] = None
            else:
                it["playable"] = _probe(it["_url"], it["_headers"])
        with ThreadPoolExecutor(max_workers=8) as ex:
            list(ex.map(run, out))
    for it in out:
        it.pop("_url", None)
        it.pop("_headers", None)

    rank = {"audio": 0, "muxed": 1, "video": 2}
    out.sort(key=lambda i: (i.get("playable") is False, rank[i["kind"]], -(i["abr"] or i["tbr"] or 0)))
    return {
        "video_id": video_id,
        **(meta or {}),
        "auto_stream_url": _audio_link(request, video_id),
        "count": len(out),
        "probed": probe,
        "elapsed_s": round(time.time() - started, 1),
        "sources": out,
        "client_errors": errors,
    }


_PASS_HEADERS = ("content-type", "content-length", "content-range", "accept-ranges")


@app.get("/audio/{video_id}", include_in_schema=False)
def audio(
    video_id: str,
    request: Request,
    key: Optional[str] = Query(default=None),
    client: Optional[str] = Query(default=None),
    fmt: Optional[str] = Query(default=None),
):
    """Byte-range proxy for the audio stream with enlarged buffer size."""
    check_video_id(video_id)
    _check_src(client, fmt)
    if API_KEY and key != API_KEY and request.headers.get("x-api-key") != API_KEY:
        raise HTTPException(401, "Invalid or missing key")
    rng = request.headers.get("range")
    m = re.match(r"bytes=(\d*)-(\d*)", rng or "")
    start = int(m.group(1)) if m and m.group(1) else 0
    end_req = int(m.group(2)) if m and m.group(2) else None
    up, last_err, chunked = None, "unknown", False
    simple = not (client or fmt)
    for attempt in ((0, 1) if simple else (0, 1, 2)):
        e = _resolve_audio(video_id, force=(attempt == 1), client=client, fmt=fmt)
        if not e["url"]:
            raise HTTPException(502, "No playable audio stream found for this track")
        if "m3u8" in e["protocol"] or ".m3u8" in e["url"]:
            return RedirectResponse(e["url"])
        h = {k: v for k, v in e["headers"].items() if k.lower() not in ("accept-encoding", "range", "host")}
        h.setdefault("User-Agent", "Mozilla/5.0")
        chunked = not simple and attempt != 2 and "googlevideo.com" in e["url"]
        if chunked:
            stop = start + CHUNK - 1 if end_req is None else min(end_req, start + CHUNK - 1)
            h["Range"] = f"bytes={start}-{stop}"
        elif rng and (simple or attempt != 2):
            h["Range"] = rng
        try:
            up = _upstream_opener().open(UrlRequest(e["url"], headers=h), timeout=25)
            break
        except HTTPError as err:
            if err.code == 416:
                return Response(status_code=416, headers={"Content-Range": err.headers.get("Content-Range", "")})
            last_err = f"HTTP {err.code} from YouTube (chunked={chunked}, format={e['meta'].get('format_id')}, video={e['meta'].get('has_video')})"
            print(f"[audio] {video_id}: {last_err}", flush=True)
            if attempt == 0 and err.code in (403, 404, 410):
                _audio_cache.pop(_akey(video_id, client, fmt), None)
        except Exception as err:
            last_err = f"{type(err).__name__}: {err}"
            print(f"[audio] {video_id}: {last_err}", flush=True)
    if up is None:
        raise HTTPException(502, f"Upstream audio error: {last_err}")

    ctype = up.headers.get_content_type()
    cr = re.match(r"bytes (\d+)-(\d+)/(\d+)", up.headers.get("Content-Range", ""))
    if chunked and up.status == 206 and cr:
        total, first_end = int(cr.group(3)), int(cr.group(2))
        last = total - 1 if end_req is None else min(end_req, total - 1)
        headers = {"Accept-Ranges": "bytes", "Cache-Control": "no-store", "Content-Length": str(last - start + 1)}
        if rng:
            headers["Content-Range"] = f"bytes {start}-{last}/{total}"

        def chunk_body():
            cur, nxt = up, first_end + 1
            try:
                while True:
                    while True:
                        data = cur.read(STREAM_CHUNK_SIZE)
                        if not data:
                            break
                        yield data
                    cur.close()
                    cur = None
                    if nxt > last:
                        return
                    h2 = {**h, "Range": f"bytes={nxt}-{min(nxt + CHUNK - 1, last)}"}
                    try:
                        cur = _upstream_opener().open(UrlRequest(e["url"], headers=h2), timeout=25)
                    except Exception as err:
                        print(f"[audio] {video_id}: chunk at {nxt} failed: {err}", flush=True)
                        return
                    nxt = min(nxt + CHUNK - 1, last) + 1
            finally:
                if cur is not None:
                    cur.close()

        return StreamingResponse(chunk_body(), status_code=206 if rng else 200, headers=headers, media_type=ctype)

    headers = {k: up.headers[k] for k in _PASS_HEADERS if up.headers.get(k)}
    headers.setdefault("Accept-Ranges", "bytes")
    headers["Cache-Control"] = "no-store"

    def body():
        try:
            while True:
                chunk = up.read(STREAM_CHUNK_SIZE)
                if not chunk:
                    break
                yield chunk
        finally:
            up.close()

    return StreamingResponse(body(), status_code=up.status, headers=headers,
                             media_type=headers.pop("content-type", None) or ctype)


def _cleanup(path: str):
    shutil.rmtree(path, ignore_errors=True)


@app.get("/download/{video_id}", dependencies=[Depends(require_key)])
def download(
    video_id: str,
    fmt: str = Query("mp3", description="mp3, m4a, opus, flac, wav, or best (no conversion)"),
    quality: str = Query("192", description="Bitrate in kbps for lossy formats"),
):
    """Download audio and return it as a file."""
    check_video_id(video_id)
    if fmt not in ALLOWED_FORMATS:
        raise HTTPException(400, f"fmt must be one of {sorted(ALLOWED_FORMATS)}")
    if not quality.isdigit():
        raise HTTPException(400, "quality must be a number")

    tmp = tempfile.mkdtemp(prefix="ytm_")
    opts = base_opts(
        skip_download=False,
        format="bestaudio[protocol!*=m3u8]/bestaudio/best/ba*/b*",
        outtmpl=os.path.join(tmp, "%(artist,uploader)s - %(title)s.%(ext)s"),
        restrictfilenames=True,
        writethumbnail=False,
    )
    if fmt != "best" and not shutil.which("ffmpeg"):
        fmt = "best"
    if fmt != "best":
        opts["postprocessors"] = [
            {"key": "FFmpegExtractAudio", "preferredcodec": fmt, "preferredquality": quality},
            {"key": "FFmpegMetadata", "add_metadata": True},
        ]

    try:
        extract(f"https://www.youtube.com/watch?v={video_id}", opts, download=True)
        files = os.listdir(tmp)
        if not files:
            raise HTTPException(500, "Download produced no file")
        path = os.path.join(tmp, files[0])
        return FileResponse(
            path,
            filename=files[0],
            background=BackgroundTask(_cleanup, tmp),
        )
    except Exception:
        _cleanup(tmp)
        raise


@app.get("/playlist/{playlist_id}", dependencies=[Depends(require_key)])
@ttl_cache(ttl=1800, maxsize=300)
def playlist(playlist_id: str, limit: int = Query(100, ge=1, le=500)):
    """Tracks in a YouTube Music playlist or album playlist."""
    if not PLAYLIST_ID_RE.match(playlist_id):
        raise HTTPException(400, "Invalid playlist id")
    if YTMusic is not None:
        try:
            p = ytm().get_playlist(playlist_id, limit=limit)
            tracks = [t for t in map(_track, _audio_only(p.get("tracks") or [])) if t]
            if tracks:
                author = p.get("author")
                author = author.get("name") if isinstance(author, dict) else author
                sub = " · ".join(str(x) for x in (author, f"{len(tracks)} songs") if x)
                return {
                    "kind": "playlist", "id": playlist_id, "title": p.get("title"), "subtitle": sub,
                    "thumbnail": _best_thumb(p.get("thumbnails")), "track_count": len(tracks), "tracks": tracks,
                }
        except Exception:
            pass
    info = extract(
        f"https://www.youtube.com/playlist?list={playlist_id}",
        base_opts(extract_flat=True, noplaylist=False, playlistend=limit),
    )
    tracks = [track_summary(e) for e in info.get("entries", []) if e]
    return {
        "kind": "playlist", "id": info.get("id"), "title": info.get("title"),
        "subtitle": f"{len(tracks)} songs", "thumbnail": None,
        "track_count": len(tracks), "tracks": tracks,
    }


# ---- Import a YouTube playlist by link ------------------------------------------
YT_LIST_RE = re.compile(r"[?&]list=([\w-]+)")
_BLOCKED_LISTS = {"WL": "Watch Later", "LL": "Liked videos", "LM": "Liked music"}


@app.get("/import", dependencies=[Depends(require_key)])
def import_playlist(
    url: str = Query(..., min_length=3, description="YouTube / YouTube Music playlist link (or id)"),
    limit: int = Query(1000, ge=1, le=5000),
):
    """Fetch EVERY track of a public/unlisted playlist so the client can copy it into its library."""
    url = url.strip()
    m = YT_LIST_RE.search(url)
    pid = m.group(1) if m else (url if PLAYLIST_ID_RE.match(url) else None)
    if not pid:
        raise HTTPException(400, "That doesn't look like a YouTube playlist link.")
    if pid in _BLOCKED_LISTS:
        raise HTTPException(403, f"{_BLOCKED_LISTS[pid]} is private and can't be imported. Copy those songs into a public playlist first.")
    private_msg = ("Couldn't read that playlist. It may be private or deleted. "
                   "Set it to Public or Unlisted on YouTube and try again.")

    title = thumbnail = None
    tracks: list = []
    if YTMusic is not None:
        try:
            p = ytm().get_playlist(pid, limit=limit)
            tracks = [t for t in map(_track, p.get("tracks") or []) if t]
            title, thumbnail = p.get("title"), _best_thumb(p.get("thumbnails"))
        except Exception:
            tracks = []
    if not tracks:
        try:
            info = extract(
                f"https://www.youtube.com/playlist?list={pid}",
                base_opts(extract_flat=True, noplaylist=False, playlistend=limit),
            )
        except HTTPException:
            raise HTTPException(404, private_msg)
        entries = [
            e for e in (info.get("entries") or [])
            if e and e.get("id") and not str(e.get("title") or "").startswith(("[Private", "[Deleted"))
        ]
        tracks = [track_summary(e) for e in entries]
        title = title or info.get("title")
    seen, uniq = set(), []
    for t in tracks:
        if t["id"] not in seen:
            seen.add(t["id"])
            uniq.append(t)
    if not uniq:
        raise HTTPException(404, private_msg)
    return {
        "kind": "playlist", "id": pid, "title": title or "Imported playlist",
        "thumbnail": thumbnail, "track_count": len(uniq), "tracks": uniq,
    }


# ---- Lyrics (Unison + lrc.red) ----------------------------------------------------
import json
from urllib.parse import urlencode
from xml.etree import ElementTree as ET

UNISON_URL = os.getenv("UNISON_URL", "https://unison.boidu.dev").rstrip("/")
LRCRED_URL = os.getenv("LRCRED_URL", "https://lrc.red").rstrip("/")
ISRC_RE = re.compile(r"^[A-Z]{2}[A-Z0-9]{3}\d{7}$")
_LYR_UA = {"User-Agent": "Mozilla/5.0 (compatible; Thirai/1.0)"}
_LRC_LINE = re.compile(r"^((?:\[\d+:\d+(?:[.:]\d+)?\])+)(.*)$")
_LRC_TIME = re.compile(r"\[(\d+):(\d+(?:[.:]\d+)?)\]")
_LRC_WORD = re.compile(r"<(\d+):(\d+(?:\.\d+)?)>")
_TTML_SKIP_ROLES = ("x-translation", "x-roman")


def _http_text(url: str, timeout: int = 8) -> Optional[str]:
    try:
        with urlopen(UrlRequest(url, headers=_LYR_UA), timeout=timeout) as r:
            return r.read().decode("utf-8-sig", "replace")
    except Exception:
        return None


def _clock(s) -> Optional[float]:
    if not s:
        return None
    s = s.strip()
    try:
        if s.endswith("ms"):
            return float(s[:-2]) / 1000
        if s.endswith("s"):
            return float(s[:-1])
        sec = 0.0
        for part in s.split(":"):
            sec = sec * 60 + float(part)
        return sec
    except ValueError:
        return None


def _local(tag) -> str:
    return tag.rsplit("}", 1)[-1] if isinstance(tag, str) else ""


def _collect_words(el, words: list):
    for sp in el:
        tail = sp.tail
        if tail:
            tail = " " if tail.isspace() else tail
        if _local(sp.tag) == "span":
            role = next((v for k, v in sp.attrib.items() if k.endswith("role")), "")
            if role not in _TTML_SKIP_ROLES:
                b = _clock(sp.get("begin"))
                if b is not None:
                    words.append({"t": b, "e": _clock(sp.get("end")), "w": "".join(sp.itertext())})
                elif len(sp):
                    _collect_words(sp, words)
                elif sp.text and words:
                    words[-1]["w"] += sp.text
        if tail and words:
            words[-1]["w"] += tail


def parse_ttml(text: str) -> list:
    try:
        root = ET.fromstring(text.lstrip("\ufeff").encode("utf-8"))
    except ET.ParseError:
        return []
    lines = []
    for p in root.iter():
        if _local(p.tag) != "p":
            continue
        words: list = []
        _collect_words(p, words)
        start, end = _clock(p.get("begin")), _clock(p.get("end"))
        if words:
            words[-1]["w"] = words[-1]["w"].rstrip()
            text_ = "".join(w["w"] for w in words).strip()
            start = start if start is not None else words[0]["t"]
            end = end if end is not None else words[-1]["e"]
        else:
            text_ = " ".join("".join(p.itertext()).split())
        if start is None:
            continue
        line = {"t": round(start, 3), "e": round(end, 3) if end is not None else None, "text": text_}
        if words:
            line["words"] = [
                {"t": round(w["t"], 3), "w": w["w"]} for w in words if w["w"].strip()
            ]
        lines.append(line)
    lines.sort(key=lambda l: l["t"])
    return lines


def _lrc_secs(mm: str, ss: str) -> float:
    return int(mm) * 60 + float(ss.replace(":", "."))


def parse_lrc(text: str) -> list:
    lines, offset = [], 0.0
    for raw in text.lstrip("\ufeff").splitlines():
        raw = raw.strip()
        m = re.match(r"^\[offset:\s*(-?\d+)\]", raw, re.I)
        if m:
            offset = int(m.group(1)) / 1000
            continue
        m = _LRC_LINE.match(raw)
        if not m:
            continue
        times = [_lrc_secs(a, b) for a, b in _LRC_TIME.findall(m.group(1))]
        rest = m.group(2)
        lead, words = "", []
        first = _LRC_WORD.search(rest)
        if first:
            lead, pos, cur = rest[:first.start()], 0, None
            for wm in _LRC_WORD.finditer(rest):
                if cur is not None and rest[pos:wm.start()]:
                    words.append({"t": cur, "w": rest[pos:wm.start()]})
                cur, pos = _lrc_secs(wm.group(1), wm.group(2)), wm.end()
            if cur is not None and rest[pos:]:
                words.append({"t": cur, "w": rest[pos:]})
            rest = lead + "".join(w["w"] for w in words)
        txt = rest.strip()
        for t in times:
            line = {"t": round(t - offset, 3), "e": None, "text": txt}
            if words:
                shift = t - times[0]
                ws = [{"t": round(w["t"] + shift - offset, 3), "w": w["w"]} for w in words]
                if lead.strip():
                    ws.insert(0, {"t": round(t - offset, 3), "w": lead})
                line["words"] = ws
            lines.append(line)
    lines.sort(key=lambda l: l["t"])
    return lines


def parse_lyrics(text: str):
    text = (text or "").strip()
    if not text:
        return [], "plain"
    lines: list = []
    if text.startswith("<") and "<tt" in text[:3000]:
        lines = parse_ttml(text)
    elif re.search(r"^\s*\[\d+:\d+", text, re.M):
        lines = parse_lrc(text)
    if lines:
        for i, l in enumerate(lines):
            if l["e"] is None and i + 1 < len(lines):
                l["e"] = lines[i + 1]["t"]
        return lines, ("richsync" if any(l.get("words") for l in lines) else "linesync")
    plain = [{"t": None, "e": None, "text": ln.strip()} for ln in text.splitlines()]
    while plain and not plain[-1]["text"]:
        plain.pop()
    return plain, "plain"


def _lyrics_result(source: str, text: str, meta: dict) -> Optional[dict]:
    lines, sync = parse_lyrics(text)
    if not any(l["text"] for l in lines):
        return None
    return {"found": True, "source": source, "syncType": sync, "synced": sync != "plain", "lines": lines, "meta": meta}


def _fetch_unison(video_id: str, title: str, artist: str) -> Optional[dict]:
    def get(**params):
        raw = _http_text(f"{UNISON_URL}/lyrics?{urlencode({k: v for k, v in params.items() if v})}")
        if not raw:
            return None
        try:
            body = json.loads(raw)
        except ValueError:
            return None
        d = body.get("data") if isinstance(body, dict) and body.get("success") else None
        return d if isinstance(d, dict) and d.get("lyrics") else None

    d = get(v=video_id)
    if not d and title and artist:
        for a in dict.fromkeys([artist, artist.split(",")[0].strip()]):
            d = get(song=title, artist=a)
            if d:
                break
    if not d:
        return None
    meta = {k: d.get(k) for k in ("id", "song", "artist", "language", "confidence", "voteCount")}
    return _lyrics_result("unison", d["lyrics"], meta)


def _fetch_lrcred(isrc: str) -> Optional[dict]:
    for ext in ("ttml", "lrc"):
        raw = _http_text(f"{LRCRED_URL}/s/{isrc}.{ext}")
        if not raw or raw.lstrip().lower().startswith(("<!doctype", "<html")):
            continue
        res = _lyrics_result("lrcred", raw, {"isrc": isrc})
        if res:
            return res
    return None


@ttl_cache(ttl=3600, maxsize=500)
def _get_lyrics(video_id: str, title: str, artist: str, isrc: str, source: str) -> dict:
    order = []
    if isrc and source in ("auto", "lrcred"):
        order.append("lrcred")
    if source in ("auto", "unison"):
        order.append("unison")
    fallback = None
    for name in order:
        res = _fetch_lrcred(isrc) if name == "lrcred" else _fetch_unison(video_id, title, artist)
        if not res:
            continue
        if res["synced"]:
            return res
        fallback = fallback or res
    if fallback:
        return fallback
    note = "lrc.red looks tracks up by ISRC. Enter this track's ISRC to use it." if source == "lrcred" and not isrc else None
    return {"found": False, "source": None, "syncType": None, "synced": False, "lines": [], "note": note}


@app.get("/lyrics/{video_id}", dependencies=[Depends(require_key)])
def lyrics(
    video_id: str,
    title: Optional[str] = Query(None, max_length=200),
    artist: Optional[str] = Query(None, max_length=200),
    isrc: Optional[str] = Query(None, max_length=20, description="Needed for lrc.red lookups"),
    source: str = Query("auto", description="auto, unison or lrcred"),
):
    """Synced lyrics as timed lines. Unison is queried by video id, lrc.red by ISRC."""
    check_video_id(video_id)
    if source not in ("auto", "unison", "lrcred"):
        raise HTTPException(400, "source must be auto, unison or lrcred")
    isrc = re.sub(r"[\s-]", "", isrc or "").upper()
    if isrc and not ISRC_RE.match(isrc):
        raise HTTPException(400, "That doesn't look like an ISRC (2 letters, 3 letters/digits, 7 digits).")
    return _get_lyrics(video_id, (title or "").strip(), (artist or "").strip(), isrc, source)


# ---- Cover art (auto-cropped to a square) ------------------------------------
@lru_cache(maxsize=64)
def _fetch_thumb(vid: str):
    for name in ("maxresdefault", "sddefault", "hqdefault", "mqdefault"):
        try:
            req = UrlRequest(f"https://i.ytimg.com/vi/{vid}/{name}.jpg", headers={"User-Agent": "Mozilla/5.0"})
            with urlopen(req, timeout=10) as r:
                data = r.read()
            if len(data) > 2000:
                return data
        except Exception:
            continue
    return None


def _trim_borders(img, tol: int = 28):
    start = img.size
    for _ in range(3):
        w, h = img.size
        bg = Image.new("RGB", img.size, img.getpixel((2, 2)))
        diff = ImageChops.difference(img, bg).convert("L").point(lambda p: 255 if p > tol else 0)
        box = diff.getbbox()
        if not box or box == (0, 0, w, h):
            break
        l, t, r, b = box
        if (r - l) < w * 0.3 or (b - t) < h * 0.3:
            break
        img = img.crop(box)
    if img.size != start:
        w, h = img.size
        if w > 8 and h > 8:
            img = img.crop((2, 2, w - 2, h - 2))
    return img


@lru_cache(maxsize=256)
def _cover_bytes(vid: str, size: int):
    raw = _fetch_thumb(vid)
    if raw is None or Image is None:
        return raw
    img = Image.open(io.BytesIO(raw)).convert("RGB")
    img = _trim_borders(img)
    w, h = img.size
    side = min(w, h)
    left, top = (w - side) // 2, (h - side) // 2
    img = img.crop((left, top, left + side, top + side)).resize((size, size), Image.LANCZOS)
    out = io.BytesIO()
    img.save(out, "JPEG", quality=88, optimize=True)
    return out.getvalue()


@app.get("/cover/{video_id}", include_in_schema=False)
def cover(video_id: str, s: int = Query(400, ge=64, le=1000)):
    """Square, border-free cover art."""
    check_video_id(video_id)
    data = _cover_bytes(video_id, s)
    if data is None:
        raise HTTPException(404, "No thumbnail found")
    return Response(data, media_type="image/jpeg", headers={"Cache-Control": "public, max-age=86400"})


# ---- Home feed -------------------------------------------------------------
KOLLYWOOD_HITLIST = "RDCLAK5uy_nTbyVypdXPQd00z15bTWjZr7pG-26yyQ4"
HOME_PLAN = [
    {"id": "kollywood", "type": "playlist", "title": "Kollywood Hitlist", "playlist": KOLLYWOOD_HITLIST},
    {"id": "tamil_hits", "type": "playlist_search", "query": "Tamil hits"},
    {"id": "tamil_love", "type": "playlist_search", "query": "Tamil love songs"},
    {"id": "tamil_90s", "type": "playlist_search", "query": "Tamil 90s"},
    {"id": "tamil_party", "type": "playlist_search", "query": "Tamil dance party"},
    {"id": "anirudh", "type": "songs", "title": "Anirudh Ravichander", "query": "Anirudh Ravichander"},
    {"id": "arr", "type": "songs", "title": "A. R. Rahman · Tamil", "query": "A. R. Rahman Tamil"},
    {"id": "raja", "type": "songs", "title": "Ilaiyaraaja", "query": "Ilaiyaraaja"},
    {"id": "pls", "type": "featured_playlists", "title": "Tamil playlists", "query": "Tamil"},
    {"id": "albums", "type": "albums", "title": "Tamil albums", "query": "Tamil movie soundtrack"},
    {"id": "artists", "type": "artists", "title": "Tamil artists", "query": "Tamil playback singer"},
]

HOME_FALLBACK = [("kollywood", "Kollywood Hitlist", [f"{MUSIC_URL}/playlist?list={KOLLYWOOD_HITLIST}"])]
_home_cache = {"t": 0.0, "data": None}


def _load_section(sec):
    sid, title, sources = sec
    for src in sources:
        try:
            with yt_dlp.YoutubeDL(base_opts(extract_flat=True, playlistend=25)) as ydl:
                info = ydl.extract_info(src, download=False)
            items = [track_summary(e) for e in (info.get("entries") or []) if e and e.get("id")]
            if items:
                return {"id": sid, "title": title, "tracks": items[:25]}
        except Exception:
            continue
    return {"id": sid, "title": title, "tracks": []}


def _playlist_tracks(pid: str, limit: int = 25):
    p = ytm().get_playlist(pid, limit=limit)
    return p, [t for t in map(_track, _audio_only(p.get("tracks") or [])) if t]


def _load_home_section(spec):
    sid, typ = spec["id"], spec["type"]
    empty = {"id": sid, "title": spec.get("title", ""), "tracks": []}
    try:
        if typ == "playlist":
            p, tracks = _playlist_tracks(spec["playlist"])
            return {"id": sid, "title": spec.get("title") or p.get("title"), "tracks": tracks[:25]}
        if typ == "playlist_search":
            hits = ytm().search(spec["query"], filter="featured_playlists", limit=5, ignore_spelling=True)
            for h in hits:
                ent = _entity(h, "playlist")
                if not ent:
                    continue
                try:
                    _, tracks = _playlist_tracks(ent["id"])
                except Exception:
                    continue
                if len(tracks) >= 5:
                    return {"id": sid, "title": ent["title"], "tracks": tracks[:25]}
            return empty
        if typ == "songs":
            raw = ytm().search(spec["query"], filter="songs", limit=25, ignore_spelling=True)
            return {"id": sid, "title": spec["title"], "tracks": [t for t in map(_track, _audio_only(raw)) if t]}
        kind = {"featured_playlists": "playlist", "albums": "album", "artists": "artist"}[typ]
        raw = ytm().search(spec["query"], filter=typ, limit=20, ignore_spelling=True)
        items = [e for e in (_entity(x, kind) for x in raw) if e]
        return {"id": sid, "title": spec["title"], "items": items}
    except Exception:
        return empty


@app.get("/home", dependencies=[Depends(require_key)])
def home(refresh: bool = False):
    """India / Tamil home feed. Cached for 30 minutes."""
    if not refresh and _home_cache["data"] and time.time() - _home_cache["t"] < 1800:
        return _home_cache["data"]
    note = None
    if YTMusic is None:
        sections = [_load_section(s) for s in HOME_FALLBACK]
        note = "Install ytmusicapi for the full Tamil home feed."
    else:
        with ThreadPoolExecutor(max_workers=4) as pool:
            sections = list(pool.map(_load_home_section, HOME_PLAN))
    seen, out = set(), []
    for sec in sections:
        if not (sec.get("tracks") or sec.get("items")):
            continue
        key = (sec["title"] or "").casefold()
        if key in seen:
            continue
        seen.add(key)
        out.append(sec)
    data = {"sections": out, "note": note}
    if len(out) >= 3:
        _home_cache.update(t=time.time(), data=data)
    return data


# ---- Charts (per country) ----------------------------------------------------------
CHART_COUNTRIES = {
    "ZZ": "Global", "US": "United States", "GB": "United Kingdom", "IN": "India", "CA": "Canada",
    "AU": "Australia", "NZ": "New Zealand", "IE": "Ireland", "DE": "Germany", "FR": "France",
    "ES": "Spain", "IT": "Italy", "NL": "Netherlands", "SE": "Sweden", "NO": "Norway",
    "DK": "Denmark", "FI": "Finland", "PL": "Poland", "TR": "Turkey", "BR": "Brazil",
    "MX": "Mexico", "AR": "Argentina", "CO": "Colombia", "CL": "Chile", "JP": "Japan",
    "KR": "South Korea", "ID": "Indonesia", "TH": "Thailand", "VN": "Vietnam", "PH": "Philippines",
    "MY": "Malaysia", "SG": "Singapore", "ZA": "South Africa", "NG": "Nigeria", "EG": "Egypt",
    "SA": "Saudi Arabia", "AE": "United Arab Emirates",
}
_chart_cache: dict = {}


def _chart_block(ch: dict, *keys):
    for k in keys:
        b = ch.get(k)
        if isinstance(b, dict) and (b.get("items") or b.get("playlist")):
            return b.get("playlist"), (b.get("items") or [])
        if isinstance(b, list) and b:
            return None, b
    return None, []


@app.get("/charts/countries", dependencies=[Depends(require_key)])
def chart_countries():
    return {"countries": [{"code": c, "name": n} for c, n in CHART_COUNTRIES.items()]}


@app.get("/charts/{code}", dependencies=[Depends(require_key)])
def charts(code: str):
    """Chart playlists, ranked top songs and top artists for a country (ZZ = global)."""
    code = code.upper()
    if code not in CHART_COUNTRIES:
        raise HTTPException(400, "Unknown country code")
    hit = _chart_cache.get(code)
    if hit and time.time() - hit[0] < 3600:
        return hit[1]
    if YTMusic is None:
        raise HTTPException(501, "Charts need ytmusicapi: pip install ytmusicapi")
    name = CHART_COUNTRIES[code]

    def official():
        try:
            return ytm().get_charts(code) or {}
        except Exception:
            return {}

    def searched():
        out = []
        for q in (f"Top 100 {name}", f"{name} top songs chart"):
            try:
                for h in ytm().search(q, filter="featured_playlists", limit=6, ignore_spelling=True):
                    e = _entity(h, "playlist")
                    if e:
                        out.append(e)
            except Exception:
                continue
        return out

    with ThreadPoolExecutor(max_workers=2) as pool:
        f1, f2 = pool.submit(official), pool.submit(searched)
        ch, found = f1.result(), f2.result()

    pid, items = _chart_block(ch, "songs", "videos")
    tracks = [t for t in map(_track, items) if t]
    if pid and not tracks:
        try:
            _, tracks = _playlist_tracks(pid, 50)
        except Exception:
            pass

    playlists, seen = [], set()
    if pid:
        seen.add(pid)
        playlists.append({
            "kind": "playlist", "id": pid, "title": f"Top songs · {name}", "artist": "YouTube Charts",
            "thumbnail": tracks[0]["thumbnail"] if tracks else None,
        })
    for e in found:
        if e["id"] not in seen:
            seen.add(e["id"])
            playlists.append(e)
    if not tracks and playlists:
        try:
            _, tracks = _playlist_tracks(playlists[0]["id"], 50)
        except Exception:
            pass

    _, aitems = _chart_block(ch, "artists")
    artists = [e for e in (_entity(x, "artist") for x in aitems if isinstance(x, dict)) if e]
    data = {"code": code, "name": name, "tracks": tracks[:50], "playlists": playlists[:12], "artists": artists[:20]}
    if tracks or playlists:
        _chart_cache[code] = (time.time(), data)
    return data


MOODS = ["Energize", "Feel good", "Relax", "Workout", "Party", "Commute", "Romance", "Sad", "Focus", "Sleep"]
_mood_cache: dict = {}


@app.get("/mood", dependencies=[Depends(require_key)])
def mood(name: str = Query(...)):
    """Tamil-leaning rows for a mood chip."""
    if name not in MOODS:
        raise HTTPException(400, f"name must be one of {MOODS}")
    hit = _mood_cache.get(name)
    if hit and time.time() - hit[0] < 1800:
        return hit[1]
    if YTMusic is None:
        raise HTTPException(501, "Moods need ytmusicapi: pip install ytmusicapi")
    low = name.lower()
    plan = [
        {"id": "a", "type": "playlist_search", "query": f"Tamil {low}"},
        {"id": "b", "type": "playlist_search", "query": f"{low} Tamil songs"},
        {"id": "c", "type": "playlist_search", "query": f"{low} Kollywood"},
        {"id": "d", "type": "featured_playlists", "title": f"{name} playlists", "query": f"Tamil {low}"},
        {"id": "e", "type": "songs", "title": f"{name} · songs", "query": f"Tamil {low} songs"},
    ]
    with ThreadPoolExecutor(max_workers=4) as pool:
        sections = list(pool.map(_load_home_section, plan))
    seen, out = set(), []
    for sec in sections:
        if not (sec.get("tracks") or sec.get("items")):
            continue
        key = (sec["title"] or "").casefold()
        if key not in seen:
            seen.add(key)
            out.append(sec)
    data = {"name": name, "sections": out}
    if out:
        _mood_cache[name] = (time.time(), data)
    return data


@app.get("/cookies/refresh", dependencies=[Depends(require_key)])
async def cookies_refresh():
    """Trigger the Google sign-in + cookie rewrite immediately."""
    try:
        return await refresh_cookies()
    except Exception as e:
        raise HTTPException(500, f"Cookie sync failed: {e}")


@app.get("/debug", dependencies=[Depends(require_key)])
def debug():
    """Shows whether cookies/JS runtime are visible to the server."""
    here = os.path.dirname(os.path.abspath(__file__))
    bundled = os.path.join(here, "cookies.txt")
    opts = base_opts()
    cf = opts.get("cookiefile")
    names, bad_lines = [], 0
    if cf and os.path.exists(cf):
        for line in open(cf, encoding="utf-8", errors="ignore"):
            if line.startswith("#") or not line.strip():
                continue
            parts = line.rstrip("\n").split("\t")
            if len(parts) == 7:
                names.append(parts[5])
            else:
                bad_lines += 1
    return {
        "yt_dlp": yt_dlp.version.__version__,
        "cookies_txt_in_repo": os.path.exists(bundled),
        "cookiefile_used": bool(cf),
        "cookie_count": len(names),
        "has_SID": "SID" in names, "has_PSIDTS": "__Secure-1PSIDTS" in names,
        "malformed_cookie_lines": bad_lines,
        "player_clients": opts["extractor_args"]["youtube"]["player_client"],
        "proxy_set": bool(opts.get("proxy")),
        "cookie_sync": {"enabled": COOKIE_SYNC_ENABLED, "refresh_hours": COOKIE_REFRESH_HOURS, **_cookie_state},
        "deno": shutil.which("deno"), "node": shutil.which("node"),
    }


@app.get("/health")
def health():
    return {
        "status": "ok",
        "yt_dlp": yt_dlp.version.__version__,
        "ffmpeg": bool(shutil.which("ffmpeg")),
    }

# Suppress WinError 10054 on Windows asyncio event loops
if sys.platform == "win32":
    from asyncio.proactor_events import _ProactorBasePipeTransport
    
    _orig_call_connection_lost = _ProactorBasePipeTransport._call_connection_lost
    def _call_connection_lost_silent(self, exc=None):
        try:
            _orig_call_connection_lost(self, exc)
        except ConnectionResetError:
            pass
            
    _ProactorBasePipeTransport._call_connection_lost = _call_connection_lost_silent

if __name__ == "__main__":
    import uvicorn

    port = int(os.getenv("PORT", 8000))
    uvicorn.run(app, host="0.0.0.0", port=port)
