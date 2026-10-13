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
    "+PLiTy4v/vPLi//i8uKfXV78V5cX/83lxb+4vPjvLi/+h8uL/+ny4i8uL/7Xy4v//fLi/7i8+D8vL/6vy4v/+/Li/7m8+FeXF//2"
    "8uKvLi/+w+XF315e/N3lm59evrm4fPPm8s1vX7752eWb371883uXb37/8s0fXL75w8s3f3T55o8v3/zp5Rtq6w8vL/7x5cU/ubz4"
    "08uLP7u8+KeXF//l5cV/fXnxzy8v/tvLi//+8uLPLy/+58uL/+Xy4n+7vPiXlxf/+vLi311e/PXlxd9cXvzl5cW/ubz4+eXFv7+8"
    "+I+Xb/7J5Zs/uXzzZw4a9Q9eso6RzvxpEBF7dBgGh3FwOA0OaaCTIMdhFgf5NOCMosEEqffiYEI3JvCZCmgqxjGxT0T6wWUPwoAe"
    "700DIKgkwSgMRnEwmgajKBglwWkYnE6D04S2RpDFJD8ECLVOgmOcq7S698NgPw72p8F+FOwnwedhQBP7+TT4PAo+RzICddmH3yAd"
    "D0E3DrpTzHk3CdIwSOMgnQZpFKRUZRwcR8HRtNHJ02E8aTYC1xvyB0/FYM+U4wcf79ht2dPb8gdPofe8SwNEzI6vjscCLNGhgRKI"
    "TNK2bRjW1pfFvnZrZ3G/DZX7vWqOsYJA3VpqOfl0RIfZ1mwEfubsjO0o5JRmcsoRIpl1d8rhgC35ZTgRWDbJf0T7owk6rPWI8/R4"
    "NciQ1Zt+rnmVE5lgtRndVs1na1p0U05dUWqbRFcT5UG2hIyMhuPB28a0Pl9ZH7OjSnwfwMlu4Kfv6YkLHW3Q/1HwRLif4q1f5iO9"
    "N37rb2zkArOk/FH4ue10jBnNqrqkU6d8ODYu3/xWQ0mz9Pt3GspYR7//UYMtb8H5dm/g6XxP3cZdWCii3XwrGvfVvMQSnZM2txu0"
    "+1BvT/4cEKdgc0TLV9yXt814LyxjbE+D1cr7jVPM9an2MWdBxt6r++oj9dUXF/arL3gEYvntjMAFj0Akv3+vbjSO3NFQKUUa8tGN"
    "Y3TnqOXgXMqX4mHVNx15X3M04zuwBbCx/b4IIId3ZvLS6A3W7H4zdhvJgN2qYJvLSuKN0yweUmepk9/PouiwrMr9sSJEjS//ZRC+"
    "/vIvg+7rL/9VcPT6y38d7L/+8t8E/ddf/tsgev3VnxDZfP3lvws+H7z+8ufB56+//Ksgfv3lXwenr7/898Hh6y//QzB8/eXfBKPX"
    "X/7HYPz6y78NqPTfBenrr34aZK+/ugjy11+9CSavv/qtYPr6q98O9l5/9TvB4eD1Vz8jWv76q39E3/r6q98lWv/6q9+jf3H1+8Hr"
    "r/6A6v/qD+nHH6EP/5io9+uv/pjI+Ouv/ik1/9U/C07p3z8LTqPX/++fBPuG1r52wo1SIQobP95OibgwHKaavxWDJ6/2+2kmNJSR"
    "noWl810sFYOH51Rf0XoFbRrfJa7L5yOk/u+/1GP9xV/SWH+BYf4Cw/wFhvkLDPMXNMCvv/g5fdsXfxVMBq+/+Gv8xAB/gQH+AgP8"
    "BQb4i78NTl5/8Xc0yr/4KY3yLy5olH/xWzTKv3iDf36bhvoXv0OD94uf0VD/gof3F78bpPTo94Jk1jh9/+Vbx2k/OyyP0zjJRuEQ"
    "2BaNZ48fNlreObR0Xbw5rt/a43Oo0Sj4rtrSX/zdL36HiyS0HZ3xpn5VjLfcLYy36ejLT9lOwT14cId78ODx4535146HygN4qCxt"
    "GHcVeVrnsiJP69xWVM3WdUXdcNxX5hf3vaMc4nwzVwe5hoQ1o4EPaKtjrWw7989sL5ebp8bQJs87S67J8/Fj698r5v2CfVy9BpW6"
    "fY1GyLym1PiF1/R7GELnRQwlR56oxxhUG9uuRKvqHmC4TVHhfaoL3nCqpM3sFVO3ae06t43/s0kfqgn2udEyECmFzz74goj2iXhN"
    "EasX9YCUhT/A3gkR/jOFmxwxoXlKk0ds4eQ4QgBtmEVGNwOrGuacYXmQrZ32YQB/Ssl6TRyjeCItRgz2nHMCZBXOz2TbBvNy000E"
    "FHmY99OJ0oOsZ1l4iuea40FkypC3CHN0/19v15rctrGl/3sVkCp1QcYUJcqOnYixcyVbydVc+VGWE09GVmSQhChGIIEAoCiOwoXM"
    "FmYD83+WMiuZ853TTwCUnFTllqssEGg0+nH6vB9jx7ihUugmwrr5IYVoGw2HiulDrnDHnB0EY4NBrty3An4HISt5fnp11iWmc6qi"
    "APEl2DyfCfRTO2efaPzUHKwfNXGZRXwYzIbcZ8SEW4ad21O9uZ9z+lXjvnAMFlbN6y6FjubLred+a9EJruqW+oX+CsEPL53NPu5z"
    "gGMnvcP2Lx8LVTl6QW/q98xiMnW/8vxgtj8WX6x7Rc/Bu6nZgXmpgVjduVWwp8AWVWXarbb1qPuQcq4Y5VLXVcjJiU1OlgfpaNlK"
    "CClNhpdu7Bu2E06DLeNBjxbMW3I/hR/8yrnh1RNG8gt8c9FdeCU4Odxngz39WovCoHhbtHjhvPzJS4iw0P6jC5NG5JNPlI28AqpP"
    "s1UHalH4q6g+UYcBGzu//UvrY/Flu3X6sfh4cvbld23+SXsW38QYgLuZG9PT3TMz/vvH3K/xj1nOBwSFXKgr7TnAd3Vj3fsXt9PT"
    "HjcJdL5U73tBuajUW0r1EHiYtqASJxbz8n6iUc4YPfzbbFBkfc4ngXa69ge+/sj7+icNtGt0uSWn/U84p5AtWyWwcGMSUwXh//3X"
    "fztPXChBM9OO67MgJb89AfRTMT90qh5u1ypz2FIf1ZghOR2t0ocOfwPXL2d551qKAIDEIXotab1kgauLqpJYqAUMKqX96ARyMP17"
    "L78D69w21OlU3ryF482bokxj2ONN2rH505Lli3nOJNw6Hc+y95FYbENxHw5tkrXBjfZd/g0Buiy3DG5sggbUWWMsQd124SWNmqns"
    "jn7MXckHO/pzJpMECa5uN0BQpSBYCXuR4b/13JxTsTlWbl5chE3xLDKTNX7QTniF2FF4VXT95mR5mHCZizNcH42wBFs9XH+Ymct3"
    "0YWUeE6WSJT4vpAiz2z0KnI2eUuhYv6F+rorg5ST5Uk+bPTEpraQcRGiGJrmJz+/fnF+vH9weMwSM3CwKm7HhiNZdahxiIFWD3Bp"
    "HxDjOUHZ3vlM3QKVkL6Pfz5/vf/q8IR7loDJEDGRIYrYTwqu9vsjX+AD+TCP4W1CF0i5J7eSyYBuHb97cXx04PScLPdVCcTbFVaJ"
    "tm0gUdry+2h2kahSh9gGtoqpd1RE6tEIDt1FOs8NPxYNyzkdnCVxl9ex3mOwcZPygWzkSRmV2NpwhnyX+ND3qbu171m3w/t2nEYj"
    "5+fhxYW4RpZwx1Tj4e4wY4nFDANCYFL0IfhdfcPM980VF8ZBiPBGS+KduxLSwZe8Pc6lTTPsHHWktiDU5Sbs4GR5cnxgTOZodKbB"
    "slg6RQPhy4aPyurRWTrV1xCtTs8c0Q+ZHrnepJ9W/FRWogMX+egab0XXalmQptLfF3c7WoAfabMAPwyftjiECXN4SYxw3LbC+eUk"
    "K6RwhRDkK6/2IGcdSVTlhSuEvQl+/eK2pXaLUBYHqnAHbjAsayAVvgg5tZEGdKKoq6a6gHY9JrOLlDfSWcvvgk/XkyigL99+3ilo"
    "O+sNoqfOkErMYE80mtGZfL/MVENVMjdU8VvJ8nJUC7Hx0uYvaYE0RcLQmysmJktebC6rgItVJeamTAbIbcXkxF872QYiyKYOQbqo"
    "xJ9Aes/V9m8+34+qBcM+efQM8z1eEsnxUrFdcmI8c345w686Z7+DbDn3zVlspl1O7qGBW0inmtyojAaFSm1Dl1giHv+ZqrnclM0m"
    "WYLcdIINDBdJswfohTM4cJIjmoNkVNjq8UMiyPslCRS0HPQ211uTDEzQtEvrkNXhvNhQOJvs3VOin43JCitj8DmFt3F8hawUBBPO"
    "4oIEIQkzKJGgCwG1TnDJVdYUQTxFZRd6uvr9i1tqij94ZfXpTHMP1NzK95PSKQGE+RODl0fqAw571uKvP9Oolc2NPCLUMLyR/7s6"
    "buk7+8O4onkz/IHo5B+YoFTcWTcxp66uWgh3Afu1OetEMHlcpMl13NILp2ryoKlltDSB46emi8p9O4LfCiXj//ju+ITj1t9GeTQt"
    "tN8DgXA+IVnG5PpWGR5taVyd17HDC0H3k8F8yrdxoVdEV/jZc1OxVQv/6MaCwvawHGBQdd6T005wfcbMy3Xb5cQrk+Oo/FpCI1eZ"
    "dUc980/bAgbbau++++L2twL15L0gzSCo7MHIFcw+h/6yfb4GoSZ7S1NiFk7H4kK7ALH9rcFZQuUP8USxwyUSFFdEOjXkVcAuQMnS"
    "Zg2vAovk/m5LLgcosYijgwaqSFEvgb2EkBRaNCx7rHuS7waEpljtVKhSJoSzS2LO1EmDNotXSqmw4qigpZrMGmIfhZGLVeV0gXTm"
    "sMzq2CBRzXvhft8PUmZGTNpojs0ePsX/MnYUGuBwYH2XgJhKfk69KymZZ2HK4AzNVtdTJKjIVx6UPwE7uDdXxJX5Q2L2zx54h0Tx"
    "k/WylVo2GnBLpXYoMZ1QEtaYcmLJ0uR8FzOR307nO3OXg8FicQk1zcTNZSi8WpVr5jBjBpmWUlUqflE4M+bhOPdAHlMvacZBxe31"
    "UHEi3/GAw2FSgVWMIKD5Vne1vUe06j0nk4jIVKehsF+QkuZaLgmF/wrP/JSiEnii2uPbDn1wuIScM8DWM32hsc1KYqDoxs9XwW7R"
    "ggTNofWmITNzV+EZT8Yg0xvtHcAwRqOBb4ChI1pOF2XCGogycgMLsgwGlndsKN0hZf6aS3aUbh5HT/lgl+yuyqNg2NfUHnW1FCLp"
    "2jKjiVBcnHKFKjGN/gOte+jWiyeTdBFD1aHzijiSuM1d1FQGmTWsd3TMWn9OevpnO68eD2dWawQ7Ux+XB2WT91XzaRr8qaRXAS+r"
    "vugbSZa1DFZ1u2HxK7dgxGMAh8G4r4pgusnOKwV8UHQHUryAHid9zpCRfOXlbNAouYKA5buOMlhjVZZmMeoNQ4RldL5MfjdOZ9GU"
    "RMwCNhhBY5dEE2cmuYKD76o5D6wygNCEnLAN54SxjUsdRE4J46dCcPVdIKH1HAv6W8+8bzWeZlc590y+Vd2VT/6uBOszK3DFgWq2"
    "WHekDQWaFQBazVffar76jnJMIM8oLGz2a8V0SfYLT9WhwcOFV75zzwz17EZdlCRk5vR1agmZlzWDyZlkzVhXgi9ZXiBL8Sybl1Ks"
    "bnkEIdrk6KUnm1K5/TJNaHbPNo9O3r3oEMobd4MfDn589bS3s/vNk53Hm1JdR2clr8kfKBE5jW5k9s82e082Wcc2TKcZSMWzTRLl"
    "1C1ieUu2tT/bhAk4GhJtKDaDIouThNjb4dWzTZYUN9dmy6AzkUquDKWYWJOwuZpuXLUG9zkq9KIOlgHmjJxIcdDb3TJjIsAfpjnj"
    "AGRWaXcDUW3A7ZHHiVorNKEpSRND5mapK2JD4rQrAOnWUk5rhknrGsQEDPtCKJpX2fU+KLYcnwMnvbxnldn+5XR/6z/ObndX+Luz"
    "9c3Z7aPVx9Ht05U2vV23q/mw3kObNUrjYvYxJDST0ilFHdcgmvF6uAmx+DvOjkvZJEvitOL3307evO5K+OvkYilA0vZGqjC18lgS"
    "rkZ4Jee+4nHaDVTU6IuVROTRUMf+yUv6Q+rxBOO07y11OiNJwyt+rbgFlqQxkEPU3KVxjFNTKKyaqFAf8FG/zhk6jBe41GeB1YCp"
    "GlJKvx3q+r9ermiFUNh8l/jB1qrXCIqkiqESDm1Nhkm3WF3LtVF51sRholhPZIIYKTOHybfH2vWw0/BJnoro0TpsJP7ytPXx9Kz7"
    "5Wn749kZ/dRwSGNm0WIwvpbmZzUblmMbckpJpyOxvngW3IoxK7N6U5qIVuhN8FuyvqOXlTmcFUOewfeq5nc9RTQJu2H7TG+Wa9LZ"
    "kQ5+5GpGLaYp/zS5dn0ZiKtmzyZTNDxFguxoOCmXe8GOcFjmdy9YneGG1WI8+nqnA4GVjhdcBAkNbCGXl8py5kgoehiW5I205Uqx"
    "W5pmqQ3GD55+JXeeo2CEpTjqKnKNPOGsPukEDqhqETVJxdBwiZioY8cxtMNRUls9J8N0wlFulxNrh8OHcPsh333+HIE+GPPx6fSs"
    "W6I1jeVhsNPd+ZrZDcnjwN/E/Z4RIfnzU4kU0uLvRPFARPAtica8jbMEMskpSzl106CVZDlMyq1N2HOyoQ2xySW3+la3kZoqqG2f"
    "p4TDy2Ur3NqCbMeqKaLDUq8vGhStKxoy4myftNs29EHzKBOXRXnghHqp+AsnlemW5eSfB4++gncRgUA84/Subl5hv4djEsrW+jzY"
    "h2JOnGnYNxs6ozkvXI3TojidmY1rBzOdcEMJuxlDJm0Bej5fKB24/e08bTiQCy5tKfwwdGMjxG0GL9+8CrhxECPRb3CRR9PYRg4q"
    "GPgws77Rak1nmrAUmYWIwgJE0bDXi5HaacTs9rjyVkOjoQEa3Uyq9m2YO9y9gInk5nIhJQu54/PMyD6rpphIHQVXZKfc6ZmJwoPz"
    "FKs9sHk6V/l8Nlb1TMpUvLQ83mSBkHZsn5umg7eTMLje1j2cTBVR+F2gL/nBYof+uJlrlAZ9xuktVNIMaqQ1SfPpgMgtwwxuPucO"
    "QC34J+3sTb+WRMQcn54+StENXJtbJU6+dLBtn3R7u86Rw0ikUSfodR+32+3KUDO2QWao2dHbwSrsgAv7fnITj1o9VfioI1HfZsn9"
    "gHJsGfY4u5b4cNnCjPinYdGMFBDBlV1bOY9VU6g9RCysMTPKfhobMadyM8Cw8qmBOvLFNCX50FFXAaF8K5XwBPmf8r2zOvKvCEwV"
    "+gc9PVITu8vv9tcl1h/qvJRzBNCLxJDRkP4Ri1ugpY20093dx7TR3UdfIy3uIL6MridpvhfI2ME3yBWzDqLBrhE/obu3VhcA/4W1"
    "8qfxEnH9OljtHXWzaF7ID576tWekgo88bUlBBCGLkcvReErkMeGeotxnGk9j+h7YpwVZmLN9e4PFPRms8bPQHEOzbL4hAzZXDgU3"
    "A8bDzxqx3Wdeqky8NtsuI+OM7I/M6wT6l4nDgCSaAWlaa/nNPARCo83W8Uwi1Np2x+pzIexw1fd9U7wJSJJCsTHWS4JqPbMxqQo1"
    "LF6lA+T8pUXilfQNlEhNHM4ZJ5NQ4GqltTOFa4lAukUxRazx3JmSdElY5hLZ//c4yy8Jn9M0zy5hmSDUDLfPLTpuSCbd6O3jpAlU"
    "0ZDZtT6x1/BmmrGboJ5KJ/hN+0musRkXbWOVR/W6il3+5Zv3J5rZY+8slYYclURzDcMykDdv37PDjeViv3ricrHD+WAy3BrE/zkh"
    "FNV9tNvpPt3t7HR6bS+lSzGLsooArWgJc+xgHYnQ78kE+RqTVNZDbD9f4p62IHIOVsn8LGm6r/aC34ihmGW4xj243Eo7XPGdTP3O"
    "eElJgpLfuCK5asW+7pzIthKKdQUDEw2VoFi8g+kabr7juDyASoeW4gXjxHe0+n65lItCS6dZlBfx9yTxli16D0le52U8OgEJaXHZ"
    "nBkX52SDZu+JJxmBkyUuJu8EFzTki4KY3EIVzUOaeXNLFoTu5REyKd/1QWrN69wmUQkVdZGuel7wx3dk55ztmzIZjQij8wZ+KvNo"
    "ViScCvc26jIDQpSBL1bZTUdq4zG1wF+61Xbs16JKAZuOGMCOWCO5X2KztWDFsz9V9mTorMczkCl8l/Zl+oaYHfYT2wl2pDqA3N+T"
    "DPcr1asxdqLebyf4E90p81i9Q2LNiKOi08G7TWjh++Ojt3vio88mqFjqXGoEspA6FcQBRFLZd5xMRjHXgzePiO2Hbsp3tGc80trv"
    "BAeeo31Ei7jfzSWbzwEuDvkObayjtY5kk1UtSGDjQe0O4Wc6MV4Te8PXHqvDfCOipNPPduD1q1wtdZtL4RRsI7khfY7T1qHc7rDH"
    "8HUr0j9V8/YqKIZRAmArblYEXcVy1f7UCUj4dmGXGNl9JFOn7xQ3zNtlN6HI5H6zA26ln+uSODwO5aagx6F+DnSBSjOO/e4F5nNA"
    "f2gobg/ar0F3oX8P9OH0Oomkk6jSCdbfdiG/ZFec17192w7cXVsR/tUdnoaM/joBJ4IggAayO/OjJvBRwmedAN/jiwH9r7jplQuN"
    "oJUtDxAXEVdetRRXeLW8kXEBzb3rORFHENPQsbxI/8RFpbYYnBAtPFFwmcRRrmufMRHzcLCq7EKk9A5uinnGKewgr+LRJGqFiO+4"
    "iPNiSyo2j7amKRNA+dkO4axNrePC/RQSvCVSPhA0r9X2slTp+bQrY2F+JFnCTYptxEswDKEO6/TbimzZso1Mz24BmsDiDRmHp8WV"
    "MVizYpM2y0eDBuP/3Hr0mPB5WFV2NWLNszrOHcXEHlH7xyiQQjIQcmZEw6tFlI8K7hQotSYYy4Bv17CwLWWTVoISMzPtWjAM4WgC"
    "k2tmW67iOGMxTHFjwrL9OgewwCgTz9L5+BLI+SIaxcrV5FKXLudSgxI2pRMtFITNuRCqipMyejuueVWxHHBGp5mPWgM+EyJQ8kpO"
    "+LxpB43+WihgoDG7+5vyFly3q/fqKHefrNdRaleg9Xtw17PbtTOEUbbt6//VGWppjtSpbYgl7QSPv97hbJn4Zav7wCnt1bzkb78Z"
    "kEBxDcGZcBaJDvKTxLIcM460s2Oxpwq3mTvfsz6bMz1jvUOdk8xDDiQnb0nN0Ke7OzgQTdb5IVcHhHMahsChoS5LXpVm+ECqZ/yk"
    "pZmLkthnpoUBbIcgRlypht4txRlGhI5+UCwmmZSVkoLucXDJVk8sIRLrM3C6XHbTqPFpx5/AV387nj48OmG64c57Z2eOgWbDdqZP"
    "aMyltKBFica8eeg/7oJyUW8v44tonpQt38/IsW8hkVkejWXezAFi5rJg23oFUMmgJVGSKcQzErXblVVk78MteU+JcbxgnMp2YVR3"
    "WkSDTCzTV3iYLhqWIEsnwEsYnFkI17FAKU+I9ao7qohZFDkDiXn3RX7tGyPamJ+D5/6+rpFNiN2nHqFoR+IetzeeoNRgoZWXMR+N"
    "OsENfstH/r0TLO2vn5WccP/UlYNKderFQiZtPsbakmJR8c0zuJQ9d/VQSLqgljedgO1Kdkx8e2kXiB4/J6zGnpK4NGp6WBC+DHrd"
    "XdbcLhynFANiZnaneiZz5qHUjyFKxyQOM8WRW40rUdrj5HxKYT1hqnQ0ZEXH8PbDfvA32n+SI5KkojbA/EKgtckw/sAlHkNIqjOi"
    "cnSMUtbVtJJ0yEeKTlMKg74kTQovyzIr9sR4q1ugri/X31DO68Rp4tZdjXq7T7s79K8H4MTeLiYzgvQGWICt12IV3h8z0K43CaJu"
    "Y7wG1/dt2s1fQc7Eky3OORwdAJGixn2Uz1rhyYc9QFeeayJCK8gUPqKG2RJpVNjfgpALZ/HB7WQkkpkye6QXF1Bf0T3oZcERFoIR"
    "skwTdOZDZHJsqiBhWf520RxG9GiyRaxBkmxd90JVSEq8q4Z1v4HcOAhdxJiYXV7iOkGguG/kGIt54TjHKp+avOt7ftrin8MuIYlq"
    "T2C0mUbS+43NUhZ+IQ9tn59jEuc8ifNzGIpNnG9T5StVnYldqMAqE2cMr8SsNA4zSgu/iA7Kmeiv6PpIYJlzJRjBYs76PvWIq/sE"
    "rtP8SYlElYlwU2oXPHo8mhTA2FsQH/awtaq5w6cDitWrDuA5HT+z9XO5BhcP2y07446jraalOBr1fcuwPTD5Mte1C02Fl7VnZhAT"
    "aonV4c94bV082kAh2bmzshe1Gd0xIuzp+vFEqETPg4n9s7xm/z/vs2bBlGfLEQFhYL4TFPPhMC4KiDvLDY6gxBirO6Q6tzxV3Z2f"
    "yYE3UCsu+fe7statijlJosJsCWD/HWIo8hfcwjMhyTtwleOrLvGww1Sjz4imlpWoVeqkLli7mCqXwP1wV8nt6aOeSXH0hhOTTN5G"
    "o98nb6G3pj/pSLl42MOBGe2PEQzL0rECi1cnJ2UeR1N3ltynOwftpJTqjdxjJvaEk7tDkCpYVR1s7o+4zuQ/sCQnrCLfDNuVHP13"
    "div7DWStsEcwGXKW72CZzvNggNJPxMgRMKMMOfF7zERP49k8rFZSFq3n6kEdGdXIcpICaY7hRt/C9VD4zveXk5yBdxTfVEsbtTSy"
    "cx07Tg7f/XTISeiEIG9vE0gQ31YS/UBX3fmVk67uhxdHL9H26e43jx71Hvee9r7+eoum9c2w980geZI/Laa/fjPcHeRXyeVXu/H0"
    "12w+u+jSqS264zQdJzF2FJoPWAwICp2u3yN1eygfPY/4xJ2X6VU8c9qM41KiUDUvIwEM2gEb/MIJwQ2RWbCfR2U8bb3/p4rQ6dfT"
    "nchNR89MPagCVLiCkn6Q3sTap+eu2u/J1QG3VHwyNFjK5KmehCYAg8l+PLJWj/HRjEOq1E9VdV4llvOUX3hzP8u0Akydh/Pz+Qzj"
    "5T5t9YbLySg+Tm29bk5FJ9+uMN5mQPblmtchF+6yJzOdHYNd+S6QWl4wpzoF6u0Hq2/YI9pcca/qRR0wlnm2mdHxgUrgqyfZTbD7"
    "OLvpwwFtK0om49nekPUum8+PVRVYPnfJZJBH+dL4XWtkQWu9LxDeQpQWhxEZDYE46oGfekn8Gw3YETQNNuBGD7T74H5eqgKfRcur"
    "3kks3DyPpV6sbeG8ycFOjS/pJw36T9oG2dT1IOCkJDQgC8c1hbEhn10kHEMaqhBLPabhVVUpmM5C4yT359QuTb1y7cK2ozt9O2GJ"
    "m4/LYQ7xEdv7QhCFUtHwwx/WPNW66xBqvsksrK+cPQ63TbPVCq2JmbCj8jGRDc3v8CLdu9Yh6wwe7ezUx0ZnA+j8RBgNFdKuw7M8"
    "tFYYtAb3SsaP1SitO9/TCJbINgvqCtOys2blHmemRJwtDreE3tY/ZVGSnpSBSOzEG07H5Id4tLzZRcPyJKJFVHFcyP/jVs2uBBvl"
    "cGo+pfGVXU75E49abEld6BYtFs+crcuR4JjWvH32WeskW6opR3/tw3XrWP+IkXNEkFIL5aRpI47WYFkmN+x3O+Cf4s7tu5kaqLEn"
    "51a9qPUA7ssMeohXuWmA3BinqV9BMXFJh6w19awssSZmh/JGXDmC08oH+JhL7+sOk4qscrtBUh9oQ+KG43/n+NXJajha9OEDIqjQ"
    "d99q0prO+k50luAVjowZ4AxEg4TRKFoNKgORXCs/xfnkYkmUhogLn44fGflybI/37flgOik1vHOC+znSudRVS+zTNfHqqWbaBfLb"
    "4IkKfMS2iE95ADbzSTAiybksUPS0YmvQs3Y88EXMV+wehO1rngXSrRAzWl6myNPw9s3Je8S6s8ayQBbtUE1+C17nnH00y4jhZZDe"
    "/pXd71cd9q7eq7rv33LYwx5NboXSYYoAC7XjY5rryuHeo5FxrOEpiDWlr4KUCaShnKshTGWqMss00sE9zPwdzYYpCTTE7r89es3L"
    "5VIdPjunO1CjDeeFKlFtxuTpHWqj0rtywqr+YD7LYYEHCHUDU4v1c75oINeAoyNKCiAxzvAPeov4Td+zn240yM3ClnaqdiBqq3GE"
    "ubaxIx9f6sARyTe31fOMePZtks1QDkiGZr2124HCS9qn08zWuyuCmNZ3GvDHSrmJSugQ6PPk535rnrEKzfC1vkE1QAOaVk5XGAra"
    "qSv8vZm2vSUDVjIpcrlYhjtjKZjhNPUeuKBWLbbSEEDyR2bum0/QRq9w26rLCZs2aMtJtq3oyZs1PG5YplgAskEa5aOXURk5Wi7v"
    "PlsEcEG0k/2d1gPaDnzX3UR4PsqsHIGBPgCW4JWnkzMvOEXW3vjt6vzPnTrM2q158LmguDKVNX5gGTcA57M1QToPaBtGCOvStx5q"
    "XnlLGIa2NfCMX8GNj/XehNpcofvwHafOFZkf8f3CBncCrafme+/iMd+u1G0YvyNkvmwNB+1bV4Us4jiOrlx1ldhfNNxie8iQ3RNN"
    "bL1HzO03FIPr0+CLSflDK058tw32YiMBLC/KQ3FVenE5SUZKybzwt3zh2m1h46/om5R6THUqppgP4gnEgVPmpjgNi6Pd4m7/OR7H"
    "kE1EG0PxTHLdlrQX0f0D/aQ9Zqiz7SDXLjIB8gvxDeloJU5q3spJ+WwsHixh0C37XFnC/AuettkAcSg3ADGnaH3mpLDnnCg23EJ7"
    "z7Dqoe4f8GfBRCfqyKOFH2P48KEM4HnQe6LDfHnEbRl4hdParJyl0WQ04zDDaNQNXiB6UsR8msYsVlIUlGzBgOXgXPlMQOcnNHiz"
    "npzUgWOsgxXOAj+9/kgC5eqLtMGqG1ftqHU5fhHN+kJ1oYeYSMbo20Bg8xymT2jYOhwWei5oe0/rhRAiCmPxHtIwZH6yWQMQLgAw"
    "QoHYE9dW1+avbWQN6fOX2zLov5Y/JOxI79I6yKS69obHM97LOdb5R+9BcB/3WGltSPGoq3zazxXaBuQyh/bm6lUxrmkiPLZz82cA"
    "qHqRA+wHcMAW0lHGBMcf4pD4+HiK5H8EzUEE/pSGN4Q7JvLAZVmOyAwAL5QbhO/Tq7DtlyI2A65vs88FV07UBX2Vug79yVfX3Gd/"
    "GyDpHs6373juUO+rWrk+TfaArmzdOV8pGPpmkIUbt2OiRnzEjxnTcUYRJFTRfLxjU4Q3nEbBswfs7MCuwbcBwotQPokNbjmsTQRd"
    "U9yC21g8Oh8Q8wI+q6AzDAIMzwlOVhbxixm1wkvs5R3qigjncNhCGrx0nJ6z9hKUDw1Yh0lPxKmH5miX6pSm0fuK/vsKE+rRjCom"
    "/xpB1hQXeQt8zztB6+9ijFp7KLFxhZbvPE/bErVIVyrFlt+y0r2EJlJj490UJwY6FQoFZm1VEt0C+Slo1GhVUzowNwelpKphPsgw"
    "Vz9N4gWhHFHwweF0vgT1jMfyf3pFf9VpdUs8/HR0+EHK9SrVIOrXz5dcjz4eqz/pFbtVyNtSjcsyUGnrWlFd7sss/UzOBKGD6y2U"
    "zJi1uypjFELy4Epy7cRfQnVYi/hVxTiE2deqSxBHs0AtETL97a3KjwweZuGdLjFDg7KIQbxTt6oZyKYGDfobZ8foTbVnmiMNRZub"
    "j19H05jLLGh5h3j7xqFiT8xQD+bLO4cKTT/EhWYTpCx2Q7QnNZs5NR+UmszR+WixfqWj89HRfU5lFa/4ddl+xqnN9RP5XGOT4Elg"
    "F5mUP+PUkd2Movl+qbcmTxIrmkm6rYou23FHVs7IDNcaJhVkt30duyP6vJ3nhP2LWEpyZrFkuIBrKrKBsiuL4NtA4RyRez5zo0o+"
    "a/TnfndBlz3Oc2ODUwDVx801zNCfhhpHy3YndA5ES9isjsvUAm7rhftLOa8sJ0GbGU4sqgYzvnufts7hsqijFPxoN73qBCO4k1Xe"
    "iwvH7TKHq9KVCE90OerOc2L+y0s4RoLU0AalRGH4GQBQGsW4KzbcFxqkhHUJlX7eOBtxjKHquF9T4cUGXf/1+KMOZLHHip2k2FhQ"
    "qgUeL/J0Nm5km1a2bOc7xUiK4mAvYB+4h4p79GN2hMUkrOyHSojXnIeXReUnhRw6qi/V4hA/6k3smdL0xBGX8QVmIeqH7G0CZ+6A"
    "2RwR3dAYM/XFMp2P5pePxd/PHv5d/f3YVRc6DwgPtf0534oCZvtlcvXvrccHFRMByGPdSiClzwY1rliYfGUj6K/1yG8An6beEGiu"
    "BInQ1mqrohBDfP9KzIFd05DyJzEF8dQlAqHY+42u7sQd1ivJeNo7pcPiQvXB9O3xzjdtseIbXq6hJol9VQrz3SHPfbpHhIMSh8HY"
    "VjkktmylJTsi6sS0IihDPI7oP4Z8SHllSu/yMq5E4jPC3qd+/Yha5qdyMNUDTzqsT7gO5Heg2fuR04OKrFiREtVONR2tO6XFAAE+"
    "uYP8tDlEHb2aRYTui3e0WiwwoGp5rIQ0GUlsA0n+f4Zj8jTwjFL7LlY+SNNyz2TOu5yU4rfLLoT7b49U8liNg4gfLICg4xvYt10x"
    "pWS/JnFwEihf6wSpfIUrERIbVd8e5asGLQSBhvEw/t//YScS4ydj3HY2FXP6+vD9+ZvXxz/bQocAYiTohQuQ5+ZjFSUM57xgznMl"
    "IrzUd6yha/3cZg1TMzO71f53sNsEqq0a9uePQI1BTAuCAqxbTV8Tsqrf0lrflMoCd4MXopLECQenHNSVj2s+ceu6U9gXOImHdE7i"
    "79VEIseYTezARYuwc8QBrvRBM/cHTRZfwCAdsS3xq/srqQR/YY+h2hKJtQq8BsWdp7Bz/C//da4tdfeWZo/Qf4UTCY/FwqjvNarW"
    "0MXBdtzUF4FPRfZy0K+KRYwUTuK0PgpJsQULLCMqNbNDqYoQ+Xa7GJKMVz6nK+w//l6W0+T5g/8H1Ugu1g=="
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
    return {
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


def _resolve_audio(video_id: str, force: bool = False, client: Optional[str] = None, fmt: Optional[str] = None) -> dict:
    key = _akey(video_id, client, fmt)
    pinned = bool(client or fmt)
    hit = _audio_cache.get(key)
    if hit and not force and time.time() - hit["t"] < _AUDIO_TTL:
        return hit
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
