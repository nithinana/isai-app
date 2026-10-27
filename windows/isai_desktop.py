"""Isai for Windows.

A desktop window (pywebview / Edge WebView2) around the Isai site, with the same Python backend
that the Android app runs, started as a separate supervised process.

 * Supervisor  starts the backend in a child process, mirrors its output to a log, and restarts
               it if it exits or stops answering (same rules as ServerService.java).
 * UI server   tiny local web server the window loads. It serves the live site (the last saved
               copy when offline, the bundled one if none yet) with an `IsaiNative` shim injected, so the page's Server logs
               screen, "Save as" dialog and media keys work as in the Android app.
 * Window      pywebview, with persistent storage so downloads and settings survive restarts.

The same executable is the backend: `Isai.exe --backend --port N` runs the FastAPI server.
"""
import base64
import collections
import datetime
import http.server
import json
import os
import re
import shlex
import socket
import socketserver
import subprocess
import sys
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
import webbrowser

# Windows: stop child processes (ffmpeg, yt-dlp helpers) from flashing console windows
if sys.platform == "win32":
    _orig_popen = subprocess.Popen

    class _NoWindowPopen(_orig_popen):
        def __init__(self, *a, **kw):
            kw["creationflags"] = kw.get("creationflags", 0) | subprocess.CREATE_NO_WINDOW
            super().__init__(*a, **kw)

    subprocess.Popen = _NoWindowPopen

SITE = "https://isai.thirai.uk"
BACKEND_PORT = 8765
UI_PORT = 8766
FROZEN = bool(getattr(sys, "frozen", False))
HERE = os.path.dirname(os.path.abspath(sys.executable if FROZEN else __file__))
RES = getattr(sys, "_MEIPASS", HERE)                      # where PyInstaller puts bundled data
DATA_DIR = os.path.join(os.environ.get("APPDATA") or os.path.expanduser("~"), "Isai")
MARKERS = ("isai-shim-v2", "isai-serverlogs-v1")          # the live page must have both (see build-apk.yml)


# ============================================================ backend (child process) mode

def run_backend(port):
    """Runs the FastAPI backend in this process. Exits when the parent closes our stdin."""
    os.environ.setdefault("YTDLP_FAST_CLIENT", "android_vr")
    os.environ.setdefault("YTDLP_AUDIO_CLIENTS", "android_vr;tv;mweb;web_safari")
    os.environ.setdefault("YTDLP_REMOTE_COMPONENTS", "")
    os.environ.setdefault("PUBLIC_URL", "http://127.0.0.1:%d" % port)
    os.makedirs(DATA_DIR, exist_ok=True)
    os.environ.setdefault("YTDLP_COOKIES", os.path.join(DATA_DIR, "cookies.txt"))
    ff = os.path.join(RES, "ffmpeg")
    if os.path.isdir(ff):
        os.environ["PATH"] = ff + os.pathsep + os.environ.get("PATH", "")

    def parent_watch():                                    # parent gone (even if killed) -> stdin hits EOF
        try:
            if sys.stdin is not None:
                while sys.stdin.read(1024):
                    pass
        except Exception:
            pass
        os._exit(0)
    threading.Thread(target=parent_watch, daemon=True).start()

    for p in (os.path.join(RES, "python"), os.path.join(HERE, "..", "app", "src", "main", "python")):
        sys.path.insert(0, p)                              # dev layout; frozen builds import normally
    import isai_launcher
    import backend
    import uvicorn
    uvicorn.run(isai_launcher._PrivateNetwork(backend.app), host="127.0.0.1", port=port,
                log_level="info", access_log=False, loop="asyncio", http="h11", lifespan="on")


# ============================================================ log + supervisor

class Log:
    MAX = 1500
    MAX_FILE = 512 * 1024

    def __init__(self):
        self.lines = collections.deque()
        self.seq = 0
        self.lock = threading.Lock()
        self.path = None

    def init(self, path):
        self.path = path
        try:
            os.makedirs(os.path.dirname(path), exist_ok=True)
            if os.path.exists(path) and os.path.getsize(path) > self.MAX_FILE:
                os.remove(path)
            if os.path.exists(path):
                with open(path, encoding="utf-8", errors="replace") as f:
                    for l in f:
                        self._push(l.rstrip("\n"))
                self._push("---- app started ----")
        except Exception:
            pass

    def _push(self, l):
        self.lines.append(l)
        self.seq += 1
        while len(self.lines) > self.MAX:
            self.lines.popleft()

    def append(self, text):
        if not text:
            return
        ts = datetime.datetime.now().strftime("%H:%M:%S")
        with self.lock:
            for part in re.split(r"\r?\n", text):
                if not part.strip():
                    continue
                l = ts + "  " + part
                self._push(l)
                if self.path:
                    try:
                        with open(self.path, "a", encoding="utf-8") as f:
                            f.write(l + "\n")
                    except Exception:
                        pass

    def since(self, after):
        with self.lock:
            first = self.seq - len(self.lines) + 1
            return self.seq, [l for i, l in enumerate(self.lines, first) if i > after]


class Supervisor:
    CHECK = 8            # seconds between health checks
    GRACE = 40           # backend import + startup can be slow on first run
    MAX_FAILS = 3

    def __init__(self, port, log):
        self.port = port
        self.log = log
        self.state = "stopped"          # starting | running | unresponsive | restarting | stopped
        self.restarts = 0
        self.last_error = None
        self.info = ""
        self.proc = None
        self.wanted = False
        self.busy = False
        self.launched_at = 0.0
        self.lock = threading.Lock()

    def command(self):
        override = os.environ.get("ISAI_BACKEND_CMD")          # used by the headless tests
        if override:
            return shlex.split(override) + ["--port", str(self.port)]
        if FROZEN:
            return [sys.executable, "--backend", "--port", str(self.port)]
        return [sys.executable, os.path.abspath(__file__), "--backend", "--port", str(self.port)]

    def start(self):
        self.wanted = True
        self._launch()
        threading.Thread(target=self._watch, name="isai-watchdog", daemon=True).start()

    def _launch(self):
        self.last_error = None
        self.launched_at = time.time()
        self.state = "starting"
        self.log.append("[app] starting backend on 127.0.0.1:%d" % self.port)
        try:
            kw = {}
            if os.name == "nt":
                kw["creationflags"] = 0x08000000                  # CREATE_NO_WINDOW
            env = dict(os.environ, PYTHONUNBUFFERED="1", PYTHONIOENCODING="utf-8")
            p = subprocess.Popen(self.command(), stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                 stderr=subprocess.STDOUT, env=env, **kw)
        except Exception as e:
            self.last_error = str(e)
            self.log.append("[app] backend could not start: %s" % e)
            return
        self.proc = p
        threading.Thread(target=self._pump, args=(p,), name="isai-log", daemon=True).start()

    def _pump(self, p):
        try:
            for raw in p.stdout:
                self.log.append(raw.decode("utf-8", "replace").rstrip())
        except Exception:
            pass
        code = p.wait()
        self.log.append("[app] backend exited (code %s)" % code)

    def _kill(self):
        p = self.proc
        if not p or p.poll() is not None:
            return
        try:
            p.stdin.close()                                       # the child exits when stdin closes
        except Exception:
            pass
        try:
            p.wait(5)
            return
        except Exception:
            pass
        try:
            p.terminate()
            p.wait(3)
        except Exception:
            try:
                if os.name == "nt":
                    subprocess.run(["taskkill", "/F", "/T", "/PID", str(p.pid)], capture_output=True,
                                   creationflags=0x08000000)
                else:
                    p.kill()
            except Exception:
                pass

    def stop(self):
        self.wanted = False
        self.state = "stopped"
        self.log.append("[app] stopping backend")
        self._kill()

    def restart(self, reason):
        with self.lock:
            if self.busy or not self.wanted:
                return
            self.busy = True
        try:
            self.restarts += 1
            self.state = "restarting"
            self.log.append("[app] restarting backend: " + reason)
            self._kill()
            if self.wanted:
                self._launch()
        finally:
            self.busy = False

    def request_restart(self, reason):
        threading.Thread(target=self.restart, args=(reason,), daemon=True).start()

    def ping(self):
        try:
            with urllib.request.urlopen("http://127.0.0.1:%d/__isai_ping" % self.port, timeout=4) as r:
                return r.status == 200
        except Exception:
            return False

    def backend_info(self):
        """JSON the page reads once at load: where the local backend is and its api version."""
        if self.info:
            return self.info
        if not self.ping():
            return ""
        api = 0
        try:
            with urllib.request.urlopen("http://127.0.0.1:%d/health" % self.port, timeout=4) as r:
                api = int(json.loads(r.read().decode("utf-8")).get("api_version", 0))
        except Exception:
            pass
        self.info = json.dumps({"url": "http://127.0.0.1:%d" % self.port, "api": api})
        return self.info

    def logs_json(self, after):
        seq, lines = self.log.since(after)
        return json.dumps({"seq": seq, "state": self.state, "restarts": self.restarts, "lines": lines})

    def _watch(self):
        fails = crashes = 0
        ok_since = 0.0
        while self.wanted:
            time.sleep(1 if self.state == "starting" else self.CHECK)
            if not self.wanted:
                return
            if self.busy:
                fails = 0
                continue
            if self.proc is None or self.proc.poll() is not None:     # exited or never started
                wait = min(60, 5 << min(crashes, 4))
                crashes += 1
                self.log.append("[app] backend is not running; restarting in %d s" % wait)
                self.state = "restarting"
                time.sleep(wait)
                self.restart("backend process exited")
                fails = 0
                ok_since = 0.0
                continue
            if self.ping():
                if self.state != "running":
                    self.log.append("[app] backend is up")
                self.state = "running"
                fails = 0
                ok_since = ok_since or time.time()
                if time.time() - ok_since > 120:
                    crashes = 0                                       # stable: reset the back-off
                continue
            ok_since = 0.0
            if time.time() - self.launched_at < self.GRACE:
                continue
            fails += 1
            self.state = "unresponsive"
            self.log.append("[app] backend not answering (%d/%d)" % (fails, self.MAX_FAILS))
            if fails >= self.MAX_FAILS:
                self.restart("backend stopped answering")
                fails = 0


# ============================================================ injected into the page (before its own scripts)

SHIM = r"""<script>/* isai-desktop shim: IsaiNative for Windows */
(function(){
  if (window.IsaiNative) return;
  function x(m, u, body){
    try { var r = new XMLHttpRequest(); r.open(m, u, false); r.send(body == null ? null : body); return r.status === 200 ? r.responseText : ''; }
    catch (e) { return ''; }
  }
  function ext(u){ x('POST', '/__app/open?url=' + encodeURIComponent(u)); }

  /* keep the real Media Session so the Windows media overlay / media keys work */
  var ms = navigator.mediaSession, P = window.MediaSession && MediaSession.prototype, real = null;
  if (ms && P) {
    try {
      real = { meta: Object.getOwnPropertyDescriptor(P, 'metadata'), state: Object.getOwnPropertyDescriptor(P, 'playbackState'),
               pos: P.setPositionState, act: P.setActionHandler };
      ['play', 'pause', 'nexttrack', 'previoustrack'].forEach(function(n){
        try { real.act.call(ms, n, function(){ if (window.__isaiMedia) window.__isaiMedia(n); }); } catch (e) {}
      });
    } catch (e) { real = null; }
  }
  function media(json){
    if (!real) return;
    try {
      var o = JSON.parse(json), art = o.artData || o.art;
      if (o.t) real.meta.set.call(ms, new MediaMetadata({ title: o.t, artist: o.a || '', album: o.al || '', artwork: art ? [{ src: art }] : [] }));
      else real.meta.set.call(ms, null);
      real.state.set.call(ms, o.state === 'playing' || o.state === 'paused' ? o.state : 'none');
      if (o.dur > 0 && isFinite(o.dur) && o.pos >= 0 && o.pos <= o.dur) real.pos.call(ms, { duration: o.dur, position: o.pos, playbackRate: o.rate || 1 });
    } catch (e) {}
  }

  window.IsaiNative = {
    backendInfo: function(){ return x('GET', '/__app/info'); },
    serverLogs: function(after){ return x('GET', '/__app/logs?after=' + Math.floor(after || 0)); },
    restartServer: function(){ x('POST', '/__app/restart'); },
    hello: function(){},
    update: media,
    downloads: function(){},
    downloadStatus: function(){},
    saveFile: function(id, name, mime){
      fetch('/__app/save/open?id=' + encodeURIComponent(id) + '&name=' + encodeURIComponent(name || 'song') + '&mime=' + encodeURIComponent(mime || ''), { method: 'POST' })
        .then(function(r){ return r.json(); })
        .then(function(j){ if (window.__isaiSaved) window.__isaiSaved(id, !!j.ok, j.msg || ''); })
        .catch(function(){ if (window.__isaiSaved) window.__isaiSaved(id, false, 'Couldn\u2019t open the save dialog'); });
    },
    saveChunk: function(id, b64){ return x('POST', '/__app/save/chunk?id=' + encodeURIComponent(id), b64) === '1'; },
    saveEnd: function(id, ok){ return x('POST', '/__app/save/end?id=' + encodeURIComponent(id) + '&ok=' + (ok ? '1' : '0')) === '1'; }
  };

  /* links to other sites open in the default browser, not inside the app window */
  function foreign(u){ return (u.protocol === 'http:' || u.protocol === 'https:') && u.origin !== location.origin && u.hostname !== '127.0.0.1'; }
  document.addEventListener('click', function(e){
    var a = e.target && e.target.closest && e.target.closest('a[href]'); if (!a || a.hasAttribute('download')) return;
    var u; try { u = new URL(a.href, location.href); } catch (err) { return; }
    if (foreign(u)) { e.preventDefault(); ext(u.href); }
  }, true);
  var wo = window.open;
  window.open = function(u){
    try { var p = new URL(u, location.href); if (foreign(p)) { ext(p.href); return null; } } catch (e) {}
    return wo.apply(window, arguments);
  };
})();
</script>"""

LOGO = "https://thirai.uk/static/thiraiwhite.png"

SPLASH = """<!doctype html><meta charset="utf-8"><title>Isai</title>
<style>html,body{height:100%;margin:0;background:#0A0A0B;color:#fff;font:600 26px system-ui,Segoe UI,sans-serif}
body{display:grid;place-items:center}
.f{opacity:0;animation:bootfade 1.8s ease-in-out infinite}
img.f{height:34px;width:auto;max-width:60vw;object-fit:contain}
@keyframes bootfade{0%,100%{opacity:0;transform:scale(.97)}50%{opacity:1;transform:scale(1)}}</style>
<img class="f" src="@LOGO@" alt="Thirai" onerror="this.outerHTML='<div class=&quot;f&quot;>Thirai</div>'">
<script>
(function poll(){
  fetch('/__app/ready').then(function(r){return r.json();}).then(function(j){
    if (j.ready) { location.replace('/'); return; }
    setTimeout(poll, 400);
  }).catch(function(){ setTimeout(poll, 600); });
})();
</script>""".replace("@LOGO@", LOGO)

# Same logo fade, shown over the page itself until the app has decided between sign-in and home.
BOOT = """<style>#boot{position:fixed;inset:0;z-index:100000;display:flex;align-items:center;justify-content:center;background:#0a0a0b;transition:opacity .45s ease}
#boot.out{opacity:0;pointer-events:none}
#boot img{height:34px;width:auto;max-width:60vw;object-fit:contain;opacity:0;animation:bootfade 1.8s ease-in-out infinite}
@keyframes bootfade{0%,100%{opacity:0;transform:scale(.97)}50%{opacity:1;transform:scale(1)}}</style>
<script>(function(){function h(){var b=document.getElementById('boot');if(!b||b.__h)return;b.__h=1;
var w=Math.max(0,1200-performance.now());setTimeout(function(){b.classList.add('out');setTimeout(function(){b.remove()},500)},w)}
var t=setInterval(function(){if(typeof window.__unlocked!=='undefined'){clearInterval(t);h()}},100);setTimeout(h,10000);
document.addEventListener('DOMContentLoaded',function(){if(!document.getElementById('boot')){var d=document.createElement('div');d.id='boot';
d.innerHTML='<img src="@LOGO@" alt="Thirai">';document.body.appendChild(d)}})})();</script>""".replace("@LOGO@", LOGO)


# ============================================================ local UI server

def _bundled_assets_dir():
    for p in (os.path.join(RES, "assets"),
              os.path.join(HERE, "..", "app", "src", "main", "assets"),
              os.path.join(HERE, "assets")):
        if os.path.isfile(os.path.join(p, "index.html")):
            return os.path.abspath(p)
    return None


CACHE_FILE = os.path.join(DATA_DIR, "index.html")


def has_hooks(html):
    return all(k in html for k in MARKERS)


def fetch_live(timeout=4):
    """The latest page from isai.thirai.uk, or None if offline, unreachable or not the app-ready page."""
    try:
        req = urllib.request.Request(SITE + "/", headers={"User-Agent": "Isai-Desktop", "Cache-Control": "no-cache"})
        with urllib.request.urlopen(req, timeout=timeout) as r:
            live = r.read().decode("utf-8", "replace")
    except Exception:
        return None
    return live if has_hooks(live) else None       # never save an error / captive-portal / hook-less page


def read_cache():
    try:
        with open(CACHE_FILE, encoding="utf-8") as f:
            html = f.read()
        return html if has_hooks(html) else None
    except OSError:
        return None


def save_cache(html):
    try:
        os.makedirs(DATA_DIR, exist_ok=True)
        tmp = CACHE_FILE + ".tmp"
        with open(tmp, "w", encoding="utf-8", newline="") as f:
            f.write(html)
        os.replace(tmp, CACHE_FILE)
    except OSError:
        pass


class SaveState:
    """One 'Save as' at a time, like MediaBridge.java."""
    def __init__(self):
        self.lock = threading.Lock()
        self.id = None
        self.fh = None
        self.path = None

    def close(self, discard):
        with self.lock:
            fh, path = self.fh, self.path
            self.fh = self.path = self.id = None
        if fh:
            try:
                fh.close()
            except Exception:
                pass
        if discard and path:
            try:
                os.remove(path)
            except Exception:
                pass


class App:
    def __init__(self, sup, headless=False):
        self.sup = sup
        self.headless = headless
        self.started = time.time()
        self.save = SaveState()
        self.assets = _bundled_assets_dir()
        self.page = read_cache()                           # last live page, for offline

    def pick_save_path(self, name):
        if os.environ.get("ISAI_TEST_SAVE_PATH"):          # headless tests have no dialog
            return os.environ["ISAI_TEST_SAVE_PATH"]
        import webview
        music = os.path.join(os.path.expanduser("~"), "Music")
        kind = webview.FileDialog.SAVE if hasattr(webview, "FileDialog") else webview.SAVE_DIALOG
        r = webview.windows[0].create_file_dialog(
            kind, directory=music if os.path.isdir(music) else os.path.expanduser("~"), save_filename=name)
        if not r:
            return None
        return r if isinstance(r, str) else r[0]


def refresh_loop(app):
    """Every 2 minutes while online: pick up a new page and tell the window it is ready."""
    while True:
        time.sleep(120)
        html = fetch_live(8)
        if html is None or html == app.page:
            continue
        app.page = html
        save_cache(html)
        app.sup.log.append("[app] page updated from the live site")
        if not app.headless:
            try:
                import webview
                webview.windows[0].evaluate_js("try{toast('Update ready - restart Isai to apply')}catch(e){}")
            except Exception:
                pass


def make_handler(app):
    class H(http.server.BaseHTTPRequestHandler):
        protocol_version = "HTTP/1.1"
        server_version = "Isai"

        def log_message(self, *a):
            pass

        def send(self, code, body=b"", ctype="text/plain; charset=utf-8", extra=None):
            if isinstance(body, str):
                body = body.encode("utf-8")
            self.send_response(code)
            self.send_header("Content-Type", ctype)
            self.send_header("Content-Length", str(len(body)))
            self.send_header("Cache-Control", "no-store")
            for k, v in (extra or []):
                self.send_header(k, v)
            self.end_headers()
            if self.command != "HEAD":
                self.wfile.write(body)

        def body(self):
            n = int(self.headers.get("Content-Length") or 0)
            return self.rfile.read(n) if n else b""

        def route(self):
            u = urllib.parse.urlsplit(self.path)
            return u.path, dict(urllib.parse.parse_qsl(u.query))

        def do_HEAD(self):
            self.do_GET()

        def do_GET(self):
            path, q = self.route()
            if path.startswith("/__app/"):
                return self.app_get(path, q)
            if path in ("/", "/index.html"):
                return self.index()
            self.proxy(path)

        def do_POST(self):
            path, q = self.route()
            if not path.startswith("/__app/"):
                return self.send(404)
            self.app_post(path, q)

        def app_get(self, path, q):
            s = app.sup
            if path == "/__app/ping":
                return self.send(200, "isai")
            if path == "/__app/splash":
                return self.send(200, SPLASH, "text/html; charset=utf-8")
            if path == "/__app/ready":
                ready = s.ping() or bool(s.last_error) or time.time() - app.started > 25
                if ready:
                    s.backend_info()                 # cache it before the page asks
                return self.send(200, json.dumps({"ready": ready, "error": s.last_error or ""}), "application/json")
            if path == "/__app/info":
                return self.send(200, s.backend_info(), "application/json")
            if path == "/__app/logs":
                try:
                    after = int(q.get("after", "0"))
                except ValueError:
                    after = 0
                return self.send(200, s.logs_json(after), "application/json")
            self.send(404)

        def app_post(self, path, q):
            s = app.sup
            if path == "/__app/restart":
                s.request_restart("requested from the app")
                return self.send(200, "ok")
            if path == "/__app/open":
                url = q.get("url", "")
                if url.startswith(("http://", "https://")):
                    try:
                        webbrowser.open(url)
                    except Exception:
                        pass
                return self.send(200, "ok")
            if path == "/__app/save/open":
                sv = app.save
                sv.close(True)
                name = os.path.basename(q.get("name") or "song") or "song"
                try:
                    dest = app.pick_save_path(name)
                    if not dest:
                        return self.send(200, json.dumps({"ok": False, "msg": "cancelled"}), "application/json")
                    fh = open(dest, "wb")
                    with sv.lock:
                        sv.id, sv.fh, sv.path = q.get("id"), fh, dest
                    return self.send(200, json.dumps({"ok": True}), "application/json")
                except Exception:
                    return self.send(200, json.dumps({"ok": False, "msg": "Couldn\u2019t create the file"}), "application/json")
            if path == "/__app/save/chunk":
                sv = app.save
                data = self.body()
                with sv.lock:
                    if not sv.fh or q.get("id") != sv.id:
                        return self.send(200, "0")
                    try:
                        sv.fh.write(base64.b64decode(data))
                        return self.send(200, "1")
                    except Exception:
                        pass
                sv.close(True)
                return self.send(200, "0")
            if path == "/__app/save/end":
                sv = app.save
                if not sv.fh or q.get("id") != sv.id:
                    return self.send(200, "0")
                sv.close(q.get("ok") != "1")
                return self.send(200, "1")
            self.send(404)

        def index(self):
            html = fetch_live()                              # online: always the latest page
            if html is not None:
                if html != app.page:
                    app.page = html
                    save_cache(html)                         # keep it for offline
            else:
                html = app.page or read_cache()              # offline: the last page we saw
                if html:
                    app.sup.log.append("[app] live site unavailable, using the saved copy")
            if html is None and app.assets:
                app.sup.log.append("[app] no saved copy yet, using the bundled copy")
                with open(os.path.join(app.assets, "index.html"), encoding="utf-8") as f:
                    html = f.read()
            if html is None:
                return self.send(502, "Isai could not load the site and has no offline copy.")
            m = re.search(r"<head[^>]*>", html, re.I)
            inject = SHIM + (BOOT if 'id="boot"' not in html else "")
            html = html[:m.end()] + inject + html[m.end():] if m else inject + html
            self.send(200, html, "text/html; charset=utf-8")

        def proxy(self, path):
            if re.search(r"(^|/)(sw|service-worker)\.js$", path):
                return self.send(404)               # no service worker: the page is served by this app
            qs = self.path.split("?", 1)[1] if "?" in self.path else ""
            try:
                req = urllib.request.Request(SITE + path + ("?" + qs if qs else ""),
                                             headers={"User-Agent": "Isai-Desktop", "Accept-Encoding": "identity"})
                with urllib.request.urlopen(req, timeout=20) as r:
                    data = r.read()
                    ctype = r.headers.get("Content-Type", "application/octet-stream")
                    extra = []
                    if r.headers.get("ETag"):
                        extra.append(("ETag", r.headers["ETag"]))
                    return self.send(r.status, data, ctype, extra)
            except urllib.error.HTTPError as e:
                return self.send(e.code)
            except Exception:
                pass
            if app.assets:                          # offline: serve what the bundle has (icons, ...)
                p = os.path.normpath(os.path.join(app.assets, path.lstrip("/")))
                if p.startswith(app.assets) and os.path.isfile(p):
                    import mimetypes
                    with open(p, "rb") as f:
                        return self.send(200, f.read(), mimetypes.guess_type(p)[0] or "application/octet-stream")
            self.send(404)

    return H


class Server(socketserver.ThreadingMixIn, http.server.HTTPServer):
    daemon_threads = True
    allow_reuse_address = False


def free_port(preferred):
    for p in (preferred, 0):
        try:
            with socket.socket() as s:
                s.bind(("127.0.0.1", p))
                return s.getsockname()[1]
        except OSError:
            continue
    raise RuntimeError("no free port")


def another_instance_running():
    try:
        with urllib.request.urlopen("http://127.0.0.1:%d/__app/ping" % UI_PORT, timeout=1.5) as r:
            return r.read() == b"isai"
    except Exception:
        return False


def fatal(msg):
    try:
        import ctypes
        ctypes.windll.user32.MessageBoxW(0, msg, "Isai", 0x10)
    except Exception:
        print(msg, file=sys.stderr)


# ============================================================ main

def main():
    argv = sys.argv[1:]
    if "--backend" in argv:
        port = int(argv[argv.index("--port") + 1]) if "--port" in argv else BACKEND_PORT
        return run_backend(port)

    headless = os.environ.get("ISAI_HEADLESS") == "1"
    if another_instance_running():
        if not headless:
            fatal("Isai is already running.")
        return

    log = Log()
    log.init(os.path.join(DATA_DIR, "server.log"))
    sup = Supervisor(free_port(BACKEND_PORT), log)
    sup.start()

    app = App(sup, headless)
    threading.Thread(target=refresh_loop, args=(app,), name="isai-refresh", daemon=True).start()
    ui_port = free_port(UI_PORT)
    server = Server(("127.0.0.1", ui_port), make_handler(app))
    threading.Thread(target=server.serve_forever, name="isai-ui", daemon=True).start()
    url = "http://127.0.0.1:%d/__app/splash" % ui_port
    if ui_port != UI_PORT:
        log.append("[app] port %d was busy, using %d (saved settings may not carry over)" % (UI_PORT, ui_port))

    if headless:
        print("UI", url, flush=True)
        try:
            while True:
                time.sleep(3600)
        except KeyboardInterrupt:
            pass
        sup.stop()
        return

    # let the page play audio without a click, like the Android WebView setting
    os.environ.setdefault("WEBVIEW2_ADDITIONAL_BROWSER_ARGUMENTS", "--autoplay-policy=no-user-gesture-required")
    try:
        import webview
        window = webview.create_window("Isai", url, width=1280, height=820, min_size=(900, 600),
                                       background_color="#0A0A0B")
        window.events.closed += lambda: sup.stop()
        webview.start(private_mode=False, storage_path=os.path.join(DATA_DIR, "webview"),
                      debug=os.environ.get("ISAI_DEBUG") == "1")
    except Exception as e:
        log.append("[app] window failed: %r" % (e,))
        fatal("Isai couldn\u2019t open its window.\n\nIt needs the Microsoft Edge WebView2 Runtime "
              "(built into Windows 11). Install it from:\nhttps://developer.microsoft.com/microsoft-edge/webview2/\n\n%s" % e)
    finally:
        sup.stop()
        server.shutdown()


if __name__ == "__main__":
    main()
