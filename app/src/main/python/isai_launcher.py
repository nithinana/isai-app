"""Starts your FastAPI backend (backend.py) inside the app on 127.0.0.1.

Everything the backend prints / logs is forwarded to the app's in-app server log (ServerLog.java).
start() blocks until the server exits; stop() asks it to exit so ServerService can restart it.
"""
import os
import sys
import threading
import traceback

_server = None
_lock = threading.Lock()
_stream_installed = False


def _emit(line):
    try:
        from java import jclass
        jclass("uk.thirai.isai.ServerLog").append(line)
    except Exception:
        pass


class _LogStream:
    """File-like object that turns writes into log lines."""
    encoding = "utf-8"

    def __init__(self, tag=""):
        self._buf = ""
        self._tag = tag

    def write(self, s):
        if not isinstance(s, str):
            s = s.decode("utf-8", "replace")
        self._buf += s
        while "\n" in self._buf:
            line, self._buf = self._buf.split("\n", 1)
            if line.strip():
                _emit(self._tag + line)
        return len(s)

    def flush(self):
        if self._buf.strip():
            _emit(self._tag + self._buf)
        self._buf = ""

    def isatty(self):
        return False

    def fileno(self):
        raise OSError("no fileno")


def _install_streams():
    global _stream_installed
    if _stream_installed:
        return
    _stream_installed = True
    sys.stdout = _LogStream()
    sys.stderr = _LogStream()


class _PrivateNetwork:
    """Lets the https UI call http://127.0.0.1 (Chrome's Private Network Access rule).

    Also answers /__isai_ping directly on the event loop (no thread pool, no backend code), so the
    app's watchdog can tell a hung server from a busy one."""
    def __init__(self, app):
        self.app = app

    async def __call__(self, scope, receive, send):
        if scope["type"] != "http":
            return await self.app(scope, receive, send)

        if scope.get("path") == "/__isai_ping":
            await send({"type": "http.response.start", "status": 200,
                        "headers": [(b"content-type", b"text/plain"), (b"content-length", b"2")]})
            await send({"type": "http.response.body", "body": b"ok"})
            return

        async def wrapped(msg):
            if msg["type"] == "http.response.start":
                msg["headers"] = list(msg.get("headers") or []) + [(b"access-control-allow-private-network", b"true")]
            await send(msg)

        await self.app(scope, receive, wrapped)


def start(port=8765):
    """Blocks while the server runs. Never raises: problems are written to the log instead."""
    global _server
    _install_streams()
    try:
        # No Node/Deno on a phone: use clients that need no JS challenge solving.
        os.environ.setdefault("YTDLP_FAST_CLIENT", "android_vr")
        os.environ.setdefault("YTDLP_AUDIO_CLIENTS", "android_vr;tv;mweb;web_safari")
        os.environ.setdefault("YTDLP_REMOTE_COMPONENTS", "")
        os.environ.setdefault("PUBLIC_URL", f"http://127.0.0.1:{port}")
        import backend
        import uvicorn
        cfg = uvicorn.Config(_PrivateNetwork(backend.app), host="127.0.0.1", port=port,
                             log_level="info", access_log=False,
                             loop="asyncio", http="h11", lifespan="on")
        srv = uvicorn.Server(cfg)
        with _lock:
            _server = srv
        srv.run()
        print("[launcher] server stopped", flush=True)
    except BaseException:
        print("[launcher] server crashed:\n" + traceback.format_exc(), flush=True)
    finally:
        with _lock:
            _server = None


def stop():
    """Ask the running server to shut down (returns immediately)."""
    with _lock:
        srv = _server
    if srv is not None:
        srv.should_exit = True
        return True
    return False
