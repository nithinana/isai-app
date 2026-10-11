"""Starts your FastAPI backend (backend.py) inside the app on 127.0.0.1."""
import os


class _PrivateNetwork:
    """Lets the https UI call http://127.0.0.1 (Chrome's Private Network Access rule)."""
    def __init__(self, app):
        self.app = app

    async def __call__(self, scope, receive, send):
        if scope["type"] != "http":
            return await self.app(scope, receive, send)

        async def wrapped(msg):
            if msg["type"] == "http.response.start":
                msg["headers"] = list(msg.get("headers") or []) + [(b"access-control-allow-private-network", b"true")]
            await send(msg)

        await self.app(scope, receive, wrapped)


def start(port=8765):
    # No Node/Deno on a phone: use clients that need no JS challenge solving.
    os.environ.setdefault("YTDLP_FAST_CLIENT", "android_vr")
    os.environ.setdefault("YTDLP_AUDIO_CLIENTS", "android_vr;tv;mweb;web_safari")
    os.environ.setdefault("YTDLP_REMOTE_COMPONENTS", "")
    os.environ.setdefault("PUBLIC_URL", f"http://127.0.0.1:{port}")
    import backend
    import uvicorn
    cfg = uvicorn.Config(_PrivateNetwork(backend.app), host="127.0.0.1", port=port,
                         log_level="warning", loop="asyncio", http="h11", lifespan="on")
    uvicorn.Server(cfg).run()
