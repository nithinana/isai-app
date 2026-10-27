# Isai for Windows

Desktop build of Isai: a WebView2 window around the Isai site, with the same Python backend the
Android app runs, started as a supervised child process (auto-restart, Server logs screen,
"Save as" dialog, media keys).

## Get it
Run the **Build Isai for Windows** workflow (Actions tab, or push). Download the `Isai-windows`
artifact, unzip, run `Isai\Isai.exe`. Needs the Edge WebView2 Runtime (built into Windows 11).

## Run from source (Windows)
    pip install -r windows/requirements.txt
    python windows/isai_desktop.py

## Live page and offline
The window shows the live https://isai.thirai.uk page, served through a small local server so the sign-in
and downloads stay in one place. Each load fetches the latest page and saves it to `%APPDATA%\Isai\index.html`.
Offline it opens that saved copy (the copy bundled in the app is used only before the first online launch).
While online the app also checks every 2 minutes and shows a toast when an update is ready (applied on restart).
The live page must contain the `isai-shim-v2` and `isai-serverlogs-v1` markers, otherwise it is ignored.

Settings, cookies and logs live in `%APPDATA%\Isai` (`server.log`, optional `cookies.txt`).

## Headless test (any OS)
    ISAI_HEADLESS=1 python windows/isai_desktop.py     # prints the UI url, no window
`ISAI_BACKEND_CMD` swaps in a stand-in backend; `ISAI_TEST_SAVE_PATH` skips the Save dialog.
