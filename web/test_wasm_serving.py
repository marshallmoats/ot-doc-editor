#!/usr/bin/env python3
"""Smoke-test the generated Lean/WASM browser asset serving and mount bootstrap."""

import os
import sys
import threading
from http.server import ThreadingHTTPServer
from urllib.request import urlopen

WEB_DIR = os.path.dirname(os.path.abspath(__file__))
ROOT_DIR = os.path.dirname(WEB_DIR)
DIST_DIR = os.path.join(ROOT_DIR, "dist")
sys.path.insert(0, WEB_DIR)

from server import make_handler  # noqa: E402


def main():
    loaders = sorted(
        name for name in os.listdir(DIST_DIR)
        if name.startswith("app.") and name.endswith(".js")
    )
    wasm = sorted(
        name for name in os.listdir(DIST_DIR)
        if name.startswith("app.") and name.endswith(".wasm")
    )
    assert loaders, "lasm build did not produce an app JavaScript loader"
    assert wasm, "lasm build did not produce a WebAssembly module"

    httpd = ThreadingHTTPServer(("127.0.0.1", 0), make_handler(None, None))
    thread = threading.Thread(target=httpd.serve_forever, daemon=True)
    thread.start()
    base = f"http://127.0.0.1:{httpd.server_address[1]}"
    try:
        with urlopen(base + "/") as response:
            html = response.read().decode("utf-8")
        assert f'import {{ mount }} from "/dist/{loaders[-1]}"' in html
        assert 'window.__leanBridgeReady' in html
        assert 'snapshot-request' in html

        with urlopen(base + "/dist/" + loaders[-1]) as response:
            assert response.status == 200
            assert "javascript" in response.headers.get("Content-Type", "")

        with urlopen(base + "/dist/" + wasm[-1]) as response:
            assert response.status == 200
            assert response.headers.get("Content-Type") == "application/wasm"
    finally:
        httpd.shutdown()
        thread.join(timeout=2)
        httpd.server_close()

    print("browser WASM serving and Lasm mount bootstrap passed")


if __name__ == "__main__":
    main()
