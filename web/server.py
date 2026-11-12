#!/usr/bin/env python3
"""Tiny bridge: serves the page and forwards JSON requests to the verified Lean backend.

    lake build            # once, in the project root
    python3 web/server.py # then open http://127.0.0.1:8000

Standard library only. Binds to localhost.
"""
import json, os, subprocess, sys, threading
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

ROOT = os.path.dirname(os.path.abspath(__file__))
EXE = os.environ.get("OT_EXE") or os.path.join(ROOT, "..", ".lake", "build", "bin", "ot-editor.exe")
MAX_BODY = 1 << 20


class Backend:
    """One Lean process; requests are serialized (single-user session)."""

    def __init__(self, exe):
        self.exe = exe
        self.lock = threading.Lock()
        self.proc = None
        self._start()

    def _start(self):
        self.proc = subprocess.Popen([self.exe], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                     text=True, bufsize=1)

    def call(self, msg):
        line = json.dumps(msg, ensure_ascii=False)  # json.dumps never emits a raw newline
        with self.lock:
            if self.proc.poll() is not None:
                self._start()
            self.proc.stdin.write(line + "\n")
            self.proc.stdin.flush()
            out = self.proc.stdout.readline()
        if not out:
            return {"ok": False, "error": "backend exited"}
        return json.loads(out)


def make_handler(backend):
    class Handler(BaseHTTPRequestHandler):
        def _send(self, code, body, ctype):
            data = body if isinstance(body, bytes) else body.encode("utf-8")
            self.send_response(code)
            self.send_header("Content-Type", ctype)
            self.send_header("Content-Length", str(len(data)))
            self.send_header("Cache-Control", "no-store")
            self.end_headers()
            self.wfile.write(data)

        def do_GET(self):
            if self.path in ("/", "/index.html"):
                with open(os.path.join(ROOT, "index.html"), "rb") as f:
                    self._send(200, f.read(), "text/html; charset=utf-8")
            else:
                self._send(404, "not found", "text/plain")

        def do_POST(self):
            if self.path != "/api":
                return self._send(404, "not found", "text/plain")
            try:
                n = int(self.headers.get("Content-Length", "0"))
                if n <= 0 or n > MAX_BODY:
                    raise ValueError("bad length")
                msg = json.loads(self.rfile.read(n).decode("utf-8"))
                if not isinstance(msg, dict):
                    raise ValueError("expected an object")
            except Exception as e:  # malformed request
                return self._send(400, json.dumps({"ok": False, "error": str(e)}), "application/json")
            self._send(200, json.dumps(backend.call(msg), ensure_ascii=False), "application/json; charset=utf-8")

        def log_message(self, fmt, *args):
            if os.environ.get("OT_VERBOSE"):
                super().log_message(fmt, *args)

    return Handler


def main():
    if not os.path.exists(EXE):
        sys.exit(f"backend not found at {EXE}\nbuild it first with `lake build`")
    port = int(sys.argv[1]) if len(sys.argv) > 1 else 8000
    srv = ThreadingHTTPServer(("127.0.0.1", port), make_handler(Backend(EXE)))
    print(f"editor running at http://127.0.0.1:{srv.server_address[1]}  (Ctrl+C to stop)")
    try:
        srv.serve_forever()
    except KeyboardInterrupt:
        pass


if __name__ == "__main__":
    main()
