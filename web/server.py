#!/usr/bin/env python3
"""HTTP bridge for the verified editor and revisioned collaboration rooms.

Build with `lake build`, then run `python3 web/server.py`.
Rooms are in-memory demo rooms; the Lean process owns each room's revision log
and validates/transforms every submitted edit.
"""
import json
import os
import re
import subprocess
import sys
import threading
from collections import OrderedDict
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import parse_qs, urlsplit

ROOT = os.path.dirname(os.path.abspath(__file__))
BUILD = os.path.join(ROOT, "..", ".lake", "build", "bin")
EXE = os.environ.get("OT_EXE") or os.path.join(BUILD, "ot-editor.exe")
COLLAB_EXE = os.environ.get("OT_COLLAB_EXE") or os.path.join(BUILD, "ot-collab.exe")
MAX_BODY = 1 << 20
ROOM_RE = re.compile(r"^[A-Za-z0-9_-]{1,64}$")


class JsonLineProcess:
    """Synchronous, serialized access to one long-lived Lean JSON-lines process."""

    def __init__(self, exe):
        self.exe = exe
        self.lock = threading.Lock()
        self.proc = None
        self._start()

    def _start(self):
        self.proc = subprocess.Popen(
            [self.exe], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
            stderr=None, text=True, bufsize=1
        )

    def call(self, msg):
        line = json.dumps(msg, ensure_ascii=False)
        with self.lock:
            if self.proc.poll() is not None:
                self._start()
            self.proc.stdin.write(line + "\n")
            self.proc.stdin.flush()
            out = self.proc.stdout.readline()
        if not out:
            return {"ok": False, "error": "Lean backend exited"}
        try:
            return json.loads(out)
        except json.JSONDecodeError:
            return {"ok": False, "error": "invalid response from Lean backend"}


class Backend(JsonLineProcess):
    """Legacy single-user editor process."""


class CollaborationRoom(JsonLineProcess):
    """One in-memory room; Lean owns the authoritative revision and OT log."""

    def __init__(self, exe):
        super().__init__(exe)
        self.seen = OrderedDict()

    def submit(self, msg):
        key = (msg.get("clientId"), msg.get("requestId"))
        with self.lock:
            if key in self.seen:
                self.seen.move_to_end(key)
                return self.seen[key]
            if self.proc.poll() is not None:
                self._start()
            self.proc.stdin.write(json.dumps(msg, ensure_ascii=False) + "\n")
            self.proc.stdin.flush()
            out = self.proc.stdout.readline()
            if not out:
                result = {"ok": False, "error": "Lean collaboration backend exited"}
            else:
                try:
                    result = json.loads(out)
                except json.JSONDecodeError:
                    result = {"ok": False, "error": "invalid response from Lean collaboration backend"}
            if result.get("ok") and key[0] and key[1]:
                self.seen[key] = result
                while len(self.seen) > 2048:
                    self.seen.popitem(last=False)
            return result


class Rooms:
    def __init__(self, exe):
        self.exe = exe
        self.lock = threading.Lock()
        self.rooms = {}

    def get(self, name):
        if not ROOM_RE.fullmatch(name):
            raise ValueError("room must be 1-64 letters, numbers, '_' or '-'")
        with self.lock:
            room = self.rooms.get(name)
            if room is None:
                room = CollaborationRoom(self.exe)
                self.rooms[name] = room
            return room


def make_handler(backend, rooms):
    class Handler(BaseHTTPRequestHandler):
        def _send(self, code, body, ctype):
            data = body if isinstance(body, bytes) else body.encode("utf-8")
            self.send_response(code)
            self.send_header("Content-Type", ctype)
            self.send_header("Content-Length", str(len(data)))
            self.send_header("Cache-Control", "no-store")
            self.end_headers()
            self.wfile.write(data)

        def _json(self, code, value):
            self._send(code, json.dumps(value, ensure_ascii=False),
                       "application/json; charset=utf-8")

        def _read_json(self):
            n = int(self.headers.get("Content-Length", "0"))
            if n <= 0 or n > MAX_BODY:
                raise ValueError("bad request length")
            value = json.loads(self.rfile.read(n).decode("utf-8"))
            if not isinstance(value, dict):
                raise ValueError("expected a JSON object")
            return value

        def do_GET(self):
            parsed = urlsplit(self.path)
            if parsed.path in ("/", "/index.html"):
                with open(os.path.join(ROOT, "index.html"), "rb") as f:
                    return self._send(200, f.read(), "text/html; charset=utf-8")
            if parsed.path == "/collab":
                room_name = parse_qs(parsed.query).get("room", ["demo"])[0]
                try:
                    room = rooms.get(room_name)
                except ValueError as e:
                    return self._json(400, {"ok": False, "error": str(e)})
                return self._json(200, room.call({"cmd": "state"}))
            return self._send(404, "not found", "text/plain")

        def do_POST(self):
            parsed = urlsplit(self.path)
            if parsed.path not in ("/api", "/collab"):
                return self._send(404, "not found", "text/plain")
            try:
                msg = self._read_json()
            except Exception as e:
                return self._json(400, {"ok": False, "error": str(e)})
            if parsed.path == "/api":
                return self._json(200, backend.call(msg))
            room_name = msg.pop("room", "demo")
            try:
                room = rooms.get(room_name)
            except ValueError as e:
                return self._json(400, {"ok": False, "error": str(e)})
            return self._json(200, room.submit(msg))

        def log_message(self, fmt, *args):
            if os.environ.get("OT_VERBOSE"):
                super().log_message(fmt, *args)

    return Handler


def main():
    if not os.path.exists(EXE):
        sys.exit(f"backend not found at {EXE}\nbuild it first with `lake build`")
    if not os.path.exists(COLLAB_EXE):
        sys.exit(f"collaboration backend not found at {COLLAB_EXE}\nbuild it first with `lake build`")
    port = int(sys.argv[1]) if len(sys.argv) > 1 else 8000
    host = os.environ.get("OT_HOST", "127.0.0.1")
    server = ThreadingHTTPServer((host, port),
                                 make_handler(Backend(EXE), Rooms(COLLAB_EXE)))
    print(f"editor running at http://{host}:{server.server_address[1]}  (Ctrl+C to stop)")
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass


if __name__ == "__main__":
    main()
