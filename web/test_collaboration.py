#!/usr/bin/env python3
"""Exercise two stale-base clients against the real Lean collaboration process."""
import json
import os
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
EXE = os.environ.get(
    "OT_COLLAB_EXE",
    os.path.join(ROOT, ".lake", "build", "bin", "ot-collab.exe"),
)


def main():
    if not os.path.exists(EXE):
        sys.exit(f"collaboration backend not found: {EXE}")
    proc = subprocess.Popen(
        [EXE], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
        stderr=subprocess.PIPE, text=True, bufsize=1
    )

    def call(message):
        proc.stdin.write(json.dumps(message) + "\n")
        proc.stdin.flush()
        line = proc.stdout.readline()
        if not line:
            raise AssertionError("Lean collaboration process exited unexpectedly")
        response = json.loads(line)
        if not response.get("ok"):
            raise AssertionError(response.get("error", response))
        return response

    try:
        initial = call({"cmd": "state"})
        assert initial["rev"] == 0
        assert len(initial["doc"]) >= 3

        # Both clients edit revision zero. The second request is intentionally
        # stale and must be transformed over the first by CollaborationServer.
        alice = call({
            "cmd": "replace", "baseRevision": 0,
            "clientId": "alice", "requestId": "alice-1",
            "from": {"block": 0, "offset": 0},
            "to": {"block": 0, "offset": 0}, "text": "A"
        })
        bob = call({
            "cmd": "replace", "baseRevision": 0,
            "clientId": "bob", "requestId": "bob-1",
            "from": {"block": 2, "offset": 0},
            "to": {"block": 2, "offset": 0}, "text": "B"
        })
        assert alice["rev"] == 1
        assert bob["rev"] == 2
        assert bob["doc"][0]["text"].startswith("A")
        assert bob["doc"][2]["text"].startswith("B")

        final = call({"cmd": "state"})
        assert final["rev"] == 2
        assert final["doc"] == bob["doc"]
        print("collaboration integration: two stale-base clients converged at revision 2")
    finally:
        proc.terminate()
        proc.wait(timeout=5)


if __name__ == "__main__":
    main()
