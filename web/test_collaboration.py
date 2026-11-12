#!/usr/bin/env python3
"""Exercise two stale-base clients against the real Lean collaboration process."""
import json
import os
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
def collaboration_executable():
    configured = os.environ.get("OT_COLLAB_EXE")
    if configured:
        return configured
    build = os.path.join(ROOT, ".lake", "build", "bin")
    candidates = [os.path.join(build, "ot-collab"),
                  os.path.join(build, "ot-collab.exe")]
    return next((path for path in candidates if os.path.exists(path)), candidates[0])


EXE = collaboration_executable()


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
        assert final["canUndo"] is True
        assert final["canRedo"] is False

        undone = call({"cmd": "undo"})
        assert undone["rev"] == 3
        assert undone["doc"][0]["text"] == final["doc"][0]["text"]
        assert undone["doc"][2]["text"] == initial["doc"][2]["text"]
        assert undone["canUndo"] is True
        assert undone["canRedo"] is True

        redone = call({"cmd": "redo"})
        assert redone["rev"] == 4
        assert redone["doc"] == final["doc"]
        assert redone["canUndo"] is True
        assert redone["canRedo"] is False

        # The browser bridge submits operation batches produced by Lean. The
        # server returns the transformed accepted batch and all intervening
        # log entries so the Lean client can rebase before acknowledging.
        batch = [{
            "tag": "blk", "block": 1,
            "core": {"op": "ins", "offset": 0, "char": "X"}
        }]
        submitted = call({
            "cmd": "submitOps", "baseRevision": 4,
            "clientId": "alice", "requestId": "alice-batch-1",
            "ops": batch
        })
        assert submitted["rev"] == 5
        assert submitted["acceptedRevision"] == 5
        assert submitted["acceptedCount"] == 1
        assert submitted["acceptedEdit"] == batch
        assert submitted["changes"] == []
        since_four = call({"cmd": "state", "since": 4})
        assert since_four["changes"] == [batch]
        assert since_four["doc"] == submitted["doc"]

        later_batch = [{
            "tag": "blk", "block": 1,
            "core": {"op": "ins", "offset": 1, "char": "Y"}
        }]
        later = call({
            "cmd": "submitOps", "baseRevision": 5,
            "clientId": "bob", "requestId": "bob-batch-2",
            "ops": later_batch
        })
        assert later["rev"] == 6
        since_five = call({"cmd": "state", "since": 5})
        assert since_five["changes"] == [later_batch]

        print("collaboration integration: stale-base edits, shared undo/redo, revision-scoped logs, and Lean operation batches passed")
    finally:
        proc.terminate()
        proc.wait(timeout=5)


if __name__ == "__main__":
    main()
