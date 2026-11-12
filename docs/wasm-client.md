# Browser/WebAssembly demo

The browser entry point is `BrowserMain.lean`. It runs the shared Lean editor
model in WebAssembly; the browser does not reimplement the OT/document logic in
JavaScript.

## Run the demo

Prerequisites: Node.js 24+, npm, and the Lean toolchain pinned in
`lean-toolchain`.

From the repository root:

```sh
npm install
npm run wasm:dev
```

Open the local URL printed by Lasm in your browser. The demo has two parts:

1. **Interactive editor:** append an edit, then undo and redo it. These actions
   execute the shared Lean `Session` and its validity checks in WebAssembly.
2. **Collaboration replay:** a deterministic Lean smoke scenario submits two
   edits from different clients against revision zero. The revisioned server
   transforms the stale second edit and displays the resulting revision-two
   document.

For a production bundle build:

```sh
npm run wasm:build
```

The GitHub Actions workflow builds both the Lean project and the browser
WebAssembly target on pushes and pull requests.

## Collaboration architecture and current boundary

`Editor/Collaboration.lean` provides a proof-carrying optimistic client state:

- a confirmed server document and revision;
- a pending local operation queue and optimistic document;
- remote operation rebasing using the verified `xformSeq` transformation;
- undo and redo history rebasing, with `ValidChain` proofs maintained;
- acknowledgement of a prefix of the pending queue without losing subsequent local edits.

`Editor/Collaboration/Server.lean` adds a transport-independent, revisioned
server boundary. It accepts edits against historical snapshots, transforms
them over intervening server log entries, preserves the server replay-validity
proof, and returns receipts carrying client/request identity and the new
revision.

**Important:** the collaboration replay in the browser is deterministic and
runs locally; it is not a live multi-user session. HTTP/WebSocket transport,
authentication, request de-duplication, persistence, remote delivery, remote
cursors, and two-browser convergence tests are still future work. Do not
present this milestone as a production-ready multi-user editor.
