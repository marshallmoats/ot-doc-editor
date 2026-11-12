/-
# Lean-owned browser collaboration model

This WebAssembly app exercises the same proof-carrying ClientState used by the
native Lean model. Browser-side code is only the Lasm UI shell: edits,
application, rebasing, and acknowledgement all execute in Lean.
-/

import Editor.Collaboration.Server
import Lasm.UI

open OT
open Lasm.UI

inductive Msg where
  | append
  | undo
  | redo
  | localInsert
  | remoteInsert
  | acknowledge

abbrev AppState := Session × ClientState

def appendBang (s : Session) : Session :=
  match s.doc.getLast? with
  | none => s
  | some b =>
    let i := s.doc.length - 1
    match replaceOps s.doc i b.text.length i b.text.length "!" with
    | none => s
    | some e =>
      if h : ValidSeq e s.doc then s.commit e h else s

/-- A browser-local edit enters the Lean pending queue immediately. -/
def clientLocalInsert (c : ClientState) : ClientState :=
  let e : BOps := [.blk 0 (.inl (.ins 0 '!'))]
  if h : ValidSeq e c.doc then c.applyLocal e h else c

/-- Simulate a concurrent peer edit expressed against the confirmed snapshot. -/
def clientRemoteInsert (c : ClientState) : ClientState :=
  let e : BOps := [.blk 0 (.inl (.ins 0 '?'))]
  if h : ValidSeq e c.confirmedDoc then c.receiveRemote e h else c

/-- Acknowledge the complete pending prefix without replaying it into the
optimistic document. The Lean ClientState proof checks the prefix relation. -/
def clientAcknowledge (c : ClientState) : ClientState :=
  c.acknowledge c.pending [] (by simp)

def update : Msg → AppState → AppState
  | .append, (s, c) => (appendBang s, c)
  | .undo, (s, c) =>
      (match s.undo with | some (s', _) => s' | none => s, c)
  | .redo, (s, c) =>
      (match s.redo with | some (s', _) => s' | none => s, c)
  | .localInsert, (s, c) => (s, clientLocalInsert c)
  | .remoteInsert, (s, c) => (s, clientRemoteInsert c)
  | .acknowledge, (s, c) => (s, clientAcknowledge c)

def documentText (d : BDoc) : String :=
  String.intercalate "\\n\\n" (d.map fun b => String.mk b.text)

def view (state : AppState) : Html Msg :=
  let (s, c) := state
  html! <main>
    <h1>Verified OT editor</h1>
    <p>Lean 4 running in WebAssembly. The UI dispatches messages; document operations and collaboration transformations execute in Lean.</p>
    <h2>Lean editor session</h2>
    <pre>{documentText s.doc}</pre>
    <button onClick={Msg.append}>Append !</button>
    <button onClick={Msg.undo}>Undo</button>
    <button onClick={Msg.redo}>Redo</button>
    <h2>Lean optimistic client state</h2>
    <p>Confirmed revision: {toString c.revision}</p>
    <p>Unacknowledged operations: {toString c.pending.length}</p>
    <pre>{documentText c.doc}</pre>
    <button onClick={Msg.localInsert}>Local edit (optimistic)</button>
    <button onClick={Msg.remoteInsert}>Concurrent remote edit</button>
    <button onClick={Msg.acknowledge}>Acknowledge pending edits</button>
    <h2>Server transformation smoke test</h2>
    <p>Two stale edits are serialized by the Lean collaboration server.</p>
    <p>{s!"Server revision: {CollaborationServer.revision collaborationServerSmoke}"}</p>
    <pre>{documentText collaborationServerSmoke.srv.doc}</pre>
  </main>

def main : IO Unit :=
  (App.sandbox (Session.init initialDoc, ClientState.init initialDoc) update view).run
