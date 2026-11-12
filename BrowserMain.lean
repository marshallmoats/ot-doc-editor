/-
# Browser/WebAssembly demonstration

The interactive panel uses the shared Lean editor session for local edits,
validation, undo, and redo. The second panel runs the revisioned collaboration
server smoke scenario in Lean: two clients submit edits against revision zero,
and the server transforms the second edit over the first.
-/

import Editor.Collaboration.Server
import Lasm.UI

open OT
open Lasm.UI

inductive Msg where
  | append
  | undo
  | redo

def appendBang (s : Session) : Session :=
  match s.doc.getLast? with
  | none => s
  | some b =>
    let i := s.doc.length - 1
    match replaceOps s.doc i b.text.length i b.text.length "!" with
    | none => s
    | some e =>
      if h : ValidSeq e s.doc then s.commit e h else s

def update : Msg → Session → Session
  | .append, s => appendBang s
  | .undo, s =>
      match s.undo with
      | some (s', _) => s'
      | none => s
  | .redo, s =>
      match s.redo with
      | some (s', _) => s'
      | none => s

def documentText (d : BDoc) : String :=
  String.intercalate "\n\n" (d.map fun b => String.mk b.text)

def view (s : Session) : Html Msg :=
  html! <main>
    <h1>Verified OT editor</h1>
    <p>Lean 4 running in WebAssembly. Every interactive edit is checked by the shared Lean document model.</p>
    <h2>Interactive editor</h2>
    <pre>{documentText s.doc}</pre>
    <button onClick={Msg.append}>Append !</button>
    <button onClick={Msg.undo}>Undo</button>
    <button onClick={Msg.redo}>Redo</button>
    <h2>Two-client collaboration replay</h2>
    <p>Both edits start at revision 0. The server accepts the first, transforms the stale second edit, and serializes both.</p>
    <p>{s!"Server revision: {CollaborationServer.revision collaborationServerSmoke}"}</p>
    <pre>{documentText collaborationServerSmoke.srv.doc}</pre>
    <p>This is an in-browser deterministic server-core demonstration, not a live network session.</p>
  </main>

def main : IO Unit :=
  (App.sandbox (Session.init initialDoc) update view).run
