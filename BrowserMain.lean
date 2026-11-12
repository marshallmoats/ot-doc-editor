/-!
# Browser-side OT smoke test

This entry point runs the existing Lean session and edit builders in the browser.
The first milestone deliberately reuses Main's pure editor logic; the next extraction
will move Session and the edit builders into an IO-free Editor.Core module.
-/

import Editor.Core
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

def documentText (s : Session) : String :=
  String.intercalate "\n\n" (s.doc.map fun b => String.mk b.text)

def view (s : Session) : Html Msg :=
  html! <main>
    <h1>Lean OT engine running in WebAssembly</h1>
    <p>This page applies edits, undo, and redo using the existing verified Lean session.</p>
    <pre>{documentText s}</pre>
    <button onClick={Msg.append}>Append !</button>
    <button onClick={Msg.undo}>Undo</button>
    <button onClick={Msg.redo}>Redo</button>
  </main>

def main : IO Unit :=
  (App.sandbox (Session.init initialDoc) update view).run
