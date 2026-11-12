/-
# Lean client bridge for the production contenteditable editor

The DOM editor sends edit intents over the Lasm port. This module constructs,
validates, applies, rebases, and acknowledges document operations. The browser
shell is responsible only for DOM/selection/IME and HTTP transport.
-/

import Editor.Collaboration.Server
import Lean.Data.Json
import Lasm.UI

open OT
open Lasm.UI

inductive BridgeMsg where
  | intent (raw : String)
  | acknowledge (raw : String)

def bridgeKindName : Kind → String
  | .para => "para"
  | .h1 => "h1"
  | .h2 => "h2"
  | .item => "item"
  | .quote => "quote"

def bridgeDocJson (d : BDoc) : Json :=
  Json.arr (d.map fun b =>
    Json.mkObj [
      ("kind", Json.str (bridgeKindName b.kind)),
      ("text", Json.str (String.ofList b.text))
    ]).toArray

def bridgeSnapshot (c : ClientState) : String :=
  (Json.mkObj [
    ("ok", Json.bool true),
    ("doc", bridgeDocJson c.doc),
    ("confirmedDoc", bridgeDocJson c.confirmedDoc),
    ("rev", toJson c.revision),
    ("pendingCount", toJson c.pending.length),
    ("canUndo", Json.bool (!c.undoStack.isEmpty)),
    ("canRedo", Json.bool (!c.redoStack.isEmpty))
  ]).compress

def bridgeParsePos (j : Json) (key : String) :
    Except String (Nat × Nat) := do
  let p ← j.getObjVal? key
  let block ← p.getObjValAs? Nat "block"
  let offset ← p.getObjValAs? Nat "offset"
  pure (block, offset)

def bridgeIntent (c : ClientState) (raw : String) : Option ClientState :=
  match Json.parse raw with
  | .error _ => none
  | .ok j =>
    match j.getObjValAs? String "cmd",
        bridgeParsePos j "from",
        bridgeParsePos j "to",
        j.getObjValAs? String "text" with
    | .ok "replace", .ok (i, p), .ok (k, q), .ok txt =>
      c.applyReplace i p k q txt
    | _, _, _, _ => none

def bridgeAckCount (raw : String) : Option Nat :=
  match Json.parse raw with
  | .error _ => none
  | .ok j =>
    match j.getObjValAs? Nat "acceptedCount" with
    | .ok n => some n
    | .error _ => none

def bridgeInit (_ : Unit) : ClientState × Cmd BridgeMsg :=
  let c := ClientState.init initialDoc
  (c, Cmd.port "snapshot" (.string (bridgeSnapshot c)))

def bridgeUpdate : BridgeMsg → ClientState → ClientState × Cmd BridgeMsg
  | .intent raw, c =>
    match bridgeIntent c raw with
    | none =>
      (c, Cmd.port "error" (.string "Lean rejected the edit intent"))
    | some next =>
      (next, Cmd.batch [
        Cmd.port "snapshot" (.string (bridgeSnapshot next)),
        Cmd.port "submit" (.string raw)
      ])
  | .acknowledge raw, c =>
    match bridgeAckCount raw with
    | none => (c, Cmd.port "error" (.string "Malformed acknowledgement"))
    | some count =>
      match c.acknowledgePrefixLength count with
      | none => (c, Cmd.port "error" (.string "Acknowledgement is not a pending prefix"))
      | some next =>
        (next, Cmd.port "snapshot" (.string (bridgeSnapshot next)))

def bridgeSubscriptions (_ : ClientState) : Subs BridgeMsg :=
  Subs.batch [
    Subs.port "intent" fun
      | .string raw => some (.intent raw)
      | _ => none,
    Subs.port "ack" fun
      | .string raw => some (.acknowledge raw)
      | _ => none
  ]

def bridgeView (_ : ClientState) : Html BridgeMsg :=
  html! <div></div>

def bridgeApp : App Unit ClientState BridgeMsg :=
  App.element bridgeInit bridgeUpdate bridgeView bridgeSubscriptions

def main : IO Unit :=
  bridgeApp.run
