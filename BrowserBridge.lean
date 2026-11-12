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
  | remote (raw : String)
  | acknowledge (raw : String)
  | snapshotRequest

def bridgeKindName : Kind → String
  | .para => "para"
  | .h1 => "h1"
  | .h2 => "h2"
  | .item => "item"
  | .quote => "quote"

def bridgeCoreJson : Core Char Kind → Json
  | .inl .nop => Json.mkObj [("op", Json.str "nop")]
  | .inl (.ins p ch) => Json.mkObj [
      ("op", Json.str "ins"), ("offset", toJson p),
      ("char", Json.str (String.singleton ch))]
  | .inl (.del p ch) => Json.mkObj [
      ("op", Json.str "del"), ("offset", toJson p),
      ("char", Json.str (String.singleton ch))]
  | .setK old next => Json.mkObj [
      ("op", Json.str "setKind"), ("old", Json.str (bridgeKindName old)),
      ("kind", Json.str (bridgeKindName next))]
  | .split p kind => Json.mkObj [
      ("op", Json.str "split"), ("offset", toJson p),
      ("kind", Json.str (bridgeKindName kind))]
  | .merge p kind => Json.mkObj [
      ("op", Json.str "merge"), ("offset", toJson p),
      ("kind", Json.str (bridgeKindName kind))]

def bridgeBOpJson : BOp Char Kind → Json
  | .nop => Json.mkObj [("tag", Json.str "nop")]
  | .blk block core => Json.mkObj [
      ("tag", Json.str "blk"), ("block", toJson block),
      ("core", bridgeCoreJson core)]

def bridgeOpsJson (ops : BOps) : Json :=
  Json.arr (ops.map bridgeBOpJson).toArray

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
    ("pendingOps", bridgeOpsJson c.pending),
    ("canUndo", Json.bool (!c.undoStack.isEmpty)),
    ("canRedo", Json.bool (!c.redoStack.isEmpty))
  ]).compress

def bridgeParsePos (j : Json) (key : String) :
    Except String (Nat × Nat) := do
  let p ← j.getObjVal? key
  let block ← p.getObjValAs? Nat "block"
  let offset ← p.getObjValAs? Nat "offset"
  pure (block, offset)

def bridgeKind? : String → Option Kind
  | "para" => some .para
  | "h1" => some .h1
  | "h2" => some .h2
  | "item" => some .item
  | "quote" => some .quote
  | _ => none

def bridgeChar? (j : Json) : Option Char := do
  let s ← (j.getObjValAs? String "char").toOption
  match s.toList with
  | [ch] => some ch
  | _ => none

def bridgeCore? (j : Json) : Option (Core Char Kind) := do
  let op ← (j.getObjValAs? String "op").toOption
  match op with
  | "nop" => some (.inl .nop)
  | "ins" =>
    let p ← (j.getObjValAs? Nat "offset").toOption
    let ch ← bridgeChar? j
    some (.inl (.ins p ch))
  | "del" =>
    let p ← (j.getObjValAs? Nat "offset").toOption
    let ch ← bridgeChar? j
    some (.inl (.del p ch))
  | "setKind" =>
    let oldText ← (j.getObjValAs? String "old").toOption
    let newText ← (j.getObjValAs? String "kind").toOption
    let old ← bridgeKind? oldText
    let next ← bridgeKind? newText
    some (.setK old next)
  | "split" =>
    let p ← (j.getObjValAs? Nat "offset").toOption
    let kindText ← (j.getObjValAs? String "kind").toOption
    let kind ← bridgeKind? kindText
    some (.split p kind)
  | "merge" =>
    let p ← (j.getObjValAs? Nat "offset").toOption
    let kindText ← (j.getObjValAs? String "kind").toOption
    let kind ← bridgeKind? kindText
    some (.merge p kind)
  | _ => none

def bridgeBOp? (j : Json) : Option (BOp Char Kind) := do
  let tag ← (j.getObjValAs? String "tag").toOption
  match tag with
  | "nop" => some .nop
  | "blk" =>
    let block ← (j.getObjValAs? Nat "block").toOption
    let coreJson ← (j.getObjVal? "core").toOption
    let core ← bridgeCore? coreJson
    some (.blk block core)
  | _ => none

def bridgeOps? (j : Json) : Option BOps :=
  match j with
  | .arr items => items.toList.mapM bridgeBOp?
  | _ => none

def bridgeChanges? (j : Json) : Option (List BOps) :=
  match j with
  | .arr items => items.toList.mapM bridgeOps?
  | _ => none

def bridgeRemote (c : ClientState) (raw : String) : Option ClientState := do
  let json ← (Json.parse raw).toOption
  let changes ← bridgeChanges? json
  changes.foldlM (fun state ops =>
    if h : ValidSeq ops state.confirmedDoc then
      some (state.receiveRemote ops h)
    else
      none) c

def bridgeIntent (c : ClientState) (raw : String) : Option ClientState :=
  match Json.parse raw with
  | .error _ => none
  | .ok j =>
    match j.getObjValAs? String "cmd" with
    | .ok "replace" =>
      match bridgeParsePos j "from", bridgeParsePos j "to",
          j.getObjValAs? String "text" with
      | .ok (i, p), .ok (k, q), .ok txt => c.applyReplace i p k q txt
      | _, _, _ => none
    | .ok "setKind" =>
      match j.getObjValAs? Nat "block", j.getObjValAs? String "kind" with
      | .ok block, .ok kindText =>
        match bridgeKind? kindText with
        | some kind => c.applySetKind block kind
        | none => none
      | _, _ => none
    | _ => none

def bridgeAckInfo (raw : String) : Option (BOps × Nat) :=
  match Json.parse raw with
  | .error _ => none
  | .ok j =>
    match j.getObjVal? "acceptedEdit",
        j.getObjValAs? Nat "acceptedRevision" with
    | .ok acceptedJson, .ok revision =>
      match bridgeOps? acceptedJson with
      | some accepted => some (accepted, revision)
      | none => none
    | _, _ => none

def bridgeInit (_ : Unit) : ClientState × Cmd BridgeMsg :=
  let c := ClientState.init initialDoc
  (c, Cmd.port "snapshot" (.string (bridgeSnapshot c)))

def bridgeUpdate : BridgeMsg → ClientState → ClientState × Cmd BridgeMsg
  | .intent raw, c =>
    match bridgeIntent c raw with
    | none =>
      (c, Cmd.port "error" (.string "Lean rejected the edit intent"))
    | some next =>
      (next, Cmd.port "snapshot" (.string (bridgeSnapshot next)))
  | .remote raw, c =>
    match bridgeRemote c raw with
    | none => (c, Cmd.port "error" (.string "Malformed or invalid remote change batch"))
    | some next => (next, Cmd.port "snapshot" (.string (bridgeSnapshot next)))
  | .snapshotRequest, c =>
    (c, Cmd.port "snapshot" (.string (bridgeSnapshot c)))
  | .acknowledge raw, c =>
    match bridgeAckInfo raw with
    | none => (c, Cmd.port "error" (.string "Malformed acknowledgement"))
    | some (accepted, revision) =>
      match c.acknowledgeAcceptedAt accepted revision with
      | none => (c, Cmd.port "error" (.string "Server acknowledgement does not match the pending prefix"))
      | some next =>
        (next, Cmd.port "snapshot" (.string (bridgeSnapshot next)))

def bridgeSubscriptions (_ : ClientState) : Subs BridgeMsg :=
  Subs.batch [
    Subs.port "intent" fun
      | .string raw => some (.intent raw)
      | _ => none,
    Subs.port "remote" fun
      | .string raw => some (.remote raw)
      | _ => none,
    Subs.port "ack" fun
      | .string raw => some (.acknowledge raw)
      | _ => none,
    Subs.port "snapshot-request" fun _ => some .snapshotRequest
  ]

def bridgeView (_ : ClientState) : Html BridgeMsg :=
  html! <div></div>

def bridgeApp : App Unit ClientState BridgeMsg :=
  App.element bridgeInit bridgeUpdate bridgeView bridgeSubscriptions

def main : IO Unit :=
  bridgeApp.run
