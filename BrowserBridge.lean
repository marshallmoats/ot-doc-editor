/-
# Lean client bridge for the production contenteditable editor

The DOM editor sends edit intents over Lasm ports. This module constructs,
validates, applies, rebases, and acknowledges document operations. JavaScript
is responsible only for DOM/selection/IME, rendering, and HTTP transport.
-/

import Editor.Collaboration.Server
import Lasm.UI

open OT
open Lasm.UI
open Lasm.JS

inductive BridgeMsg where
  | intent (data : Data)
  | remote (data : Data)
  | acknowledge (data : Data)
  | snapshotRequest

def bridgeKindName : Kind → String
  | .para => "para"
  | .h1 => "h1"
  | .h2 => "h2"
  | .item => "item"
  | .quote => "quote"

def bridgeString? (data : Data) (key : String) : Option String :=
  match data.field key with
  | .string value => some value
  | _ => none

def bridgeNat? (data : Data) (key : String) : Option Nat :=
  match data.field key with
  | .number value =>
    if value >= 0 && value.floor == value then some value.toUInt64.toNat else none
  | _ => none

def bridgeCoreData : Core Char Kind → Data
  | .inl .nop => .object #[("op", .string "nop")]
  | .inl (.ins p ch) => .object #[
      ("op", .string "ins"), ("offset", toJS p),
      ("char", .string (String.singleton ch))]
  | .inl (.del p ch) => .object #[
      ("op", .string "del"), ("offset", toJS p),
      ("char", .string (String.singleton ch))]
  | .setK old next => .object #[
      ("op", .string "setKind"), ("old", .string (bridgeKindName old)),
      ("kind", .string (bridgeKindName next))]
  | .split p kind => .object #[
      ("op", .string "split"), ("offset", toJS p),
      ("kind", .string (bridgeKindName kind))]
  | .merge p kind => .object #[
      ("op", .string "merge"), ("offset", toJS p),
      ("kind", .string (bridgeKindName kind))]

def bridgeBOpData : BOp Char Kind → Data
  | .nop => .object #[("tag", .string "nop")]
  | .blk block core => .object #[
      ("tag", .string "blk"), ("block", toJS block),
      ("core", bridgeCoreData core)]

def bridgeOpsData (ops : BOps) : Data :=
  .array (ops.map bridgeBOpData).toArray

def bridgeDocData (doc : BDoc) : Data :=
  .array ((doc.map fun block =>
    Data.object #[
      ("kind", .string (bridgeKindName block.kind)),
      ("text", .string (String.ofList block.text))
    ]).toArray)

def bridgeSnapshot (c : ClientState) : Data :=
  .object #[
    ("ok", .bool true),
    ("doc", bridgeDocData c.doc),
    ("confirmedDoc", bridgeDocData c.confirmedDoc),
    ("rev", toJS c.revision),
    ("pendingCount", toJS c.pending.length),
    ("pendingOps", bridgeOpsData c.pending),
    ("canUndo", .bool (!c.undoStack.isEmpty)),
    ("canRedo", .bool (!c.redoStack.isEmpty))
  ]

def bridgeErrorData (message : String) : Data :=
  .object #[("ok", .bool false), ("error", .string message)]

def bridgeParsePos (data : Data) (key : String) : Option (Nat × Nat) := do
  let pos := data.field key
  let block ← bridgeNat? pos "block"
  let offset ← bridgeNat? pos "offset"
  pure (block, offset)

def bridgeKind? : String → Option Kind
  | "para" => some .para
  | "h1" => some .h1
  | "h2" => some .h2
  | "item" => some .item
  | "quote" => some .quote
  | _ => none

def bridgeChar? (data : Data) : Option Char := do
  let raw ← bridgeString? data "char"
  match raw.toList with
  | [ch] => some ch
  | _ => none

def bridgeCore? (data : Data) : Option (Core Char Kind) := do
  let op ← bridgeString? data "op"
  match op with
  | "nop" => some (.inl .nop)
  | "ins" =>
    let offset ← bridgeNat? data "offset"
    let ch ← bridgeChar? data
    some (.inl (.ins offset ch))
  | "del" =>
    let offset ← bridgeNat? data "offset"
    let ch ← bridgeChar? data
    some (.inl (.del offset ch))
  | "setKind" =>
    let oldText ← bridgeString? data "old"
    let newText ← bridgeString? data "kind"
    let old ← bridgeKind? oldText
    let next ← bridgeKind? newText
    some (.setK old next)
  | "split" =>
    let offset ← bridgeNat? data "offset"
    let kindText ← bridgeString? data "kind"
    let kind ← bridgeKind? kindText
    some (.split offset kind)
  | "merge" =>
    let offset ← bridgeNat? data "offset"
    let kindText ← bridgeString? data "kind"
    let kind ← bridgeKind? kindText
    some (.merge offset kind)
  | _ => none

def bridgeBOp? (data : Data) : Option (BOp Char Kind) := do
  let tag ← bridgeString? data "tag"
  match tag with
  | "nop" => some .nop
  | "blk" =>
    let block ← bridgeNat? data "block"
    let core ← bridgeCore? (data.field "core")
    some (.blk block core)
  | _ => none

def bridgeOps? (data : Data) : Option BOps :=
  match data with
  | .array items => items.toList.mapM bridgeBOp?
  | _ => none

def bridgeChanges? (data : Data) : Option (List BOps) :=
  match data with
  | .array items => items.toList.mapM bridgeOps?
  | _ => none

def bridgeRemote (c : ClientState) (data : Data) : Option ClientState := do
  let changes ← bridgeChanges? data
  changes.foldlM (fun state ops =>
    if h : ValidSeq ops state.confirmedDoc then
      some (state.receiveRemote ops h)
    else
      none) c

def bridgeIntent (c : ClientState) (data : Data) : Option ClientState :=
  match bridgeString? data "cmd" with
  | some "replace" =>
    match bridgeParsePos data "from", bridgeParsePos data "to",
        bridgeString? data "text" with
    | some (i, p), some (k, q), some txt => c.applyReplace i p k q txt
    | _, _, _ => none
  | some "setKind" =>
    match bridgeNat? data "block", bridgeString? data "kind" with
    | some block, some kindText =>
      match bridgeKind? kindText with
      | some kind => c.applySetKind block kind
      | none => none
    | _, _ => none
  | _ => none

def bridgeAckInfo (data : Data) : Option (BOps × Nat) := do
  let accepted ← bridgeOps? (data.field "acceptedEdit")
  let revision ← bridgeNat? data "acceptedRevision"
  pure (accepted, revision)

def bridgeInit (_ : Unit) : ClientState × Cmd BridgeMsg :=
  let c := ClientState.init initialDoc
  (c, Cmd.port "snapshot" (bridgeSnapshot c))

def bridgeUpdate : BridgeMsg → ClientState → ClientState × Cmd BridgeMsg
  | .intent data, c =>
    match bridgeIntent c data with
    | none =>
      (c, Cmd.port "snapshot" (bridgeErrorData "Lean rejected the edit intent"))
    | some next =>
      (next, Cmd.port "snapshot" (bridgeSnapshot next))
  | .remote data, c =>
    match bridgeRemote c data with
    | none => (c, Cmd.port "snapshot" (bridgeErrorData "Malformed or invalid remote change batch"))
    | some next => (next, Cmd.port "snapshot" (bridgeSnapshot next))
  | .acknowledge data, c =>
    match bridgeAckInfo data with
    | none => (c, Cmd.port "snapshot" (bridgeErrorData "Malformed acknowledgement"))
    | some (accepted, revision) =>
      match c.acknowledgeAcceptedAt accepted revision with
      | none => (c, Cmd.port "snapshot" (bridgeErrorData "Server acknowledgement does not match the pending prefix"))
      | some next =>
        (next, Cmd.port "snapshot" (bridgeSnapshot next))
  | .snapshotRequest, c =>
    (c, Cmd.port "snapshot" (bridgeSnapshot c))

def bridgeSubscriptions (_ : ClientState) : Subs BridgeMsg :=
  Subs.batch [
    Subs.port "intent" fun data => some (.intent data),
    Subs.port "remote" fun data => some (.remote data),
    Subs.port "ack" fun data => some (.acknowledge data),
    Subs.port "snapshot-request" fun _ => some .snapshotRequest
  ]

def bridgeView (_ : ClientState) : Html BridgeMsg :=
  html! <div></div>

def bridgeApp : App Unit ClientState BridgeMsg :=
  App.element bridgeInit bridgeUpdate bridgeView bridgeSubscriptions

def main : IO Unit :=
  bridgeApp.run
