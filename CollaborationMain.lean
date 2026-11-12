import Editor.Collaboration.Server
import Lean.Data.Json

open OT Lean

def collabKindToString : Kind → String
  | .para => "para"
  | .h1 => "h1"
  | .h2 => "h2"
  | .item => "item"
  | .quote => "quote"

def collabDocJson (d : BDoc) : Json :=
  Json.arr (d.map fun b =>
    Json.mkObj [
      ("kind", Json.str (collabKindToString b.kind)),
      ("text", Json.str (String.ofList b.text))
    ]).toArray

def collabCoreJson : Core Char Kind → Json
  | .inl .nop => Json.mkObj [("op", Json.str "nop")]
  | .inl (.ins p ch) => Json.mkObj [
      ("op", Json.str "ins"), ("offset", toJson p),
      ("char", Json.str (String.singleton ch))]
  | .inl (.del p ch) => Json.mkObj [
      ("op", Json.str "del"), ("offset", toJson p),
      ("char", Json.str (String.singleton ch))]
  | .setK old next => Json.mkObj [
      ("op", Json.str "setKind"), ("old", Json.str (collabKindToString old)),
      ("kind", Json.str (collabKindToString next))]
  | .split p kind => Json.mkObj [
      ("op", Json.str "split"), ("offset", toJson p),
      ("kind", Json.str (collabKindToString kind))]
  | .merge p kind => Json.mkObj [
      ("op", Json.str "merge"), ("offset", toJson p),
      ("kind", Json.str (collabKindToString kind))]

def collabBOpJson : BOp Char Kind → Json
  | .nop => Json.mkObj [("tag", Json.str "nop")]
  | .blk block core => Json.mkObj [
      ("tag", Json.str "blk"), ("block", toJson block),
      ("core", collabCoreJson core)]

def collabOpsJson (ops : BOps) : Json :=
  Json.arr (ops.map collabBOpJson).toArray

def collabChangesJson (changes : List BOps) : Json :=
  Json.arr (changes.map collabOpsJson).toArray

/-- Log entries before the accepted request's own revision. This also
makes duplicate request receipts safe: the client's own accepted batch is
never replayed as a remote operation. Later log entries are fetched by poll. -/
def collabChangesBefore (s : CollaborationServer) (base acceptedRevision : Nat) : Json :=
  let count := acceptedRevision - base - 1
  collabChangesJson ((s.srv.log.drop base).take count)

def collabStateJson (s : CollaborationServer) (since : Nat := 0) : Json :=
  Json.mkObj [
    ("ok", Json.bool true),
    ("doc", collabDocJson s.srv.doc),
    ("rev", toJson s.revision),
    ("canUndo", Json.bool (!s.undoHistory.isEmpty)),
    ("canRedo", Json.bool (!s.redoHistory.isEmpty)),
    ("changes", collabChangesJson (s.srv.log.drop since)),
    ("cursor", Json.null)
  ]

def collabError (message : String) : Json :=
  Json.mkObj [("ok", Json.bool false), ("error", Json.str message)]

def collabParsePos (j : Json) (key : String) : Except String (Nat × Nat) := do
  let p ← j.getObjVal? key
  let block ← p.getObjValAs? Nat "block"
  let offset ← p.getObjValAs? Nat "offset"
  pure (block, offset)

def collabParseKind : String → Option Kind
  | "para" => some .para
  | "h1" => some .h1
  | "h2" => some .h2
  | "item" => some .item
  | "quote" => some .quote
  | _ => none

def collabParseChar (j : Json) : Except String Char := do
  let raw ← j.getObjValAs? String "char"
  match raw.toList with
  | [ch] => pure ch
  | _ => throw "expected a single Unicode scalar value"

def collabParseCore (j : Json) : Except String (Core Char Kind) := do
  let op ← j.getObjValAs? String "op"
  match op with
  | "nop" => pure (.inl .nop)
  | "ins" =>
    let offset ← j.getObjValAs? Nat "offset"
    let ch ← collabParseChar j
    pure (.inl (.ins offset ch))
  | "del" =>
    let offset ← j.getObjValAs? Nat "offset"
    let ch ← collabParseChar j
    pure (.inl (.del offset ch))
  | "setKind" =>
    let oldText ← j.getObjValAs? String "old"
    let newText ← j.getObjValAs? String "kind"
    let old ← match collabParseKind oldText with
      | some kind => pure kind
      | none => throw "unknown previous block kind"
    let next ← match collabParseKind newText with
      | some kind => pure kind
      | none => throw "unknown block kind"
    pure (.setK old next)
  | "split" =>
    let offset ← j.getObjValAs? Nat "offset"
    let kindText ← j.getObjValAs? String "kind"
    let kind ← match collabParseKind kindText with
      | some kind => pure kind
      | none => throw "unknown block kind"
    pure (.split offset kind)
  | "merge" =>
    let offset ← j.getObjValAs? Nat "offset"
    let kindText ← j.getObjValAs? String "kind"
    let kind ← match collabParseKind kindText with
      | some kind => pure kind
      | none => throw "unknown block kind"
    pure (.merge offset kind)
  | _ => throw "unknown core operation"

def collabParseBOp (j : Json) : Except String (BOp Char Kind) := do
  let tag ← j.getObjValAs? String "tag"
  match tag with
  | "nop" => pure .nop
  | "blk" =>
    let block ← j.getObjValAs? Nat "block"
    let coreJson ← j.getObjVal? "core"
    let core ← collabParseCore coreJson
    pure (.blk block core)
  | _ => throw "unknown block operation"

def collabParseOps (j : Json) : Except String BOps := do
  match j with
  | .arr items => items.toList.mapM collabParseBOp
  | _ => throw "expected an operation array"

/-- One JSON-lines room process. The Lean server is the serialization point:
each request is built against its declared historical revision and submitted
through the proof-carrying CollaborationServer API. -/
def collabHandle (s : CollaborationServer) (line : String) :
    Json × CollaborationServer :=
  match Json.parse line with
  | .error e => (collabError s!"bad json: {e}", s)
  | .ok j =>
    match j.getObjValAs? String "cmd" with
    | .error _ => (collabError "missing cmd", s)
    | .ok "state" =>
      let since := (j.getObjValAs? Nat "since").toOption.getD 0
      (collabStateJson s since, s)
    | .ok "undo" =>
      let since := (j.getObjValAs? Nat "baseRevision").toOption.getD s.revision
      match s.undo with
      | none => (collabError "nothing to undo", s)
      | some next => (collabStateJson next since, next)
    | .ok "redo" =>
      let since := (j.getObjValAs? Nat "baseRevision").toOption.getD s.revision
      match s.redo with
      | none => (collabError "nothing to redo", s)
      | some next => (collabStateJson next since, next)
    | .ok "submitOps" =>
      match j.getObjValAs? Nat "baseRevision",
          j.getObjValAs? String "clientId",
          j.getObjValAs? String "requestId",
          j.getObjVal? "ops" with
      | .ok base, .ok clientId, .ok requestId, .ok opsJson =>
        if hbase : base ≤ s.revision then
          let historicalDoc := s.srv.docAt base
          match collabParseOps opsJson with
          | .error e => (collabError e, s)
          | .ok edit =>
            if hvalid : ValidSeq edit historicalDoc then
              let request : SubmitRequest := {
                clientId := clientId
                requestId := requestId
                baseRevision := base
                edit := edit
              }
              let (next, receipt) := s.accept request hbase hvalid
              let response := Json.mkObj [
                ("ok", Json.bool true),
                ("clientId", Json.str receipt.clientId),
                ("requestId", Json.str receipt.requestId),
                ("acceptedRevision", toJson receipt.revision),
                ("acceptedCount", toJson receipt.acceptedEdit.length),
                ("acceptedEdit", collabOpsJson receipt.acceptedEdit),
                ("changes", collabChangesBefore s base receipt.revision),
                ("doc", collabDocJson receipt.document),
                ("rev", toJson receipt.revision),
                ("canUndo", Json.bool (!next.undoHistory.isEmpty)),
                ("canRedo", Json.bool (!next.redoHistory.isEmpty)),
                ("cursor", Json.null)
              ]
              (response, next)
            else
              (collabError "operation batch rejected by Lean validity check", s)
        else
          (collabError s!"base revision {base} is ahead of server revision {s.revision}", s)
      | _, _, _, _ => (collabError "bad submitOps arguments", s)
    | .ok "setKind" =>
      match j.getObjValAs? Nat "baseRevision",
          j.getObjValAs? String "clientId",
          j.getObjValAs? String "requestId",
          j.getObjValAs? Nat "block",
          j.getObjValAs? String "kind" with
      | .ok base, .ok clientId, .ok requestId, .ok block, .ok kindText =>
        if hbase : base ≤ s.revision then
          let historicalDoc := s.srv.docAt base
          let kind? : Option Kind :=
            match kindText with
            | "para" => some .para
            | "h1" => some .h1
            | "h2" => some .h2
            | "item" => some .item
            | "quote" => some .quote
            | _ => none
          match kind? with
          | none => (collabError "unknown block kind", s)
          | some kind =>
            match setKindOps historicalDoc block kind with
            | none => (collabError "no such block at the requested base revision", s)
            | some edit =>
              if hvalid : ValidSeq edit historicalDoc then
                let request : SubmitRequest := {
                  clientId := clientId
                  requestId := requestId
                  baseRevision := base
                  edit := edit
                }
                let (next, receipt) := s.accept request hbase hvalid
                let response := Json.mkObj [
                  ("ok", Json.bool true),
                  ("clientId", Json.str receipt.clientId),
                  ("requestId", Json.str receipt.requestId),
                  ("acceptedRevision", toJson receipt.revision),
                  ("acceptedCount", toJson receipt.acceptedEdit.length),
                  ("acceptedEdit", collabOpsJson receipt.acceptedEdit),
                  ("changes", collabChangesBefore s base receipt.revision),
                  ("doc", collabDocJson receipt.document),
                  ("rev", toJson receipt.revision),
                  ("canUndo", Json.bool (!next.undoHistory.isEmpty)),
                  ("canRedo", Json.bool (!next.redoHistory.isEmpty)),
                  ("cursor", Json.null)
                ]
                (response, next)
              else
                (collabError "edit rejected by Lean validity check", s)
        else
          (collabError s!"base revision {base} is ahead of server revision {s.revision}", s)
      | _, _, _, _, _ => (collabError "bad setKind arguments", s)
    | .ok "replace" =>
      match j.getObjValAs? Nat "baseRevision",
          j.getObjValAs? String "clientId",
          j.getObjValAs? String "requestId",
          collabParsePos j "from",
          collabParsePos j "to",
          j.getObjValAs? String "text" with
      | .ok base, .ok clientId, .ok requestId,
          .ok (i, p), .ok (k, q), .ok txt =>
        if hbase : base ≤ s.revision then
          let historicalDoc := s.srv.docAt base
          match replaceOps historicalDoc i p k q txt with
          | none => (collabError "invalid range at the requested base revision", s)
          | some edit =>
            if hvalid : ValidSeq edit historicalDoc then
              let request : SubmitRequest := {
                clientId := clientId
                requestId := requestId
                baseRevision := base
                edit := edit
              }
              let (next, receipt) := s.accept request hbase hvalid
              let response := Json.mkObj [
                ("ok", Json.bool true),
                ("clientId", Json.str receipt.clientId),
                ("requestId", Json.str receipt.requestId),
                ("acceptedRevision", toJson receipt.revision),
                  ("acceptedCount", toJson receipt.acceptedEdit.length),
                  ("acceptedEdit", collabOpsJson receipt.acceptedEdit),
                  ("changes", collabChangesBefore s base receipt.revision),
                ("doc", collabDocJson receipt.document),
                ("rev", toJson receipt.revision),
                ("canUndo", Json.bool (!next.undoHistory.isEmpty)),
                ("canRedo", Json.bool (!next.redoHistory.isEmpty)),
                ("cursor", Json.null)
              ]
              (response, next)
            else
              (collabError "edit rejected by Lean validity check", s)
        else
          (collabError s!"base revision {base} is ahead of server revision {s.revision}", s)
      | _, _, _, _, _, _ =>
        (collabError "bad replace arguments", s)
    | .ok c => (collabError s!"unknown command {c}", s)

partial def collabLoop (hin hout : IO.FS.Stream)
    (server : CollaborationServer) : IO Unit := do
  let line ← hin.getLine
  if line.isEmpty then
    return
  let (response, next) := collabHandle server line.trimAscii.toString
  hout.putStrLn response.compress
  hout.flush
  collabLoop hin hout next

def main : IO Unit := do
  collabLoop (← IO.getStdin) (← IO.getStdout)
    (CollaborationServer.init initialDoc)
