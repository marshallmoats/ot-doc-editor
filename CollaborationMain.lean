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

def collabStateJson (s : CollaborationServer) : Json :=
  Json.mkObj [
    ("ok", Json.bool true),
    ("doc", collabDocJson s.srv.doc),
    ("rev", toJson s.revision),
    ("canUndo", Json.bool (!s.undoHistory.isEmpty)),
    ("canRedo", Json.bool (!s.redoHistory.isEmpty)),
    ("cursor", Json.null)
  ]

def collabError (message : String) : Json :=
  Json.mkObj [("ok", Json.bool false), ("error", Json.str message)]



/-! ## Browser OT operation wire format -/

def collabOpJson : BOp Char Kind → Json
  | .nop => Json.mkObj [("tag", Json.str "nop")]
  | .blk i (.inl .nop) => Json.mkObj [("tag", Json.str "blk"), ("index", toJson i),
      ("core", Json.mkObj [("tag", Json.str "nop")])]
  | .blk i (.inl (.ins p ch)) => Json.mkObj [("tag", Json.str "blk"), ("index", toJson i),
      ("core", Json.mkObj [("tag", Json.str "ins"), ("pos", toJson p), ("char", Json.str (String.ofList [ch]))])]
  | .blk i (.inl (.del p ch)) => Json.mkObj [("tag", Json.str "blk"), ("index", toJson i),
      ("core", Json.mkObj [("tag", Json.str "del"), ("pos", toJson p), ("char", Json.str (String.ofList [ch]))])]
  | .blk i (.setK old new) => Json.mkObj [("tag", Json.str "blk"), ("index", toJson i),
      ("core", Json.mkObj [("tag", Json.str "setK"), ("old", Json.str (collabKindToString old)),
        ("new", Json.str (collabKindToString new))])]
  | .blk i (.split p k) => Json.mkObj [("tag", Json.str "blk"), ("index", toJson i),
      ("core", Json.mkObj [("tag", Json.str "split"), ("pos", toJson p),
        ("kind", Json.str (collabKindToString k))])]
  | .blk i (.merge p k) => Json.mkObj [("tag", Json.str "blk"), ("index", toJson i),
      ("core", Json.mkObj [("tag", Json.str "merge"), ("pos", toJson p),
        ("kind", Json.str (collabKindToString k))])]

def collabParseKind (s : String) : Except String Kind :=
  match s with
  | "para" => .ok .para | "h1" => .ok .h1 | "h2" => .ok .h2
  | "item" => .ok .item | "quote" => .ok .quote
  | _ => .error "unknown block kind in operation"

def collabParseOp (j : Json) : Except String (BOp Char Kind) := do
  let tag ← j.getObjValAs? String "tag"
  if tag == "nop" then return .nop
  if tag != "blk" then throw "unknown operation tag"
  let i ← j.getObjValAs? Nat "index"
  let core ← j.getObjVal? "core"
  let ct ← core.getObjValAs? String "tag"
  if ct == "nop" then return .blk i (.inl .nop)
  if ct == "ins" || ct == "del" then
    let p ← core.getObjValAs? Nat "pos"
    let raw ← core.getObjValAs? String "char"
    match raw.toList with
    | [ch] => return .blk i (.inl (if ct == "ins" then .ins p ch else .del p ch))
    | _ => throw "operation char must contain exactly one Unicode scalar"
  if ct == "setK" then
    let old ← core.getObjValAs? String "old"
    let new ← core.getObjValAs? String "new"
    return .blk i (.setK (← collabParseKind old) (← collabParseKind new))
  if ct == "split" || ct == "merge" then
    let p ← core.getObjValAs? Nat "pos"
    let kind ← core.getObjValAs? String "kind"
    let k ← collabParseKind kind
    return .blk i (if ct == "split" then .split p k else .merge p k)
  throw "unknown core operation tag"

def collabParseOps (j : Json) : Except String BOps := do
  let arr ← j.getArr?
  arr.toList.mapM collabParseOp

def collabChangeJson (revision : Nat) (edit : BOps) (receipt : String × String) : Json :=
  Json.mkObj [
    ("revision", toJson revision),
    ("clientId", Json.str receipt.1),
    ("requestId", Json.str receipt.2),
    ("edit", Json.arr (edit.map collabOpJson).toArray)
  ]

def collabChangesJson (s : CollaborationServer) (since : Nat) : Json :=
  Json.arr ((s.srv.log.drop since).zip (s.receipts.drop since) |>.mapIdx
    (fun i pair => collabChangeJson (since + i + 1) pair.1 pair.2)).toArray

def collabStateChangesJson (s : CollaborationServer) (since : Nat) : Json :=
  Json.mkObj [
    ("ok", Json.bool true),
    ("doc", collabDocJson s.srv.doc),
    ("rev", toJson s.revision),
    ("canUndo", Json.bool (!s.undoHistory.isEmpty)),
    ("canRedo", Json.bool (!s.redoHistory.isEmpty)),
    ("changes", collabChangesJson s since)
  ]

def collabParsePos (j : Json) (key : String) : Except String (Nat × Nat) := do
  let p ← j.getObjVal? key
  let block ← p.getObjValAs? Nat "block"
  let offset ← p.getObjValAs? Nat "offset"
  pure (block, offset)

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
    | .ok "state" => (collabStateJson s, s)
    | .ok "changesSince" =>
      match j.getObjValAs? Nat "since" with
      | .ok since =>
        if since ≤ s.revision then (collabStateChangesJson s since, s)
        else (collabError "requested revision is ahead of server", s)
      | .error _ => (collabError "missing since revision", s)
    | .ok "submitOps" =>
      match j.getObjValAs? Nat "baseRevision",
          j.getObjValAs? String "clientId",
          j.getObjValAs? String "requestId",
          j.getObjVal? "ops" with
      | .ok base, .ok clientId, .ok requestId, .ok opsJson =>
        if hbase : base ≤ s.revision then
          match collabParseOps opsJson with
          | .error e => (collabError e, s)
          | .ok edit =>
            if hvalid : ValidSeq edit (s.srv.docAt base) then
              let request : SubmitRequest := {
                clientId := clientId, requestId := requestId,
                baseRevision := base, edit := edit
              }
              let (next, _) := s.accept request hbase hvalid
              (collabStateChangesJson next base, next)
            else (collabError "operation batch is invalid at its base revision", s)
        else (collabError "base revision is ahead of server revision", s)
      | _, _, _, _ => (collabError "bad submitOps arguments", s)
    | .ok "undo" =>
      match s.undo with
      | none => (collabError "nothing to undo", s)
      | some next => (collabStateJson next, next)
    | .ok "redo" =>
      match s.redo with
      | none => (collabError "nothing to redo", s)
      | some next => (collabStateJson next, next)
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
