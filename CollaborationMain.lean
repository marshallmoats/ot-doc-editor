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
                  ("acceptedCount", toJson receipt.acceptedEdit.length),
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
