import Editor.Core
import Lean.Data.Json

open OT Lean

/-! ## JSON protocol -/

def OT.Kind.toStr : Kind → String
  | .para => "para" | .h1 => "h1" | .h2 => "h2" | .item => "item" | .quote => "quote"

def OT.Kind.ofStr? : String → Option Kind
  | "para" => some .para | "h1" => some .h1 | "h2" => some .h2
  | "item" => some .item | "quote" => some .quote | _ => none

def docJson (d : BDoc) : Json :=
  Json.arr (d.map fun b =>
    Json.mkObj [("kind", Json.str b.kind.toStr), ("text", Json.str (String.mk b.text))]).toArray

def respond (s : Session) (cursor : Option (Nat × Nat)) : Json :=
  Json.mkObj [
    ("ok", Json.bool true),
    ("doc", docJson s.doc),
    ("rev", toJson s.srv.log.length),
    ("canUndo", Json.bool !s.undoStack.isEmpty),
    ("canRedo", Json.bool !s.redoStack.isEmpty),
    ("cursor", match cursor with
      | some (b, o) => Json.mkObj [("block", toJson b), ("offset", toJson o)]
      | none => Json.null)]

def errJson (msg : String) : Json :=
  Json.mkObj [("ok", Json.bool false), ("error", Json.str msg)]

def parsePos (j : Json) (key : String) : Except String (Nat × Nat) := do
  let p ← j.getObjVal? key
  let b ← p.getObjValAs? Nat "block"
  let o ← p.getObjValAs? Nat "offset"
  pure (b, o)

def commitEdit (s : Session) (e : BOps) : Json × Session :=
  if e.isEmpty then (respond s none, s)
  else if h : ValidSeq e s.doc then
    let s' := s.commit e h
    (respond s' (focusOf e), s')
  else (errJson "edit rejected: not valid at the current document", s)

def handle (s : Session) (line : String) : Json × Session :=
  match Json.parse line with
  | .error e => (errJson s!"bad json: {e}", s)
  | .ok j =>
    match j.getObjValAs? String "cmd" with
    | .error _ => (errJson "missing cmd", s)
    | .ok "state" => (respond s none, s)
    | .ok "replace" =>
      match parsePos j "from", parsePos j "to", j.getObjValAs? String "text" with
      | .ok (i, p), .ok (k, q), .ok txt =>
        match replaceOps s.doc i p k q txt with
        | none => (errJson "invalid range", s)
        | some e => commitEdit s e
      | _, _, _ => (errJson "bad replace arguments", s)
    | .ok "setKind" =>
      match j.getObjValAs? Nat "block", j.getObjValAs? String "kind" with
      | .ok i, .ok ks =>
        match Kind.ofStr? ks with
        | none => (errJson s!"unknown kind {ks}", s)
        | some k =>
          match setKindOps s.doc i k with
          | none => (errJson "no such block", s)
          | some e => commitEdit s e
      | _, _ => (errJson "bad setKind arguments", s)
    | .ok "undo" =>
      match s.undo with
      | none => (respond s none, s)
      | some (s', e) => (respond s' (focusOf e), s')
    | .ok "redo" =>
      match s.redo with
      | none => (respond s none, s)
      | some (s', e) => (respond s' (focusOf e), s')
    | .ok c => (errJson s!"unknown command {c}", s)

partial def loop (hin hout : IO.FS.Stream) (s : Session) : IO Unit := do
  let line ← hin.getLine
  if line.isEmpty then return
  let (resp, s') := handle s line.trimAscii
  hout.putStrLn resp.compress
  hout.flush
  loop hin hout s'

def main : IO Unit := do
  loop (← IO.getStdin) (← IO.getStdout) (Session.init initialDoc)
