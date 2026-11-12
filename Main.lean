import OT
import Lean.Data.Json

/-!
# Single-user editor backend

A JSON-lines protocol over stdin/stdout around a verified session.

Trust boundary: *every* committed edit passes through a dependent `if h : ValidSeq e doc`,
so the session invariant `Wf` (the whole log replays without an invalid op) is carried as a
proof in the `Session` structure. The edit *builders* below translate UI intent into ops and
are not verified for intent, but they cannot corrupt the document: a wrong builder can only
be rejected, or produce a different valid edit.

Undo and redo apply exact inverses held in head coordinates (see `Session`).
-/

open OT Lean

abbrev BDoc := List (Block Char Kind)
abbrev BOps := List (BOp Char Kind)
abbrev BSrv := Server (BOp Char Kind) BDoc

/-! ## Decidable validity (so the runtime can check edits and obtain proofs) -/

instance (o : Op Char) (t : List Char) : Decidable (o.Valid t) := by
  cases o <;> simp only [Op.Valid] <;> infer_instance

def decValidHead : (c : Core Char Kind) → (l : BDoc) → Decidable (c.validHead l)
  | .inl o, b :: _ => inferInstanceAs (Decidable (o.Valid b.text))
  | .setK old _, b :: _ => inferInstanceAs (Decidable (b.kind = old))
  | .split p _, b :: _ => inferInstanceAs (Decidable (p ≤ b.text.length))
  | .merge p k, b :: b2 :: _ => inferInstanceAs (Decidable (b.text.length = p ∧ b2.kind = k))
  | .inl _, [] => isFalse (fun h => h)
  | .setK _ _, [] => isFalse (fun h => h)
  | .split _ _, [] => isFalse (fun h => h)
  | .merge _ _, [] => isFalse (fun h => h)
  | .merge _ _, [_] => isFalse (fun h => h)

def decValidAt : (i : Nat) → (c : Core Char Kind) → (l : BDoc) → Decidable (validAt i c l)
  | 0, c, l => decValidHead c l
  | _ + 1, _, [] => isFalse (fun h => h)
  | i + 1, c, _ :: bs => decValidAt i c bs

instance (x : BOp Char Kind) (l : BDoc) : Decidable (x.Valid l) :=
  match x with
  | .nop => isTrue trivial
  | .blk i c => decValidAt i c l

def decValidSeq : (es : BOps) → (d : BDoc) → Decidable (ValidSeq es d)
  | [], _ => isTrue trivial
  | o :: os, d =>
    haveI : Decidable (BOp.Valid o d) := inferInstance
    haveI : Decidable (ValidSeq os (BOp.apply o d)) := decValidSeq os (BOp.apply o d)
    inferInstanceAs (Decidable (BOp.Valid o d ∧ ValidSeq os (BOp.apply o d)))

instance (es : BOps) (d : BDoc) : Decidable (ValidSeq es d) := decValidSeq es d

/-! ## Session: server log + head-coordinate undo/redo stacks, invariants as proofs

Undo and redo stacks hold *exact inverses in head coordinates*. In a single-user session the
top entry is always valid at the current document, so undoing is just applying it, and the
inverse of what was applied becomes the matching redo (and vice versa). `ValidChain` is the
invariant, and `ValidChain.push_inv` (from `invSeq_correct`) maintains it.
For collaboration, entries would additionally be transformed over incoming remote edits with
`xformSeq`, whose correctness theorem preserves exactly this invariant. -/

structure Session where
  srv : BSrv
  doc : BDoc
  undoStack : List BOps
  redoStack : List BOps
  hdoc : doc = srv.doc
  wf : srv.Wf
  uchain : ValidChain undoStack doc
  rchain : ValidChain redoStack doc

def Session.init (d : BDoc) : Session where
  srv := ⟨d, []⟩
  doc := d
  undoStack := []
  redoStack := []
  hdoc := rfl
  wf := trivial
  uchain := trivial
  rchain := trivial

/-- Commit a user edit; requires a proof it is valid at the head. Clears the redo stack. -/
def Session.commit (s : Session) (e : BOps) (h : ValidSeq e s.doc) : Session where
  srv := s.srv.append e
  doc := applyAll e s.doc
  undoStack := invSeq e :: s.undoStack
  redoStack := []
  hdoc := by rw [Server.append_doc, s.hdoc]
  wf := s.srv.append_wf s.wf e (by rw [← s.hdoc]; exact h)
  uchain := ValidChain.push_inv e s.doc h s.undoStack s.uchain
  rchain := trivial

/-- Undo: apply the top undo entry; its inverse becomes a redo entry. -/
def Session.undo (s : Session) : Option (Session × BOps) :=
  match hu : s.undoStack with
  | [] => none
  | u :: rest =>
    have h : ValidSeq u s.doc ∧ ValidChain rest (applyAll u s.doc) := by
      have := s.uchain; rw [hu] at this; exact this
    some ({
      srv := s.srv.append u
      doc := applyAll u s.doc
      undoStack := rest
      redoStack := invSeq u :: s.redoStack
      hdoc := by rw [Server.append_doc, s.hdoc]
      wf := s.srv.append_wf s.wf u (by rw [← s.hdoc]; exact h.1)
      uchain := h.2
      rchain := ValidChain.push_inv u s.doc h.1 s.redoStack s.rchain
    }, u)

/-- Redo: apply the top redo entry; its inverse becomes an undo entry. -/
def Session.redo (s : Session) : Option (Session × BOps) :=
  match hr : s.redoStack with
  | [] => none
  | r :: rest =>
    have h : ValidSeq r s.doc ∧ ValidChain rest (applyAll r s.doc) := by
      have := s.rchain; rw [hr] at this; exact this
    some ({
      srv := s.srv.append r
      doc := applyAll r s.doc
      undoStack := invSeq r :: s.undoStack
      redoStack := rest
      hdoc := by rw [Server.append_doc, s.hdoc]
      wf := s.srv.append_wf s.wf r (by rw [← s.hdoc]; exact h.1)
      uchain := ValidChain.push_inv r s.doc h.1 s.undoStack s.uchain
      rchain := h.2
    }, r)

/-! ## Edit builders: UI intent → ops (checked at runtime, never trusted) -/

/-- Kind of the block created by pressing Enter. -/
def nextKind : Kind → Kind
  | .h1 => .para
  | .h2 => .para
  | k => k

def delOps (i p : Nat) (cs : List Char) : BOps :=
  cs.map fun c => .blk i (.inl (.del p c))

/-- Delete the range from `(i,p)` to `(j,q)` (block, offset), merging blocks as needed. -/
def deleteRange (d : BDoc) (i p j q : Nat) : Option BOps :=
  if i = j then
    match d[i]? with
    | none => none
    | some b =>
      if p ≤ q ∧ q ≤ b.text.length then some (delOps i p ((b.text.drop p).take (q - p)))
      else none
  else if i < j then
    match d[i]?, d[j]? with
    | some bi, some bj =>
      if p ≤ bi.text.length ∧ q ≤ bj.text.length then
        let tailJ := delOps j 0 (bj.text.take q)
        let mids := (List.range (j - i - 1)).flatMap fun k =>
          match d[i + 1 + k]? with
          | some bm => delOps (i + 1 + k) 0 bm.text
          | none => []
        let headI := delOps i p (bi.text.drop p)
        let merges := (List.range (j - i)).filterMap fun k =>
          (d[i + 1 + k]?).map fun bk => BOp.blk i (.merge p bk.kind)
        some (tailJ ++ mids ++ headI ++ merges)
      else none
    | _, _ => none
  else none

/-- Insert text at `(i,p)`; `'\n'` splits the block. -/
def insertOps (cur : Kind) (i p : Nat) : List Char → BOps
  | [] => []
  | c :: cs =>
    if c = '\n' then .blk i (.split p (nextKind cur)) :: insertOps (nextKind cur) (i + 1) 0 cs
    else if c = '\r' then insertOps cur i p cs
    else .blk i (.inl (.ins p c)) :: insertOps cur i (p + 1) cs

/-- Replace the range `(i,p)–(j,q)` with `txt` (covers typing, paste, cut, backspace, delete). -/
def replaceOps (d : BDoc) (i p j q : Nat) (txt : String) : Option BOps := do
  let del ← deleteRange d i p j q
  let b ← d[i]?
  some (del ++ insertOps b.kind i p txt.toList)

def setKindOps (d : BDoc) (i : Nat) (k : Kind) : Option BOps := do
  let b ← d[i]?
  if b.kind = k then some [] else some [.blk i (.setK b.kind k)]

/-- Where the caret should go after an edit (derived from its last meaningful op). -/
def focusOf (es : BOps) : Option (Nat × Nat) :=
  es.reverse.findSome? fun
    | .blk i (.inl (.ins p _)) => some (i, p + 1)
    | .blk i (.inl (.del p _)) => some (i, p)
    | .blk i (.split _ _) => some (i + 1, 0)
    | .blk i (.merge p _) => some (i, p)
    | _ => none

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

def initialDoc : BDoc :=
  [⟨.h1, "A verified collaborative editor".toList⟩,
   ⟨.para, "Every edit is validated before it is committed, and undo applies exact inverses.".toList⟩,
   ⟨.para, "Try typing, pressing Enter, Backspace across lines, and Ctrl+Z / Ctrl+Shift+Z.".toList⟩]

partial def loop (hin hout : IO.FS.Stream) (s : Session) : IO Unit := do
  let line ← hin.getLine
  if line.isEmpty then return
  let (resp, s') := handle s line.trim
  hout.putStrLn resp.compress
  hout.flush
  loop hin hout s'

def main : IO Unit := do
  loop (← IO.getStdin) (← IO.getStdout) (Session.init initialDoc)
