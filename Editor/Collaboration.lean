import Editor.Core

open OT

/-!
# Optimistic collaborative client state

The client keeps the last confirmed server document and revision separately
from its optimistic document. `pending` is the flattened sequence of local
operations not yet acknowledged by the server.

Incoming remote operations are expressed against the confirmed document.
They are transformed over pending local operations; the transformed remote
operations are then applied to the optimistic document. Undo and redo chains
are rebased in head coordinates as well, preserving their validity proofs.
-/

/-- Transform every edit in a head-coordinate history over a concurrent edit.
The concurrent edit is carried forward through each history entry. -/
def rebaseChain {O D : Type} [OTAlg O D] :
    List (List O) → List O → List (List O)
  | [], _ => []
  | u :: us, remote =>
      let (u', remote') := xformSeq u remote .right
      u' :: rebaseChain us remote'

/-- Rebased history remains a valid undo/redo chain at the rebased document. -/
theorem rebaseChain_valid {O D : Type} [OTAlg O D] (stack : List (List O)) :
    ∀ (remote : List O) (d : D),
      ValidChain stack d → ValidSeq remote d →
      ValidChain (rebaseChain stack remote) (applyAll remote d) := by
  induction stack with
  | nil =>
      intro remote d _ _
      simp [rebaseChain, ValidChain]
  | cons u us ih =>
      intro remote d hs hr
      rcases hs with ⟨hu, hus⟩
      let pair := xformSeq u remote .right
      have hxf := xformSeq_correct u remote .right d hu hr
      have htail := ih pair.2 (applyAll u d) hus hxf.2.1
      change ValidSeq pair.1 (applyAll remote d) ∧
        ValidChain (rebaseChain us pair.2) (applyAll pair.1 (applyAll remote d))
      exact ⟨hxf.1, by rw [hxf.2.2]; exact htail⟩

/-- A proof-carrying optimistic client. All pending operations replay from the
confirmed document to produce the visible document. Undo and redo stacks are
valid at that visible document and at each successive history state. -/
structure ClientState where
  confirmedDoc : BDoc
  revision : Nat
  pending : BOps
  doc : BDoc
  undoStack : List BOps
  redoStack : List BOps
  hdoc : doc = applyAll pending confirmedDoc
  hpending : ValidSeq pending confirmedDoc
  uchain : ValidChain undoStack doc
  rchain : ValidChain redoStack doc

namespace ClientState

/-- Start at a server snapshot with no optimistic edits. -/
def init (doc : BDoc) (revision : Nat := 0) : ClientState where
  confirmedDoc := doc
  revision := revision
  pending := []
  doc := doc
  undoStack := []
  redoStack := []
  hdoc := by simp [applyAll]
  hpending := trivial
  uchain := trivial
  rchain := trivial

/-- Apply a local edit immediately and append it to the unacknowledged queue. -/
def applyLocal (c : ClientState) (e : BOps) (he : ValidSeq e c.doc) : ClientState where
  confirmedDoc := c.confirmedDoc
  revision := c.revision
  pending := c.pending ++ e
  doc := applyAll e c.doc
  undoStack := invSeq e :: c.undoStack
  redoStack := []
  hdoc := by rw [applyAll_append, c.hdoc]
  hpending := by
    rw [ValidSeq_append]
    have he' : ValidSeq e (applyAll c.pending c.confirmedDoc) := by
      simpa [c.hdoc] using he
    exact ⟨c.hpending, he'⟩
  uchain := ValidChain.push_inv e c.doc he c.undoStack c.uchain
  rchain := trivial

/-- Integrate one server-accepted remote batch. The batch must be valid at the
confirmed revision. The remote side wins transform ties; the already-visible
local work is retained and rebased, including both history stacks. -/
def receiveRemote (c : ClientState) (remote : BOps)
    (hremote : ValidSeq remote c.confirmedDoc) : ClientState := by
  let pair := xformSeq remote c.pending .left
  have hxf := xformSeq_correct remote c.pending .left c.confirmedDoc hremote c.hpending
  have hremote' : ValidSeq pair.1 c.doc := by
    rw [c.hdoc]
    exact hxf.1
  exact {
    confirmedDoc := applyAll remote c.confirmedDoc
    revision := c.revision + 1
    pending := pair.2
    doc := applyAll pair.1 c.doc
    undoStack := rebaseChain c.undoStack pair.1
    redoStack := rebaseChain c.redoStack pair.1
    hdoc := by
      rw [c.hdoc]
      exact hxf.2.2
    hpending := hxf.2.1
    uchain := rebaseChain_valid c.undoStack pair.1 c.doc c.uchain hremote'
    rchain := rebaseChain_valid c.redoStack pair.1 c.doc c.rchain hremote'
  }

/-- Acknowledge a prefix of the pending queue. This advances the confirmed
snapshot without changing the optimistic document or its history. The prefix
condition is explicit so an out-of-order or mismatched acknowledgement cannot
silently discard local work. -/
def acknowledge (c : ClientState) (accepted rest : BOps)
    (hprefix : c.pending = accepted ++ rest) : ClientState where
  confirmedDoc := applyAll accepted c.confirmedDoc
  revision := c.revision + 1
  pending := rest
  doc := c.doc
  undoStack := c.undoStack
  redoStack := c.redoStack
  hdoc := by
    have h := c.hdoc
    rw [hprefix, applyAll_append] at h
    exact h
  hpending := by
    have h := c.hpending
    rw [hprefix, ValidSeq_append] at h
    exact h.2
  uchain := c.uchain
  rchain := c.rchain

/-- Build and apply a user replacement intent at the optimistic document head.
The browser passes only a range and text; operation construction, validation,
and queue insertion all remain in Lean. -/
def applyReplace (c : ClientState) (i p j q : Nat) (txt : String) :
    Option ClientState := do
  let edit ← replaceOps c.doc i p j q txt
  if h : ValidSeq edit c.doc then
    some (c.applyLocal edit h)
  else
    none

/-- Build and apply a block-kind change at the optimistic document head. -/
def applySetKind (c : ClientState) (i : Nat) (kind : Kind) :
    Option ClientState := do
  let edit ← setKindOps c.doc i kind
  if h : ValidSeq edit c.doc then
    some (c.applyLocal edit h)
  else
    none

end ClientState

/-! ## Executable smoke scenario

Two independent local edits are applied to the optimistic document, then a
remote edit is integrated. The output shows the rebased document and confirms
that both pending local operations remain queued.
-/

def collaborationSmoke : ClientState := by
  let c0 := ClientState.init initialDoc
  let a : BOps := [.blk 0 (.inl (.ins 0 '!'))]
  have ha : ValidSeq a c0.doc := by decide
  let c1 := c0.applyLocal a ha
  let remote : BOps := [.blk 2 (.inl (.ins 0 '?'))]
  have hr : ValidSeq remote initialDoc := by decide
  exact c1.receiveRemote remote hr

#eval (collaborationSmoke.revision, collaborationSmoke.pending.length,
  String.intercalate "\\n\\n" (collaborationSmoke.doc.map fun b => String.ofList b.text))

/-! ## Browser intent-builder checks

These are compile-time checks for the exact entry points used by the browser
bridge. A valid replacement and kind change enter the optimistic queue; an
invalid range is rejected without changing the client.
-/

example : (ClientState.init initialDoc).applyReplace 0 0 0 0 "x" |>.isSome := by
  decide

example :
    (((ClientState.init initialDoc).applyReplace 0 0 0 0 "x").getD
      (ClientState.init initialDoc)).pending.length = 1 := by
  decide

example : (ClientState.init initialDoc).applySetKind 0 .para |>.isSome := by
  decide

example : (ClientState.init initialDoc).applyReplace 99 0 99 0 "x" = none := by
  decide
