/-!
# Verified OT with block structure and undo (centralized server)

Layers:
1. `OTAlg`: an abstract operation algebra (apply / valid / inverse / transform with TP1).
2. Generic edits, server, convergence and selective undo — proven once for any `OTAlg`.
3. Instance 1: inline text (`Op α` on `List α`).
4. Instance 2: block-structured documents (`BOp α K` on `List (Block α K)`),
   with split / merge / kind change, built on instance 1.

No TP2 is needed: a central server totally orders operations.
Core Lean only (no Mathlib).
-/

namespace OT

/-- Tie-break priority for concurrent operations that would otherwise be ambiguous. -/
inductive Side where
  | left | right
  deriving DecidableEq

def Side.flip : Side → Side
  | .left => .right
  | .right => .left

@[simp] theorem Side.flip_flip (s : Side) : s.flip.flip = s := by cases s <;> rfl

/-- An operation algebra with a TP1-satisfying transform. -/
class OTAlg (O : Type) (D : outParam Type) where
  app : O → D → D
  Valid : O → D → Prop
  inv : O → O
  xf : O → O → Side → O
  tp1 : ∀ (a b : O) (s : Side) (d : D), Valid a d → Valid b d →
    app (xf a b s) (app b d) = app (xf b a s.flip) (app a d)
  valid_xf : ∀ (a b : O) (s : Side) (d : D), Valid a d → Valid b d →
    Valid (xf a b s) (app b d)
  inv_app : ∀ (o : O) (d : D), Valid o d → app (inv o) (app o d) = d
  inv_valid : ∀ (o : O) (d : D), Valid o d → Valid (inv o) (app o d)

section Generic
variable {O D : Type} [OTAlg O D]
open OTAlg

/-! ## Edits: sequences of primitive ops -/

def applyAll : List O → D → D
  | [],      d => d
  | o :: os, d => applyAll os (app o d)

def ValidSeq : List O → D → Prop
  | [],      _ => True
  | o :: os, d => Valid o d ∧ ValidSeq os (app o d)

theorem applyAll_append (xs ys : List O) (d : D) :
    applyAll (xs ++ ys) d = applyAll ys (applyAll xs d) := by
  induction xs generalizing d with
  | nil => rfl
  | cons x xs ih => exact ih _

theorem ValidSeq_append (xs ys : List O) (d : D) :
    ValidSeq (xs ++ ys) d ↔ ValidSeq xs d ∧ ValidSeq ys (applyAll xs d) := by
  induction xs generalizing d with
  | nil => simp [ValidSeq, applyAll]
  | cons x xs ih =>
    simp only [List.cons_append, ValidSeq, applyAll, ih]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩

/-- Inverse of an edit: invert each op, in reverse order. -/
def invSeq (es : List O) : List O := (es.map inv).reverse

theorem invSeq_cons (o : O) (os : List O) : invSeq (o :: os) = invSeq os ++ [inv o] := by
  simp [invSeq]

theorem invSeq_correct (es : List O) (d : D) (h : ValidSeq es d) :
    ValidSeq (invSeq es) (applyAll es d) ∧ applyAll (invSeq es) (applyAll es d) = d := by
  induction es generalizing d with
  | nil => simp [invSeq, ValidSeq, applyAll]
  | cons o os ih =>
    obtain ⟨ho, hos⟩ := h
    obtain ⟨hv, he⟩ := ih (app o d) hos
    rw [invSeq_cons]
    simp only [applyAll]
    rw [ValidSeq_append, applyAll_append, he]
    refine ⟨⟨hv, ?_⟩, ?_⟩
    · simp only [ValidSeq, and_true]
      exact OTAlg.inv_valid o d ho
    · simp only [applyAll]
      exact OTAlg.inv_app o d ho

/-- A stack of edits where the top is valid at `d`, and the next is valid after applying the top.
    This is the invariant of an undo (or redo) stack kept in head coordinates. -/
def ValidChain : List (List O) → D → Prop
  | [],      _ => True
  | u :: us, d => ValidSeq u d ∧ ValidChain us (applyAll u d)

/-- After applying a valid edit `e`, pushing its inverse keeps the chain valid. -/
theorem ValidChain.push_inv (e : List O) (d : D) (h : ValidSeq e d) (us : List (List O))
    (hus : ValidChain us d) : ValidChain (invSeq e :: us) (applyAll e d) := by
  obtain ⟨hv, heq⟩ := invSeq_correct e d h
  refine ⟨hv, ?_⟩
  rw [heq]; exact hus

/-! ## Transforming edits against edits (the OT "grid") -/

/-- Transform one op against a sequence. Returns the op moved past the sequence,
    and the sequence moved past the op. -/
def xformOne : O → List O → Side → O × List O
  | a, [], _ => (a, [])
  | a, b :: bs, s =>
      ((xformOne (xf a b s) bs s).1,
       xf b a s.flip :: (xformOne (xf a b s) bs s).2)

/-- Transform two concurrent edits against each other. `s` is the priority of the first. -/
def xformSeq : List O → List O → Side → List O × List O
  | [], bs, _ => ([], bs)
  | a :: as, bs, s =>
      ((xformOne a bs s).1 :: (xformSeq as (xformOne a bs s).2 s).1,
       (xformSeq as (xformOne a bs s).2 s).2)

theorem xformOne_correct (bs : List O) :
    ∀ (a : O) (s : Side) (d : D), Valid a d → ValidSeq bs d →
      Valid (xformOne a bs s).1 (applyAll bs d) ∧
      ValidSeq (xformOne a bs s).2 (app a d) ∧
      applyAll (xformOne a bs s).2 (app a d) = app (xformOne a bs s).1 (applyAll bs d) := by
  induction bs with
  | nil =>
    intro a s d ha _
    simp [xformOne, applyAll, ValidSeq, ha]
  | cons b bs ih =>
    intro a s d ha hbs
    obtain ⟨hb, hbs'⟩ := hbs
    have hv1 := OTAlg.valid_xf a b s d ha hb
    have hv2 := OTAlg.valid_xf b a s.flip d hb ha
    have htp := OTAlg.tp1 a b s d ha hb
    obtain ⟨i1, i2, i3⟩ := ih (xf a b s) s (app b d) hv1 hbs'
    simp only [xformOne, applyAll, ValidSeq]
    refine ⟨i1, ⟨hv2, ?_⟩, ?_⟩
    · rw [← htp]; exact i2
    · rw [← htp]; exact i3

theorem xformSeq_correct (as : List O) :
    ∀ (bs : List O) (s : Side) (d : D), ValidSeq as d → ValidSeq bs d →
      ValidSeq (xformSeq as bs s).1 (applyAll bs d) ∧
      ValidSeq (xformSeq as bs s).2 (applyAll as d) ∧
      applyAll (xformSeq as bs s).1 (applyAll bs d) =
        applyAll (xformSeq as bs s).2 (applyAll as d) := by
  induction as with
  | nil =>
    intro bs s d _ hbs
    simp [xformSeq, applyAll, ValidSeq, hbs]
  | cons a as ih =>
    intro bs s d has hbs
    obtain ⟨ha, has'⟩ := has
    obtain ⟨o1, o2, o3⟩ := xformOne_correct bs a s d ha hbs
    obtain ⟨i1, i2, i3⟩ := ih (xformOne a bs s).2 s (app a d) has' o2
    simp only [xformSeq, applyAll, ValidSeq]
    refine ⟨⟨o1, ?_⟩, i2, ?_⟩
    · rw [← o3]; exact i1
    · rw [← o3]; exact i3

/-! ## Centralized server -/

def flat : List (List O) → List O
  | []      => []
  | e :: es => e ++ flat es

theorem flat_append (xs ys : List (List O)) : flat (xs ++ ys) = flat xs ++ flat ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [flat, ih]

structure Server (O D : Type) where
  init : D
  log  : List (List O)     -- accepted edits, in server order

/-- Document after the first `n` log entries. -/
def Server.docAt (s : Server O D) (n : Nat) : D := applyAll (flat (s.log.take n)) s.init
def Server.doc (s : Server O D) : D := applyAll (flat s.log) s.init

/-- Well-formed: replaying the log from `init` never hits an invalid op. -/
def Server.Wf (s : Server O D) : Prop := ValidSeq (flat s.log) s.init

/-- A client edit made against revision `base` is transformed over everything the
    server accepted since; earlier-accepted ops win ties (`.right`). -/
def Server.submit (s : Server O D) (base : Nat) (e : List O) : Server O D × List O :=
  let e' := (xformSeq e (flat (s.log.drop base)) .right).1
  ({ s with log := s.log ++ [e'] }, e')

theorem Server.doc_split (s : Server O D) (base : Nat) :
    s.doc = applyAll (flat (s.log.drop base)) (s.docAt base) := by
  unfold Server.doc Server.docAt
  rw [← applyAll_append, ← flat_append, List.take_append_drop]

theorem Server.wf_split (s : Server O D) (h : s.Wf) (base : Nat) :
    ValidSeq (flat (s.log.drop base)) (s.docAt base) := by
  unfold Server.Wf at h
  unfold Server.docAt
  rw [← List.take_append_drop base s.log, flat_append, ValidSeq_append] at h
  exact h.2

/-- **Convergence.** The server's new document equals what the client reaches after
    applying its own edit and then the transformed concurrent server ops. -/
theorem Server.submit_converges (s : Server O D) (hwf : s.Wf) (base : Nat)
    (e : List O) (hv : ValidSeq e (s.docAt base)) :
    let r := xformSeq e (flat (s.log.drop base)) .right
    ValidSeq r.1 s.doc ∧
    ValidSeq r.2 (applyAll e (s.docAt base)) ∧
    applyAll r.2 (applyAll e (s.docAt base)) = applyAll r.1 s.doc := by
  intro r
  have h := xformSeq_correct e (flat (s.log.drop base)) .right (s.docAt base) hv
    (s.wf_split hwf base)
  rw [← s.doc_split base] at h
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1, h2, h3.symm⟩

theorem Server.submit_wf (s : Server O D) (hwf : s.Wf) (base : Nat)
    (e : List O) (hv : ValidSeq e (s.docAt base)) :
    (s.submit base e).1.Wf := by
  have h := (s.submit_converges hwf base e hv).1
  unfold Server.Wf Server.submit
  simp only [flat_append, flat, List.append_nil, ValidSeq_append]
  exact ⟨hwf, h⟩

/-! ## Selective undo -/

/-- The edit that undoes log entry `i`, already transformed over everything accepted
    after it, so it applies directly to the current head. Undoing an undo entry is redo. -/
def Server.undoEdit (s : Server O D) (i : Nat) : List O :=
  match s.log[i]? with
  | none   => []
  | some e => (xformSeq (invSeq e) (flat (s.log.drop (i + 1))) .right).1

/-- **Undo correctness.** The undo edit is valid at the head, and the resulting document
    is exactly the history *with entry `i` removed*: the later edits, transformed past
    the inverse of `i`, replayed on the state before `i`. -/
theorem Server.undo_correct (s : Server O D) (hwf : s.Wf) (i : Nat) (e : List O)
    (he : s.log[i]? = some e) :
    ValidSeq (s.undoEdit i) s.doc ∧
    applyAll (s.undoEdit i) s.doc =
      applyAll (xformSeq (invSeq e) (flat (s.log.drop (i + 1))) .right).2 (s.docAt i) := by
  have hi : i < s.log.length := (List.getElem?_eq_some_iff.mp he).1
  have hdrop : s.log.drop i = e :: s.log.drop (i + 1) := by
    rw [List.drop_eq_getElem_cons hi]
    have := (List.getElem?_eq_some_iff.mp he).2
    rw [this]
  have hwf' := s.wf_split hwf i
  rw [hdrop] at hwf'
  simp only [flat, ValidSeq_append] at hwf'
  obtain ⟨hve, hvs⟩ := hwf'
  have hdoc : s.doc = applyAll (flat (s.log.drop (i + 1))) (applyAll e (s.docAt i)) := by
    have := s.doc_split i
    rw [hdrop] at this
    simpa [flat, applyAll_append, applyAll] using this
  obtain ⟨hinv, hinv_eq⟩ := invSeq_correct e (s.docAt i) hve
  have h := xformSeq_correct (invSeq e) (flat (s.log.drop (i + 1))) .right
    (applyAll e (s.docAt i)) hinv hvs
  rw [hinv_eq, ← hdoc] at h
  obtain ⟨h1, h2, h3⟩ := h
  simp only [Server.undoEdit, he]
  exact ⟨h1, h3⟩

/-- Perform an undo: append the undo edit at the head (no further transformation needed). -/
def Server.undo (s : Server O D) (i : Nat) : Server O D :=
  { s with log := s.log ++ [s.undoEdit i] }

theorem Server.undo_wf (s : Server O D) (hwf : s.Wf) (i : Nat) (e : List O)
    (he : s.log[i]? = some e) : (s.undo i).Wf := by
  have h := (s.undo_correct hwf i e he).1
  unfold Server.Wf Server.undo
  simp only [flat_append, flat, List.append_nil, ValidSeq_append]
  exact ⟨hwf, h⟩

/-- Append an already-valid edit at the head of the log (single-user fast path). -/
def Server.append (s : Server O D) (e : List O) : Server O D := { s with log := s.log ++ [e] }

theorem Server.append_wf (s : Server O D) (hwf : s.Wf) (e : List O) (hv : ValidSeq e s.doc) :
    (s.append e).Wf := by
  unfold Server.Wf Server.append
  simp only [flat_append, flat, List.append_nil, ValidSeq_append]
  exact ⟨hwf, hv⟩

theorem Server.append_doc (s : Server O D) (e : List O) :
    (s.append e).doc = applyAll e s.doc := by
  unfold Server.doc Server.append
  simp only [flat_append, flat, List.append_nil, applyAll_append]

theorem Server.undo_doc (s : Server O D) (i : Nat) :
    (s.undo i).doc = applyAll (s.undoEdit i) s.doc := by
  unfold Server.doc Server.undo
  simp only [flat_append, flat, List.append_nil, applyAll_append]

theorem xformSeq_nil_right (es : List O) (s : Side) : xformSeq es [] s = (es, []) := by
  induction es with
  | nil => rfl
  | cons a as ih => simp [xformSeq, xformOne, ih]

/-- Sanity: undoing the *latest* entry restores the previous document exactly. -/
theorem Server.undo_last (s : Server O D) (hwf : s.Wf) (e : List O) (n : Nat)
    (hn : s.log.length = n + 1) (he : s.log[n]? = some e) :
    (s.undo n).doc = s.docAt n := by
  have h := (s.undo_correct hwf n e he).2
  have hd : s.log.drop (n + 1) = [] := List.drop_of_length_le (by omega)
  rw [hd] at h
  simp only [flat, xformSeq_nil_right] at h
  unfold Server.doc Server.undo
  simp only [flat_append, flat, List.append_nil, applyAll_append]
  exact h

end Generic


section Text
variable {α : Type}

/-! ## List helpers (total, position-indexed) -/

def insertAt : Nat → α → List α → List α
  | 0,     a, l      => a :: l
  | _ + 1, a, []     => [a]
  | n + 1, a, x :: xs => x :: insertAt n a xs

def deleteAt : Nat → List α → List α
  | _,     []      => []
  | 0,     _ :: xs => xs
  | n + 1, x :: xs => x :: deleteAt n xs

theorem length_insertAt :
    ∀ (l : List α) (p : Nat) (c : α), p ≤ l.length → (insertAt p c l).length = l.length + 1
  | [], 0, c, _ => rfl
  | [], p + 1, c, h => by simp at h
  | x :: xs, 0, c, _ => by simp [insertAt]
  | x :: xs, p + 1, c, h => by
    have h' : p ≤ xs.length := by simp at h; omega
    simp [insertAt, length_insertAt xs p c h']

theorem length_deleteAt :
    ∀ (l : List α) (p : Nat), p < l.length → (deleteAt p l).length = l.length - 1
  | [], p, h => by simp at h
  | x :: xs, 0, _ => by simp [deleteAt]
  | x :: xs, p + 1, h => by
    have h' : p < xs.length := by simp at h; omega
    have := length_deleteAt xs p h'
    simp [deleteAt, this]
    omega

theorem getElem?_insertAt_lt :
    ∀ (l : List α) (p q : Nat) (c : α), p < q → q ≤ l.length →
      (insertAt q c l)[p]? = l[p]?
  | _, p, 0, c, h, _ => absurd h (Nat.not_lt_zero _)
  | [], p, q + 1, c, _, h => by simp at h
  | x :: xs, 0, q + 1, c, _, _ => by simp [insertAt]
  | x :: xs, p + 1, q + 1, c, h, h2 => by
    have h' : q ≤ xs.length := by simp at h2; omega
    simp [insertAt]
    exact getElem?_insertAt_lt xs p q c (by omega) h'

theorem getElem?_insertAt_ge :
    ∀ (l : List α) (p q : Nat) (c : α), q ≤ p → q ≤ l.length →
      (insertAt q c l)[p + 1]? = l[p]?
  | [], p, 0, c, _, _ => by simp [insertAt]
  | [], p, q + 1, c, _, h => by simp at h
  | x :: xs, p, 0, c, _, _ => by simp [insertAt]
  | x :: xs, 0, q + 1, c, h, _ => absurd h (by omega)
  | x :: xs, p + 1, q + 1, c, h, h2 => by
    have h' : q ≤ xs.length := by simp at h2; omega
    simp [insertAt]
    exact getElem?_insertAt_ge xs p q c (by omega) h'

theorem getElem?_insertAt_self :
    ∀ (l : List α) (p : Nat) (c : α), p ≤ l.length → (insertAt p c l)[p]? = some c
  | [], 0, c, _ => by simp [insertAt]
  | [], p + 1, c, h => by simp at h
  | x :: xs, 0, c, _ => by simp [insertAt]
  | x :: xs, p + 1, c, h => by
    have h' : p ≤ xs.length := by simp at h; omega
    simp [insertAt]
    exact getElem?_insertAt_self xs p c h'

theorem getElem?_deleteAt_lt :
    ∀ (l : List α) (p q : Nat), p < q → (deleteAt q l)[p]? = l[p]?
  | [], p, q, _ => by simp [deleteAt]
  | x :: xs, p, 0, h => absurd h (Nat.not_lt_zero _)
  | x :: xs, 0, q + 1, _ => by simp [deleteAt]
  | x :: xs, p + 1, q + 1, h => by
    simp [deleteAt]
    exact getElem?_deleteAt_lt xs p q (by omega)

theorem getElem?_deleteAt_ge :
    ∀ (l : List α) (p q : Nat), q ≤ p → (deleteAt q l)[p]? = l[p + 1]?
  | [], p, q, _ => by simp [deleteAt]
  | x :: xs, p, 0, _ => by simp [deleteAt]
  | x :: xs, 0, q + 1, h => absurd h (by omega)
  | x :: xs, p + 1, q + 1, h => by
    simp [deleteAt]
    exact getElem?_deleteAt_ge xs p q (by omega)

theorem deleteAt_insertAt :
    ∀ (l : List α) (p : Nat) (c : α), p ≤ l.length → deleteAt p (insertAt p c l) = l
  | [], 0, c, _ => by simp [insertAt, deleteAt]
  | [], p + 1, c, h => by simp at h
  | x :: xs, 0, c, _ => by simp [insertAt, deleteAt]
  | x :: xs, p + 1, c, h => by
    have h' : p ≤ xs.length := by simp at h; omega
    simp [insertAt, deleteAt, deleteAt_insertAt xs p c h']

theorem insertAt_deleteAt :
    ∀ (l : List α) (p : Nat) (c : α), l[p]? = some c → insertAt p c (deleteAt p l) = l
  | [], p, c, h => by simp at h
  | x :: xs, 0, c, h => by
    simp at h
    subst h
    simp [insertAt, deleteAt]
  | x :: xs, p + 1, c, h => by
    simp at h
    simp [deleteAt, insertAt, insertAt_deleteAt xs p c h]

/-- Two inserts commute once the later position is shifted. -/
theorem insertAt_comm :
    ∀ (l : List α) (p q : Nat) (c d : α), p ≤ q → q ≤ l.length →
      insertAt (q + 1) d (insertAt p c l) = insertAt p c (insertAt q d l)
  | [], p, q, c, d, h1, h2 => by
    have hq : q = 0 := by simp at h2; omega
    have hp : p = 0 := by omega
    subst hq hp
    simp [insertAt]
  | x :: xs, 0, q, c, d, _, _ => by
    cases q <;> simp [insertAt]
  | x :: xs, p + 1, 0, c, d, h1, _ => absurd h1 (by omega)
  | x :: xs, p + 1, q + 1, c, d, h1, h2 => by
    have h' : q ≤ xs.length := by simp at h2; omega
    simp only [insertAt]
    rw [insertAt_comm xs p q c d (by omega) h']

/-- insert at `p`, delete at `q ≥ p` (delete shifted). -/
theorem deleteAt_insertAt_le :
    ∀ (l : List α) (p q : Nat) (c : α), p ≤ q → q < l.length →
      deleteAt (q + 1) (insertAt p c l) = insertAt p c (deleteAt q l)
  | [], p, q, c, _, h => by simp at h
  | x :: xs, 0, q, c, _, _ => by
    cases q <;> simp [insertAt, deleteAt]
  | x :: xs, p + 1, 0, c, h1, _ => absurd h1 (by omega)
  | x :: xs, p + 1, q + 1, c, h1, h2 => by
    have h' : q < xs.length := by simp at h2; omega
    simp only [insertAt, deleteAt]
    rw [deleteAt_insertAt_le xs p q c (by omega) h']

/-- insert at `p + 1`, delete at `q ≤ p` (insert shifted). -/
theorem deleteAt_insertAt_gt :
    ∀ (l : List α) (p q : Nat) (c : α), q ≤ p → p ≤ l.length → q < l.length →
      deleteAt q (insertAt (p + 1) c l) = insertAt p c (deleteAt q l)
  | [], p, q, c, _, _, h => by simp at h
  | x :: xs, p, 0, c, _, _, _ => by simp [insertAt, deleteAt]
  | x :: xs, 0, q + 1, c, h1, _, _ => absurd h1 (by omega)
  | x :: xs, p + 1, q + 1, c, h1, h2, h3 => by
    have h2' : p ≤ xs.length := by simp at h2; omega
    have h3' : q < xs.length := by simp at h3; omega
    simp only [insertAt, deleteAt]
    rw [deleteAt_insertAt_gt xs p q c (by omega) h2' h3']

/-- Two deletes commute (second index shifted down). -/
theorem deleteAt_comm :
    ∀ (l : List α) (p q : Nat), p ≤ q →
      deleteAt q (deleteAt p l) = deleteAt p (deleteAt (q + 1) l)
  | [], p, q, _ => by simp [deleteAt]
  | x :: xs, 0, q, _ => by simp [deleteAt]
  | x :: xs, p + 1, 0, h => absurd h (by omega)
  | x :: xs, p + 1, q + 1, h => by
    simp only [deleteAt]
    rw [deleteAt_comm xs p q (by omega)]

/-! ## Primitive operations -/

inductive Op (α : Type) where
  | nop : Op α
  | ins : Nat → α → Op α
  | del : Nat → α → Op α      -- remembers the deleted element

def Op.apply : Op α → List α → List α
  | .nop,     l => l
  | .ins p c, l => insertAt p c l
  | .del p _, l => deleteAt p l

/-- An op is valid on a document if it can be applied without clamping. -/
def Op.Valid : Op α → List α → Prop
  | .nop,     _ => True
  | .ins p _, l => p ≤ l.length
  | .del p c, l => l[p]? = some c

def Op.inv : Op α → Op α
  | .nop     => .nop
  | .ins p c => .del p c
  | .del p c => .ins p c

/-- `a.transform b s`: rewrite `a` so it applies after `b` (both concurrent). -/
def Op.transform : Op α → Op α → Side → Op α
  | .nop, _, _ => .nop
  | a, .nop, _ => a
  | .ins p c, .ins q _, s =>
      if p < q then .ins p c
      else if q < p then .ins (p + 1) c
      else match s with
        | .left  => .ins p c
        | .right => .ins (p + 1) c
  | .ins p c, .del q _, _ =>
      if p ≤ q then .ins p c else .ins (p - 1) c
  | .del p c, .ins q _, _ =>
      if p < q then .del p c else .del (p + 1) c
  | .del p c, .del q _, _ =>
      if p < q then .del p c
      else if p = q then .nop
      else .del (p - 1) c

/-! ## Validity facts -/

theorem Op.valid_del_lt {l : List α} {q : Nat} {e : α} (h : l[q]? = some e) : q < l.length := by
  obtain ⟨h, _⟩ := List.getElem?_eq_some_iff.mp h
  exact h

theorem Op.valid_transform (a b : Op α) (s : Side) (d : List α)
    (ha : a.Valid d) (hb : b.Valid d) : (a.transform b s).Valid (b.apply d) := by
  cases a with
  | nop => simp [Op.transform, Op.Valid]
  | ins p c =>
    cases b with
    | nop => simpa [Op.transform, Op.apply] using ha
    | ins q e =>
      simp only [Op.Valid] at ha hb
      have hl := length_insertAt d q e hb
      simp only [Op.transform, Op.apply]
      split
      · simp only [Op.Valid]; omega
      · split
        · simp only [Op.Valid]; omega
        · cases s <;> simp only [Op.Valid] <;> omega
    | del q e =>
      simp only [Op.Valid] at ha hb
      have hq := Op.valid_del_lt hb
      have hl := length_deleteAt d q hq
      simp only [Op.transform, Op.apply]
      split <;> simp only [Op.Valid] <;> omega
  | del p c =>
    cases b with
    | nop => simpa [Op.transform, Op.apply] using ha
    | ins q e =>
      simp only [Op.Valid] at ha hb
      simp only [Op.transform, Op.apply]
      by_cases h : p < q
      · simp only [h, if_true, Op.Valid]
        rw [getElem?_insertAt_lt d p q e h hb]; exact ha
      · simp only [h, if_false, Op.Valid]
        rw [getElem?_insertAt_ge d p q e (by omega) hb]; exact ha
    | del q e =>
      simp only [Op.Valid] at ha hb
      simp only [Op.transform, Op.apply]
      split
      · rename_i h
        simp only [Op.Valid]
        rw [getElem?_deleteAt_lt d p q h]; exact ha
      · split
        · simp [Op.Valid]
        · rename_i h1 h2
          obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
          simp only [Op.Valid, Nat.add_sub_cancel]
          rw [getElem?_deleteAt_ge d p' q (by omega)]; exact ha

/-! ## TP1 -/

theorem tp1_insIns (p q : Nat) (c e : α) (s : Side) (d : List α)
    (ha : p ≤ d.length) (hb : q ≤ d.length) :
    ((Op.ins p c).transform (.ins q e) s).apply ((Op.ins q e).apply d) =
    ((Op.ins q e).transform (.ins p c) s.flip).apply ((Op.ins p c).apply d) := by
  simp only [Op.transform, Op.apply]
  rcases Nat.lt_trichotomy p q with h | h | h
  · have h1 : ¬ q < p := by omega
    simp [h, h1, Op.apply]
    exact (insertAt_comm d p q c e (by omega) hb).symm
  · subst h
    cases s <;> simp [Side.flip, Op.apply]
    · exact (insertAt_comm d p p c e (Nat.le_refl _) hb).symm
    · exact insertAt_comm d p p e c (Nat.le_refl _) hb
  · have h1 : ¬ p < q := by omega
    simp [h, h1, Op.apply]
    exact insertAt_comm d q p e c (by omega) ha

theorem tp1_insDel (p q : Nat) (c e : α) (s : Side) (d : List α)
    (ha : p ≤ d.length) (hb : d[q]? = some e) :
    ((Op.ins p c).transform (.del q e) s).apply ((Op.del q e).apply d) =
    ((Op.del q e).transform (.ins p c) s.flip).apply ((Op.ins p c).apply d) := by
  have hq := Op.valid_del_lt hb
  simp only [Op.transform, Op.apply]
  by_cases h : p ≤ q
  · have h1 : ¬ q < p := by omega
    simp [h, h1, Op.apply]
    exact (deleteAt_insertAt_le d p q c h hq).symm
  · have h1 : q < p := by omega
    obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
    simp [h, h1, Op.apply]
    exact (deleteAt_insertAt_gt d p' q c (by omega) (by omega) hq).symm

theorem tp1_delDel (p q : Nat) (c e : α) (s : Side) (d : List α) :
    ((Op.del p c).transform (.del q e) s).apply ((Op.del q e).apply d) =
    ((Op.del q e).transform (.del p c) s.flip).apply ((Op.del p c).apply d) := by
  simp only [Op.transform, Op.apply]
  rcases Nat.lt_trichotomy p q with h | h | h
  · have h1 : ¬ q < p := by omega
    have h2 : ¬ q = p := by omega
    simp [h, h1, h2, Op.apply]
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    simp
    exact (deleteAt_comm d p q' (by omega)).symm
  · subst h
    simp [Op.apply]
  · have h1 : ¬ p < q := by omega
    have h2 : ¬ p = q := by omega
    simp [h, h1, h2, Op.apply]
    obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
    simp
    exact deleteAt_comm d q p' (by omega)

/-- **TP1**: transforming concurrent ops against each other makes both paths converge. -/
theorem Op.tp1 (a b : Op α) (s : Side) (d : List α)
    (ha : a.Valid d) (hb : b.Valid d) :
    (a.transform b s).apply (b.apply d) = (b.transform a s.flip).apply (a.apply d) := by
  cases a with
  | nop => cases b <;> simp [Op.transform, Op.apply]
  | ins p c =>
    cases b with
    | nop => simp [Op.transform, Op.apply]
    | ins q e => exact tp1_insIns p q c e s d ha hb
    | del q e => exact tp1_insDel p q c e s d ha hb
  | del p c =>
    cases b with
    | nop => simp [Op.transform, Op.apply]
    | ins q e =>
      have h := tp1_insDel q p e c s.flip d hb ha
      rw [Side.flip_flip] at h
      exact h.symm
    | del q e => exact tp1_delDel p q c e s d

/-! ## Inverses -/

theorem Op.inv_apply (o : Op α) (d : List α) (h : o.Valid d) :
    o.inv.apply (o.apply d) = d := by
  cases o with
  | nop => rfl
  | ins p c => exact deleteAt_insertAt d p c h
  | del p c => exact insertAt_deleteAt d p c h

theorem Op.inv_valid (o : Op α) (d : List α) (h : o.Valid d) :
    o.inv.Valid (o.apply d) := by
  cases o with
  | nop => trivial
  | ins p c => exact getElem?_insertAt_self d p c h
  | del p c =>
    have hq := Op.valid_del_lt h
    have := length_deleteAt d p hq
    simp only [Op.inv, Op.Valid, Op.apply]
    omega


instance : OTAlg (Op α) (List α) where
  app := Op.apply
  Valid := Op.Valid
  inv := Op.inv
  xf := Op.transform
  tp1 := Op.tp1
  valid_xf := Op.valid_transform
  inv_app := Op.inv_apply
  inv_valid := Op.inv_valid

end Text



/-! # Block-structured documents -/

section Blocks
variable {α K : Type}

structure Block (α K : Type) where
  kind : K
  text : List α

/-- Operations that act on a block, located by index. -/
inductive Core (α K : Type) where
  | inl   : Op α → Core α K        -- inline edit inside the block
  | setK  : K → K → Core α K       -- change kind: old, new
  | split : Nat → K → Core α K     -- split at text offset; new block gets this kind
  | merge : Nat → K → Core α K     -- join with next block; (length of this block, kind of next)

inductive BOp (α K : Type) where
  | nop : BOp α K
  | blk : Nat → Core α K → BOp α K

/-- How many blocks (from the index) an op reads. -/
def Core.reach : Core α K → Nat
  | .merge _ _ => 2
  | _ => 1

/-- Where an op located later is moved to by this op's effect on block numbering. -/
def Core.reindex : Core α K → Nat → Nat
  | .split _ _, j => j + 1
  | .merge _ _, j => j - 1
  | _, j => j

/-! ### Position helpers for inline ops crossing a block boundary -/

/-- Where a text boundary at `q` ends up after inline op `o`. -/
def Op.xpos : Op α → Nat → Nat
  | .nop, q => q
  | .ins p _, q => if p ≤ q then q + 1 else q
  | .del p _, q => if p < q then q - 1 else q

/-- An inline op that meets a split at `q`: which half (0/1) it lands in, and the op there. -/
def Op.splitOp : Op α → Nat → Nat × Op α
  | .nop, _ => (0, .nop)
  | .ins p c, q => if p ≤ q then (0, .ins p c) else (1, .ins (p - q) c)
  | .del p e, q => if p < q then (0, .del p e) else (1, .del (p - q) e)

/-- An inline op meeting a merge where the first block has length `q`: lands in the
    second block, so its position moves up by `q`. -/
def Op.shiftUp : Nat → Op α → Op α
  | _, .nop => .nop
  | q, .ins p c => .ins (p + q) c
  | q, .del p c => .del (p + q) c

/-! ### Semantics -/

def Core.applyHead : Core α K → List (Block α K) → List (Block α K)
  | .inl o, b :: bs => { b with text := o.apply b.text } :: bs
  | .setK _ k, b :: bs => { b with kind := k } :: bs
  | .split p k, b :: bs => { b with text := b.text.take p } :: ⟨k, b.text.drop p⟩ :: bs
  | .merge _ _, b :: b2 :: bs => { b with text := b.text ++ b2.text } :: bs
  | _, l => l

def Core.validHead : Core α K → List (Block α K) → Prop
  | .inl o, b :: _ => o.Valid b.text
  | .setK old _, b :: _ => b.kind = old
  | .split p _, b :: _ => p ≤ b.text.length
  | .merge p k, b :: b2 :: _ => b.text.length = p ∧ b2.kind = k
  | _, _ => False

def applyAt : Nat → Core α K → List (Block α K) → List (Block α K)
  | 0, c, l => c.applyHead l
  | _ + 1, _, [] => []
  | i + 1, c, b :: bs => b :: applyAt i c bs

def validAt : Nat → Core α K → List (Block α K) → Prop
  | 0, c, l => c.validHead l
  | _ + 1, _, [] => False
  | i + 1, c, _ :: bs => validAt i c bs

def Core.inv : Core α K → Core α K
  | .inl o => .inl o.inv
  | .setK a b => .setK b a
  | .split p k => .merge p k
  | .merge p k => .split p k

def BOp.apply : BOp α K → List (Block α K) → List (Block α K)
  | .nop, l => l
  | .blk i c, l => applyAt i c l

def BOp.Valid : BOp α K → List (Block α K) → Prop
  | .nop, _ => True
  | .blk i c, l => validAt i c l

def BOp.inv : BOp α K → BOp α K
  | .nop => .nop
  | .blk i c => .blk i c.inv

/-- Transform `x` so it applies after the concurrent `y`. -/
def BOp.transform : BOp α K → BOp α K → Side → BOp α K
  | .nop, _, _ => .nop
  | x, .nop, _ => x
  | .blk i (.inl o), .blk j (.inl o2), s =>
      if i = j then .blk i (.inl (o.transform o2 s)) else .blk i (.inl o)
  | .blk i (.inl o), .blk _ (.setK _ _), _ => .blk i (.inl o)
  | .blk i (.inl o), .blk j (.split q _), _ =>
      if i < j then .blk i (.inl o)
      else if j < i then .blk (i + 1) (.inl o)
      else .blk (j + (o.splitOp q).1) (.inl (o.splitOp q).2)
  | .blk i (.inl o), .blk j (.merge q _), _ =>
      if i ≤ j then .blk i (.inl o)
      else if i = j + 1 then .blk j (.inl (o.shiftUp q))
      else .blk (i - 1) (.inl o)
  | .blk i (.setK a b), .blk _ (.inl _), _ => .blk i (.setK a b)
  | .blk i (.setK a b), .blk j (.setK _ b2), s =>
      if i = j then (match s with | .left => .blk i (.setK b2 b) | .right => .nop)
      else .blk i (.setK a b)
  | .blk i (.setK a b), .blk j (.split _ _), _ =>
      if j < i then .blk (i + 1) (.setK a b) else .blk i (.setK a b)
  | .blk i (.setK a b), .blk j (.merge _ _), _ =>
      if i ≤ j then .blk i (.setK a b)
      else if i = j + 1 then .nop
      else .blk (i - 1) (.setK a b)
  | .blk i (.split p k), .blk j (.inl o), _ =>
      if i = j then .blk i (.split (o.xpos p) k) else .blk i (.split p k)
  | .blk i (.split p k), .blk _ (.setK _ _), _ => .blk i (.split p k)
  | .blk i (.split p k), .blk j (.split q _), s =>
      if i < j then .blk i (.split p k)
      else if j < i then .blk (i + 1) (.split p k)
      else if p < q then .blk i (.split p k)
      else if q < p then .blk (i + 1) (.split (p - q) k)
      else (match s with
        | .left => .blk i (.split p k)
        | .right => .blk (i + 1) (.split 0 k))
  | .blk i (.split p k), .blk j (.merge q _), _ =>
      if i ≤ j then .blk i (.split p k)
      else if i = j + 1 then .blk j (.split (q + p) k)
      else .blk (i - 1) (.split p k)
  | .blk i (.merge p k), .blk j (.inl o), _ =>
      if i = j then .blk i (.merge (o.xpos p) k) else .blk i (.merge p k)
  | .blk i (.merge p k), .blk j (.setK _ b2), _ =>
      if j = i + 1 then .blk i (.merge p b2) else .blk i (.merge p k)
  | .blk i (.merge p k), .blk j (.split q _), _ =>
      if j < i then .blk (i + 1) (.merge p k)
      else if j = i then .blk (i + 1) (.merge (p - q) k)
      else .blk i (.merge p k)
  | .blk i (.merge p k), .blk j (.merge q _), _ =>
      if j + 1 < i then .blk (i - 1) (.merge p k)
      else if j + 1 = i then .blk j (.merge (q + p) k)
      else if j = i then .nop
      else .blk i (.merge p k)

end Blocks


section ListLemmas
variable {α : Type}

theorem take_insertAt_le : ∀ (t : List α) (p q : Nat) (c : α), p ≤ q → q ≤ t.length →
    (insertAt p c t).take (q + 1) = insertAt p c (t.take q)
  | t, 0, q, c, _, _ => by simp [insertAt]
  | [], p + 1, q, c, h1, h2 => by simp at h2; omega
  | x :: xs, p + 1, 0, c, h1, _ => by omega
  | x :: xs, p + 1, q + 1, c, h1, h2 => by
    have h' : q ≤ xs.length := by simp at h2; omega
    simp [insertAt, take_insertAt_le xs p q c (by omega) h']

theorem drop_insertAt_le : ∀ (t : List α) (p q : Nat) (c : α), p ≤ q → q ≤ t.length →
    (insertAt p c t).drop (q + 1) = t.drop q
  | t, 0, q, c, _, _ => by simp [insertAt]
  | [], p + 1, q, c, h1, h2 => by simp at h2; omega
  | x :: xs, p + 1, 0, c, h1, _ => by omega
  | x :: xs, p + 1, q + 1, c, h1, h2 => by
    have h' : q ≤ xs.length := by simp at h2; omega
    simp [insertAt, drop_insertAt_le xs p q c (by omega) h']

theorem take_insertAt_gt : ∀ (t : List α) (p q : Nat) (c : α), q < p → q ≤ t.length →
    (insertAt p c t).take q = t.take q
  | _, 0, _, c, h1, _ => absurd h1 (Nat.not_lt_zero _)
  | t, p + 1, 0, c, _, _ => by simp
  | [], p + 1, q + 1, c, _, h2 => by simp at h2
  | x :: xs, p + 1, q + 1, c, h1, h2 => by
    have h' : q ≤ xs.length := by simp at h2; omega
    simp [insertAt, take_insertAt_gt xs p q c (by omega) h']

theorem drop_insertAt_gt : ∀ (t : List α) (p q : Nat) (c : α), q ≤ p → p ≤ t.length →
    (insertAt p c t).drop q = insertAt (p - q) c (t.drop q)
  | t, p, 0, c, _, _ => by simp
  | [], p, q + 1, c, h1, h2 => by simp at h2; omega
  | x :: xs, p, q + 1, c, h1, h2 => by
    obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
    have h' : p' ≤ xs.length := by simp at h2; omega
    simp [insertAt, drop_insertAt_gt xs p' q c (by omega) h']

theorem take_deleteAt_lt : ∀ (t : List α) (p q : Nat), p < q → q ≤ t.length →
    (deleteAt p t).take (q - 1) = deleteAt p (t.take q)
  | _, p, 0, h, _ => absurd h (Nat.not_lt_zero _)
  | [], p, q + 1, _, h2 => by simp at h2
  | x :: xs, 0, q + 1, _, _ => by simp [deleteAt]
  | x :: xs, p + 1, q + 1, h1, h2 => by
    have h' : q ≤ xs.length := by simp at h2; omega
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    have ih := take_deleteAt_lt xs p (q' + 1) (by omega) h'
    simp only [Nat.add_sub_cancel] at ih
    simp [deleteAt, ih]

theorem drop_deleteAt_lt : ∀ (t : List α) (p q : Nat), p < q → q ≤ t.length →
    (deleteAt p t).drop (q - 1) = t.drop q
  | _, p, 0, h, _ => absurd h (Nat.not_lt_zero _)
  | [], p, q + 1, _, h2 => by simp at h2
  | x :: xs, 0, q + 1, _, _ => by simp [deleteAt]
  | x :: xs, p + 1, q + 1, h1, h2 => by
    have h' : q ≤ xs.length := by simp at h2; omega
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    have ih := drop_deleteAt_lt xs p (q' + 1) (by omega) h'
    simp only [Nat.add_sub_cancel] at ih
    simp [deleteAt, ih]

theorem take_deleteAt_ge : ∀ (t : List α) (p q : Nat), q ≤ p →
    (deleteAt p t).take q = t.take q
  | t, p, 0, _ => by simp
  | [], p, q + 1, _ => by simp [deleteAt]
  | x :: xs, 0, q + 1, h => by omega
  | x :: xs, p + 1, q + 1, h => by
    simp [deleteAt, take_deleteAt_ge xs p q (by omega)]

theorem drop_deleteAt_ge : ∀ (t : List α) (p q : Nat), q ≤ p →
    (deleteAt p t).drop q = deleteAt (p - q) (t.drop q)
  | t, p, 0, _ => by simp
  | [], p, q + 1, _ => by simp [deleteAt]
  | x :: xs, 0, q + 1, h => by omega
  | x :: xs, p + 1, q + 1, h => by
    simp [deleteAt, drop_deleteAt_ge xs p q (by omega)]

theorem insertAt_append_left : ∀ (t t2 : List α) (p : Nat) (c : α), p ≤ t.length →
    insertAt p c (t ++ t2) = insertAt p c t ++ t2
  | t, t2, 0, c, _ => by simp [insertAt]
  | [], t2, p + 1, c, h => by simp at h
  | x :: xs, t2, p + 1, c, h => by
    have h' : p ≤ xs.length := by simp at h; omega
    simp [insertAt, insertAt_append_left xs t2 p c h']

theorem insertAt_append_right : ∀ (t t2 : List α) (p : Nat) (c : α),
    insertAt (p + t.length) c (t ++ t2) = t ++ insertAt p c t2
  | [], t2, p, c => by simp
  | x :: xs, t2, p, c => by
    have ih := insertAt_append_right xs t2 p c
    have : p + (x :: xs).length = (p + xs.length) + 1 := by simp only [List.length_cons]; omega
    rw [this]
    simp [insertAt, ih]

theorem deleteAt_append_left : ∀ (t t2 : List α) (p : Nat), p < t.length →
    deleteAt p (t ++ t2) = deleteAt p t ++ t2
  | [], t2, p, h => by simp at h
  | x :: xs, t2, 0, _ => by simp [deleteAt]
  | x :: xs, t2, p + 1, h => by
    have h' : p < xs.length := by simp at h; omega
    simp [deleteAt, deleteAt_append_left xs t2 p h']

theorem deleteAt_append_right : ∀ (t t2 : List α) (p : Nat),
    deleteAt (p + t.length) (t ++ t2) = t ++ deleteAt p t2
  | [], t2, p => by simp
  | x :: xs, t2, p => by
    have ih := deleteAt_append_right xs t2 p
    have : p + (x :: xs).length = (p + xs.length) + 1 := by simp only [List.length_cons]; omega
    rw [this]
    simp [deleteAt, ih]

theorem take_append_len (t t2 : List α) (p : Nat) :
    (t ++ t2).take (t.length + p) = t ++ t2.take p := by
  rw [List.take_append_eq_append_take, List.take_of_length_le (Nat.le_add_right _ _)]
  simp

theorem drop_append_len (t t2 : List α) (p : Nat) :
    (t ++ t2).drop (t.length + p) = t2.drop p := by
  simp [List.drop_append_eq_append_drop]

end ListLemmas


section InlineBlock
variable {α : Type}

theorem Op.splitOp_cases (o : Op α) (q : Nat) :
    (o.splitOp q).1 = 0 ∨ (o.splitOp q).1 = 1 := by
  cases o with
  | nop => simp [Op.splitOp]
  | ins p c => by_cases h : p ≤ q <;> simp [Op.splitOp, h]
  | del p e => by_cases h : p < q <;> simp [Op.splitOp, h]

/-- The op lands in the first half of a split at `q`. -/
theorem Op.splitOp_first (o : Op α) (t : List α) (q : Nat) (hv : o.Valid t)
    (hq : q ≤ t.length) (h : (o.splitOp q).1 = 0) :
    (o.splitOp q).2.Valid (t.take q) ∧
    (o.apply t).take (o.xpos q) = (o.splitOp q).2.apply (t.take q) ∧
    (o.apply t).drop (o.xpos q) = t.drop q ∧
    o.xpos q ≤ (o.apply t).length := by
  cases o with
  | nop => simp [Op.splitOp, Op.xpos, Op.Valid, Op.apply, hq]
  | ins p c =>
    simp only [Op.Valid] at hv
    by_cases hp : p ≤ q
    · have hl := length_insertAt t p c hv
      simp only [Op.splitOp, Op.xpos, Op.apply, Op.Valid, hp, if_true, List.length_take]
      refine ⟨by omega, take_insertAt_le t p q c hp hq, drop_insertAt_le t p q c hp hq, by omega⟩
    · simp [Op.splitOp, hp] at h
  | del p e =>
    simp only [Op.Valid] at hv
    have hlt := Op.valid_del_lt hv
    by_cases hp : p < q
    · have hl := length_deleteAt t p hlt
      simp only [Op.splitOp, Op.xpos, Op.apply, Op.Valid, hp, if_true]
      refine ⟨?_, take_deleteAt_lt t p q hp hq, drop_deleteAt_lt t p q hp hq, by omega⟩
      rw [List.getElem?_take_of_lt hp]; exact hv
    · simp [Op.splitOp, hp] at h

/-- The op lands in the second half of a split at `q`. -/
theorem Op.splitOp_second (o : Op α) (t : List α) (q : Nat) (hv : o.Valid t)
    (hq : q ≤ t.length) (h : (o.splitOp q).1 = 1) :
    (o.splitOp q).2.Valid (t.drop q) ∧
    (o.apply t).take (o.xpos q) = t.take q ∧
    (o.apply t).drop (o.xpos q) = (o.splitOp q).2.apply (t.drop q) ∧
    o.xpos q ≤ (o.apply t).length := by
  cases o with
  | nop => simp [Op.splitOp] at h
  | ins p c =>
    simp only [Op.Valid] at hv
    by_cases hp : p ≤ q
    · simp [Op.splitOp, hp] at h
    · have hl := length_insertAt t p c hv
      simp only [Op.splitOp, Op.xpos, Op.apply, Op.Valid, hp, if_false, List.length_drop]
      refine ⟨by omega, take_insertAt_gt t p q c (by omega) hq,
        drop_insertAt_gt t p q c (by omega) hv, by omega⟩
  | del p e =>
    simp only [Op.Valid] at hv
    have hlt := Op.valid_del_lt hv
    by_cases hp : p < q
    · simp [Op.splitOp, hp] at h
    · have hl := length_deleteAt t p hlt
      simp only [Op.splitOp, Op.xpos, Op.apply, Op.Valid, hp, if_false]
      refine ⟨?_, take_deleteAt_ge t p q (by omega), drop_deleteAt_ge t p q (by omega), by omega⟩
      rw [List.getElem?_drop]
      have : q + (p - q) = p := by omega
      rw [this]; exact hv

theorem Op.apply_append_left (o : Op α) (t t2 : List α) (hv : o.Valid t) :
    o.apply (t ++ t2) = o.apply t ++ t2 := by
  cases o with
  | nop => rfl
  | ins p c => exact insertAt_append_left t t2 p c hv
  | del p e => exact deleteAt_append_left t t2 p (Op.valid_del_lt hv)

theorem Op.apply_append_right (o : Op α) (t t2 : List α) :
    (o.shiftUp t.length).apply (t ++ t2) = t ++ o.apply t2 := by
  cases o with
  | nop => rfl
  | ins p c => exact insertAt_append_right t t2 p c
  | del p e => exact deleteAt_append_right t t2 p

theorem Op.valid_shiftUp (o : Op α) (t t2 : List α) (hv : o.Valid t2) :
    (o.shiftUp t.length).Valid (t ++ t2) := by
  cases o with
  | nop => trivial
  | ins p c =>
    simp only [Op.Valid] at hv
    simp only [Op.shiftUp, Op.Valid, List.length_append]; omega
  | del p e =>
    simp only [Op.Valid] at hv
    simp only [Op.shiftUp, Op.Valid]
    rw [List.getElem?_append_right (by omega)]
    have : p + t.length - t.length = p := by omega
    rw [this]; exact hv

theorem Op.length_apply (o : Op α) (t : List α) (hv : o.Valid t) :
    (o.apply t).length = o.xpos t.length := by
  cases o with
  | nop => rfl
  | ins p c =>
    simp only [Op.Valid] at hv
    have hl := length_insertAt t p c hv
    simp only [Op.xpos, Op.apply]
    rw [if_pos hv]; exact hl
  | del p e =>
    have hlt := Op.valid_del_lt hv
    have hl := length_deleteAt t p hlt
    simp only [Op.xpos, Op.apply]
    rw [if_pos hlt]; exact hl

end InlineBlock


section BlockProofs
variable {α K : Type}

/-! ### Basic facts -/

@[simp] theorem BOp.transform_nop_right (x : BOp α K) (s : Side) : x.transform .nop s = x := by
  cases x with
  | nop => rfl
  | blk i c => cases c <;> rfl

@[simp] theorem BOp.transform_nop_left (x : BOp α K) (s : Side) : BOp.transform .nop x s = .nop := by
  cases x <;> rfl

/-- Shift an op one block to the right. -/
def BOp.shift1 : BOp α K → BOp α K
  | .nop => .nop
  | .blk i c => .blk (i + 1) c

@[simp] theorem BOp.shift1_nop : (BOp.nop : BOp α K).shift1 = .nop := rfl
@[simp] theorem BOp.shift1_blk (i : Nat) (c : Core α K) : (BOp.blk i c).shift1 = .blk (i + 1) c := rfl
@[simp] theorem BOp.shift1_ite (p : Prop) [Decidable p] (a b : BOp α K) :
    (if p then a else b).shift1 = if p then a.shift1 else b.shift1 := by
  split <;> rfl
@[simp] theorem BOp.shift1_match_side (s : Side) (a b : BOp α K) :
    (match s with | .left => a | .right => b).shift1 =
      (match s with | .left => a.shift1 | .right => b.shift1) := by
  cases s <;> rfl

theorem BOp.apply_shift1 (x : BOp α K) (b : Block α K) (bs : List (Block α K)) :
    x.shift1.apply (b :: bs) = b :: x.apply bs := by
  cases x <;> rfl

theorem BOp.valid_shift1 (x : BOp α K) (b : Block α K) (bs : List (Block α K)) :
    x.shift1.Valid (b :: bs) ↔ x.Valid bs := by
  cases x <;> simp [BOp.Valid, validAt]

theorem xf_succ (i j : Nat) (c d : Core α K) (s : Side) :
    BOp.transform (.blk (i + 1) c) (.blk (j + 1) d) s =
      (BOp.transform (.blk i c) (.blk j d) s).shift1 := by
  cases c <;> cases d <;> (try cases s) <;>
    simp [BOp.transform] <;>
    (repeat' split) <;>
    first
      | rfl
      | omega
      | (exfalso; omega)
      | (have : i - 1 + 1 = i := by omega
         simp [this])
      | (have : j + 1 + (Op.splitOp ‹_› ‹_›).fst = j + (Op.splitOp ‹_› ‹_›).fst + 1 := by omega
         simp [this])

end BlockProofs


section BlockProofs2
variable {α K : Type}

/-! ### Inverses -/

theorem applyAt_inv : ∀ (l : List (Block α K)) (i : Nat) (c : Core α K),
    validAt i c l → applyAt i c.inv (applyAt i c l) = l
  | [], i, c, h => by cases i <;> simp [validAt, Core.validHead] at h
  | b :: bs, i + 1, c, h => by
    simp only [validAt] at h
    simp [applyAt, applyAt_inv bs i c h]
  | b :: bs, 0, c, h => by
    cases c with
    | inl o =>
      simp only [validAt, Core.validHead] at h
      simp [Core.inv, applyAt, Core.applyHead, Op.inv_apply o b.text h]
    | setK a k =>
      simp only [validAt, Core.validHead] at h
      cases b
      simp_all [Core.inv, applyAt, Core.applyHead]
    | split p k =>
      simp only [validAt, Core.validHead] at h
      simp [Core.inv, applyAt, Core.applyHead]
    | merge p k =>
      cases bs with
      | nil => simp [validAt, Core.validHead] at h
      | cons b2 bs =>
        simp only [validAt, Core.validHead] at h
        obtain ⟨h1, h2⟩ := h
        cases b; cases b2
        simp_all [Core.inv, applyAt, Core.applyHead]

theorem validAt_inv : ∀ (l : List (Block α K)) (i : Nat) (c : Core α K),
    validAt i c l → validAt i c.inv (applyAt i c l)
  | [], i, c, h => by cases i <;> simp [validAt, Core.validHead] at h
  | b :: bs, i + 1, c, h => by
    simp only [validAt] at h
    simp [applyAt, validAt, validAt_inv bs i c h]
  | b :: bs, 0, c, h => by
    cases c with
    | inl o =>
      simp only [validAt, Core.validHead] at h
      simp [Core.inv, applyAt, Core.applyHead, validAt, Core.validHead, Op.inv_valid o b.text h]
    | setK a k =>
      simp [Core.inv, applyAt, Core.applyHead, validAt, Core.validHead]
    | split p k =>
      simp only [validAt, Core.validHead] at h
      simp [Core.inv, applyAt, Core.applyHead, validAt, Core.validHead, h]
    | merge p k =>
      cases bs with
      | nil => simp [validAt, Core.validHead] at h
      | cons b2 bs =>
        simp only [validAt, Core.validHead] at h
        simp [Core.inv, applyAt, Core.applyHead, validAt, Core.validHead, h.1]

theorem BOp.inv_apply (x : BOp α K) (l : List (Block α K)) (h : x.Valid l) :
    x.inv.apply (x.apply l) = l := by
  cases x with
  | nop => rfl
  | blk i c => exact applyAt_inv l i c h

theorem BOp.inv_valid (x : BOp α K) (l : List (Block α K)) (h : x.Valid l) :
    x.inv.Valid (x.apply l) := by
  cases x with
  | nop => trivial
  | blk i c => exact validAt_inv l i c h

/-! ### Joint correctness: TP1 and validity preservation in one statement -/

def Joint (x y : BOp α K) (s : Side) (l : List (Block α K)) : Prop :=
  (x.transform y s).Valid (y.apply l) ∧ (y.transform x s.flip).Valid (x.apply l) ∧
  (x.transform y s).apply (y.apply l) = (y.transform x s.flip).apply (x.apply l)

theorem Joint.symm {x y : BOp α K} {s : Side} {l : List (Block α K)}
    (h : Joint x y s l) : Joint y x s.flip l := by
  unfold Joint at *
  rw [Side.flip_flip]
  exact ⟨h.2.1, h.1, h.2.2.symm⟩

theorem joint_nop_left (y : BOp α K) (s : Side) (l : List (Block α K)) (hy : y.Valid l) :
    Joint .nop y s l := by
  unfold Joint
  simp only [BOp.transform_nop_left, BOp.transform_nop_right]
  exact ⟨trivial, hy, rfl⟩

theorem Op.valid_append_left (o : Op α) (t t2 : List α) (hv : o.Valid t) :
    o.Valid (t ++ t2) := by
  cases o with
  | nop => trivial
  | ins p c => simp only [Op.Valid, List.length_append] at hv ⊢; omega
  | del p e =>
    simp only [Op.Valid] at hv ⊢
    rw [List.getElem?_append_left (Op.valid_del_lt hv)]; exact hv

theorem j00_inl_inl (o o2 : Op α) (s : Side) (l : List (Block α K))
    (hx : validAt 0 (.inl o) l) (hy : validAt 0 (.inl o2) l) :
    Joint (.blk 0 (.inl o)) (.blk 0 (.inl o2)) s l := by
  cases l with
  | nil => simp [validAt, Core.validHead] at hx
  | cons b bs =>
    simp only [validAt, Core.validHead] at hx hy
    simp [Joint, BOp.transform, BOp.apply, BOp.Valid, applyAt, validAt,
      Core.applyHead, Core.validHead, Op.valid_transform o o2 s _ hx hy,
      Op.valid_transform o2 o s.flip _ hy hx, Op.tp1 o o2 s _ hx hy]

theorem j00_inl_setK (o : Op α) (a a' : K) (s : Side) (l : List (Block α K))
    (hx : validAt 0 (.inl o) l) (hy : validAt 0 (.setK a a') l) :
    Joint (.blk 0 (.inl o)) (.blk 0 (.setK a a')) s l := by
  cases l with
  | nil => simp [validAt, Core.validHead] at hx
  | cons b bs =>
    simp only [validAt, Core.validHead] at hx hy
    simp [Joint, BOp.transform, BOp.apply, BOp.Valid, applyAt, validAt,
      Core.applyHead, Core.validHead, hx, hy]

theorem j00_setK_setK (a1 b1 a2 b2 : K) (s : Side) (l : List (Block α K))
    (hx : validAt 0 (.setK a1 b1) l) (hy : validAt 0 (.setK a2 b2) l) :
    Joint (.blk 0 (.setK a1 b1)) (.blk 0 (.setK a2 b2)) s l := by
  cases l with
  | nil => simp [validAt, Core.validHead] at hx
  | cons b bs =>
    simp only [validAt, Core.validHead] at hx hy
    cases s <;>
    simp [Joint, Side.flip, BOp.transform, BOp.apply, BOp.Valid, applyAt, validAt,
      Core.applyHead, Core.validHead, hx, hy]

theorem j00_setK_split (a a' : K) (q : Nat) (k : K) (s : Side) (l : List (Block α K))
    (hx : validAt 0 (.setK a a') l) (hy : validAt 0 (.split q k) l) :
    Joint (.blk 0 (.setK a a')) (.blk 0 (.split q k)) s l := by
  cases l with
  | nil => simp [validAt, Core.validHead] at hx
  | cons b bs =>
    simp only [validAt, Core.validHead] at hx hy
    simp [Joint, BOp.transform, BOp.apply, BOp.Valid, applyAt, validAt,
      Core.applyHead, Core.validHead, hx, hy]

theorem j00_setK_merge (a a' : K) (q : Nat) (k : K) (s : Side) (l : List (Block α K))
    (hx : validAt 0 (.setK a a') l) (hy : validAt 0 (.merge q k) l) :
    Joint (.blk 0 (.setK a a')) (.blk 0 (.merge q k)) s l := by
  cases l with
  | nil => simp [validAt, Core.validHead] at hx
  | cons b bs =>
    cases bs with
    | nil => simp [validAt, Core.validHead] at hy
    | cons b1 rest =>
      simp only [validAt, Core.validHead] at hx hy
      simp [Joint, BOp.transform, BOp.apply, BOp.Valid, applyAt, validAt,
        Core.applyHead, Core.validHead, hx, hy]

theorem j00_merge_merge (p : Nat) (k : K) (q : Nat) (k2 : K) (s : Side) (l : List (Block α K))
    (hx : validAt 0 (.merge p k) l) (hy : validAt 0 (.merge q k2) l) :
    Joint (.blk 0 (.merge p k)) (.blk 0 (.merge q k2)) s l := by
  cases l with
  | nil => simp [validAt, Core.validHead] at hx
  | cons b bs =>
    cases bs with
    | nil => simp [validAt, Core.validHead] at hx
    | cons b1 rest =>
      simp only [validAt, Core.validHead] at hx hy
      obtain ⟨h1, h2⟩ := hx
      obtain ⟨h3, h4⟩ := hy
      subst h1 h3 h2 h4
      simp [Joint, BOp.transform, BOp.apply, BOp.Valid, applyAt, validAt,
        Core.applyHead, Core.validHead]


theorem j00_inl_split (o : Op α) (q : Nat) (k : K) (s : Side) (l : List (Block α K))
    (hx : validAt 0 (.inl o) l) (hy : validAt 0 (.split q k) l) :
    Joint (.blk 0 (.inl o)) (.blk 0 (.split q k)) s l := by
  cases l with
  | nil => simp [validAt, Core.validHead] at hx
  | cons b bs =>
    obtain ⟨κ, t⟩ := b
    simp only [validAt, Core.validHead] at hx hy
    rcases Op.splitOp_cases o q with h | h
    · obtain ⟨v, e1, e2, e3⟩ := Op.splitOp_first o t q hx hy h
      simp [Joint, BOp.transform, BOp.apply, BOp.Valid, applyAt, validAt,
        Core.applyHead, Core.validHead, h, v, e1, e2, e3]
    · obtain ⟨v, e1, e2, e3⟩ := Op.splitOp_second o t q hx hy h
      simp [Joint, BOp.transform, BOp.apply, BOp.Valid, applyAt, validAt,
        Core.applyHead, Core.validHead, h, v, e1, e2, e3]

theorem j00_inl_merge (o : Op α) (q : Nat) (k : K) (s : Side) (l : List (Block α K))
    (hx : validAt 0 (.inl o) l) (hy : validAt 0 (.merge q k) l) :
    Joint (.blk 0 (.inl o)) (.blk 0 (.merge q k)) s l := by
  cases l with
  | nil => simp [validAt, Core.validHead] at hx
  | cons b bs =>
    cases bs with
    | nil => simp [validAt, Core.validHead] at hy
    | cons b1 rest =>
      obtain ⟨κ, t⟩ := b
      obtain ⟨κ1, t1⟩ := b1
      simp only [validAt, Core.validHead] at hx hy
      obtain ⟨rfl, rfl⟩ := hy
      simp [Joint, BOp.transform, BOp.apply, BOp.Valid, applyAt, validAt,
        Core.applyHead, Core.validHead, Op.valid_append_left o t t1 hx,
        Op.apply_append_left o t t1 hx, Op.length_apply o t hx]

theorem j00_split_merge (p : Nat) (k : K) (q : Nat) (k2 : K) (s : Side) (l : List (Block α K))
    (hx : validAt 0 (.split p k) l) (hy : validAt 0 (.merge q k2) l) :
    Joint (.blk 0 (.split p k)) (.blk 0 (.merge q k2)) s l := by
  cases l with
  | nil => simp [validAt, Core.validHead] at hx
  | cons b bs =>
    cases bs with
    | nil => simp [validAt, Core.validHead] at hy
    | cons b1 rest =>
      obtain ⟨κ, t⟩ := b
      obtain ⟨κ1, t1⟩ := b1
      simp only [validAt, Core.validHead] at hx hy
      obtain ⟨rfl, rfl⟩ := hy
      have hl : p ≤ t.length := hx
      simp [Joint, BOp.transform, BOp.apply, BOp.Valid, applyAt, validAt,
        Core.applyHead, Core.validHead, hl, List.take_append_of_le_length hl,
        List.drop_append_of_le_length hl]
      omega

theorem j00_split_split_lt (p : Nat) (k : K) (q : Nat) (k2 : K) (s : Side) (l : List (Block α K))
    (hx : validAt 0 (.split p k) l) (hy : validAt 0 (.split q k2) l) (h : p < q) :
    Joint (.blk 0 (.split p k)) (.blk 0 (.split q k2)) s l := by
  cases l with
  | nil => simp [validAt, Core.validHead] at hx
  | cons b bs =>
    obtain ⟨κ, t⟩ := b
    simp only [validAt, Core.validHead] at hx hy
    have h1 : ¬ q < p := by omega
    have e : p + (q - p) = q := by omega
    simp [Joint, BOp.transform, BOp.apply, BOp.Valid, applyAt, validAt,
      Core.applyHead, Core.validHead, h, h1, e, List.drop_take, List.length_take,
      List.take_take, Nat.min_eq_left (Nat.le_of_lt h)]
    omega

theorem j00_split_split_eq (p : Nat) (k : K) (k2 : K) (s : Side) (l : List (Block α K))
    (hx : validAt 0 (.split p k) l) (hy : validAt 0 (.split p k2) l) :
    Joint (.blk 0 (.split p k)) (.blk 0 (.split p k2)) s l := by
  cases l with
  | nil => simp [validAt, Core.validHead] at hx
  | cons b bs =>
    obtain ⟨κ, t⟩ := b
    simp only [validAt, Core.validHead] at hx hy
    cases s <;>
    simp [Joint, Side.flip, BOp.transform, BOp.apply, BOp.Valid, applyAt, validAt,
      Core.applyHead, Core.validHead, hx, hy, List.take_take]

theorem j00_split_split (p : Nat) (k : K) (q : Nat) (k2 : K) (s : Side) (l : List (Block α K))
    (hx : validAt 0 (.split p k) l) (hy : validAt 0 (.split q k2) l) :
    Joint (.blk 0 (.split p k)) (.blk 0 (.split q k2)) s l := by
  rcases Nat.lt_trichotomy p q with h | h | h
  · exact j00_split_split_lt p k q k2 s l hx hy h
  · subst h; exact j00_split_split_eq p k k2 s l hx hy
  · have := (j00_split_split_lt q k2 p k s.flip l hy hx h).symm
    rwa [Side.flip_flip] at this

theorem Joint.of_symm {x y : BOp α K} {s : Side} {l : List (Block α K)}
    (h : Joint y x s.flip l) : Joint x y s l := by
  have := h.symm
  rwa [Side.flip_flip] at this

theorem joint_00 (c d : Core α K) (s : Side) (l : List (Block α K))
    (hx : validAt 0 c l) (hy : validAt 0 d l) : Joint (.blk 0 c) (.blk 0 d) s l := by
  cases c with
  | inl o =>
    cases d with
    | inl o2 => exact j00_inl_inl o o2 s l hx hy
    | setK a a' => exact j00_inl_setK o a a' s l hx hy
    | split q k => exact j00_inl_split o q k s l hx hy
    | merge q k => exact j00_inl_merge o q k s l hx hy
  | setK a a' =>
    cases d with
    | inl o => exact .of_symm (j00_inl_setK o a a' s.flip l hy hx)
    | setK b b' => exact j00_setK_setK a a' b b' s l hx hy
    | split q k => exact j00_setK_split a a' q k s l hx hy
    | merge q k => exact j00_setK_merge a a' q k s l hx hy
  | split p k =>
    cases d with
    | inl o => exact .of_symm (j00_inl_split o p k s.flip l hy hx)
    | setK a a' => exact .of_symm (j00_setK_split a a' p k s.flip l hy hx)
    | split q k2 => exact j00_split_split p k q k2 s l hx hy
    | merge q k2 => exact j00_split_merge p k q k2 s l hx hy
  | merge p k =>
    cases d with
    | inl o => exact .of_symm (j00_inl_merge o p k s.flip l hy hx)
    | setK a a' => exact .of_symm (j00_setK_merge a a' p k s.flip l hy hx)
    | split q k2 => exact .of_symm (j00_split_merge q k2 p k s.flip l hy hx)
    | merge q k2 => exact j00_merge_merge p k q k2 s l hx hy

theorem joint_far1 (c d : Core α K) (s : Side) (b : Block α K) (bs : List (Block α K)) (j : Nat)
    (hc : c.reach = 1) (hx : validAt 0 c (b :: bs)) (hy : validAt (j + 1) d (b :: bs)) :
    Joint (.blk 0 c) (.blk (j + 1) d) s (b :: bs) := by
  cases c <;> cases d <;>
  simp_all [Core.reach, Joint, BOp.transform, BOp.apply, BOp.Valid, applyAt, validAt,
    Core.applyHead, Core.validHead]

theorem joint_far2 (p : Nat) (k : K) (d : Core α K) (s : Side) (b : Block α K)
    (bs : List (Block α K)) (j : Nat)
    (hx : validAt 0 (.merge p k) (b :: bs)) (hy : validAt (j + 2) d (b :: bs)) :
    Joint (.blk 0 (.merge p k)) (.blk (j + 2) d) s (b :: bs) := by
  cases bs with
  | nil => simp [validAt] at hy
  | cons b1 rest =>
    cases d <;>
    simp_all [Joint, BOp.transform, BOp.apply, BOp.Valid, applyAt, validAt,
      Core.applyHead, Core.validHead]

theorem joint_merge1 (p : Nat) (k : K) (d : Core α K) (s : Side) (b : Block α K)
    (bs : List (Block α K))
    (hx : validAt 0 (.merge p k) (b :: bs)) (hy : validAt 1 d (b :: bs)) :
    Joint (.blk 0 (.merge p k)) (.blk 1 d) s (b :: bs) := by
  cases bs with
  | nil => simp [validAt, Core.validHead] at hx
  | cons b1 rest =>
    obtain ⟨b⟩ := b
    obtain ⟨b1⟩ := b1
    simp only [validAt, Core.validHead] at hx
    obtain ⟨rfl, rfl⟩ := hx
    cases d with
    | inl o =>
      simp only [validAt, Core.validHead] at hy
      simp [Joint, BOp.transform, BOp.apply, BOp.Valid, applyAt, validAt,
        Core.applyHead, Core.validHead, Op.apply_append_right, Op.valid_shiftUp _ _ _ hy, hy]
    | setK a a' =>
      simp_all [Joint, BOp.transform, BOp.apply, BOp.Valid, applyAt, validAt,
        Core.applyHead, Core.validHead]
    | split a k2 =>
      simp only [validAt, Core.validHead] at hy
      simp [Joint, BOp.transform, BOp.apply, BOp.Valid, applyAt, validAt,
        Core.applyHead, Core.validHead, take_append_len, drop_append_len, hy]
    | merge a k2 =>
      cases rest with
      | nil => simp [validAt, Core.validHead] at hy
      | cons b2 rest2 =>
        obtain ⟨b2⟩ := b2
        simp only [validAt, Core.validHead] at hy
        obtain ⟨rfl, rfl⟩ := hy
        simp [Joint, BOp.transform, BOp.apply, BOp.Valid, applyAt, validAt,
          Core.applyHead, Core.validHead]

theorem joint_head (c d : Core α K) (j : Nat) (s : Side) (b : Block α K) (bs : List (Block α K))
    (hx : validAt 0 c (b :: bs)) (hy : validAt j d (b :: bs)) :
    Joint (.blk 0 c) (.blk j d) s (b :: bs) := by
  cases j with
  | zero => exact joint_00 c d s (b :: bs) hx hy
  | succ j' =>
    cases c with
    | merge p k =>
      cases j' with
      | zero => exact joint_merge1 p k d s b bs hx hy
      | succ j'' => exact joint_far2 p k d s b bs j'' hx hy
    | inl o => exact joint_far1 _ d s b bs j' rfl hx hy
    | setK a a' => exact joint_far1 _ d s b bs j' rfl hx hy
    | split p k => exact joint_far1 _ d s b bs j' rfl hx hy

theorem apply_blk_succ (i : Nat) (c : Core α K) (b : Block α K) (bs : List (Block α K)) :
    (BOp.blk (i + 1) c).apply (b :: bs) = b :: (BOp.blk i c).apply bs := rfl

theorem joint_all : ∀ (l : List (Block α K)) (x y : BOp α K) (s : Side),
    x.Valid l → y.Valid l → Joint x y s l
  | l, .nop, y, s, _, hy => joint_nop_left y s l hy
  | l, .blk i c, .nop, s, hx, _ => by
    have := (joint_nop_left (.blk i c) s.flip l hx).symm
    rwa [Side.flip_flip] at this
  | [], .blk i c, .blk j d, s, hx, _ => by
    cases i <;> simp [BOp.Valid, validAt, Core.validHead] at hx
  | b :: bs, .blk 0 c, .blk j d, s, hx, hy => joint_head c d j s b bs hx hy
  | b :: bs, .blk (i + 1) c, .blk 0 d, s, hx, hy => by
    have := (joint_head d c (i + 1) s.flip b bs hy hx).symm
    rwa [Side.flip_flip] at this
  | b :: bs, .blk (i + 1) c, .blk (j + 1) d, s, hx, hy => by
    have ih := joint_all bs (.blk i c) (.blk j d) s hx hy
    unfold Joint at *
    simp only [xf_succ, apply_blk_succ, BOp.apply_shift1, BOp.valid_shift1]
    exact ⟨ih.1, ih.2.1, by rw [ih.2.2]⟩

end BlockProofs2


section BlockInstance
variable {α K : Type}

/-- **TP1 for block operations.** -/
theorem BOp.tp1 (x y : BOp α K) (s : Side) (l : List (Block α K))
    (hx : x.Valid l) (hy : y.Valid l) :
    (x.transform y s).apply (y.apply l) = (y.transform x s.flip).apply (x.apply l) :=
  (joint_all l x y s hx hy).2.2

/-- Transformed block operations stay valid. -/
theorem BOp.valid_transform (x y : BOp α K) (s : Side) (l : List (Block α K))
    (hx : x.Valid l) (hy : y.Valid l) : (x.transform y s).Valid (y.apply l) :=
  (joint_all l x y s hx hy).1

instance : OTAlg (BOp α K) (List (Block α K)) where
  app := BOp.apply
  Valid := BOp.Valid
  inv := BOp.inv
  xf := BOp.transform
  tp1 := fun a b s d ha hb => BOp.tp1 a b s d ha hb
  valid_xf := fun a b s d ha hb => BOp.valid_transform a b s d ha hb
  inv_app := BOp.inv_apply
  inv_valid := BOp.inv_valid

end BlockInstance

/-! ## Demo -/

inductive Kind where
  | para | h1 | h2 | item | quote
  deriving Repr, DecidableEq

def render (d : List (Block Char Kind)) : List (String × String) :=
  d.map fun b => (reprStr b.kind, String.mk b.text)

def demo : Server (BOp Char Kind) (List (Block Char Kind)) :=
  { init := [⟨.para, "ab".toList⟩, ⟨.para, "cd".toList⟩], log := [] }

-- A presses Enter inside block 0; B (stale, revision 0) appends "X" to block 1
-- and turns block 0 into a heading. Then A's split is undone.
#eval
  let (s1, _) := demo.submit 0 [.blk 0 (.split 1 .para)]
  let (s2, _) := s1.submit 0 [.blk 1 (.inl (.ins 2 'X')), .blk 0 (.setK .para .h1)]
  let s3 := s2.undo 0
  (render s2.doc, render s3.doc)


/-! # Documents with referenced tables: a keyed product of two algebras

The main document contains opaque `table id` elements. Each table cell is a separate
document living in a store keyed by `κ` (e.g. table, row, column). A world is
`main document × (key → cell document)`; an op targets either the main document or one cell.
Ops on different keys commute; ops on the same key delegate to that key's own transform.
-/

section World
variable {O1 O2 D1 D2 κ D : Type}

/-- Functional update of the cell store. -/
def upd [DecidableEq κ] (f : κ → D) (k : κ) (v : D) : κ → D :=
  fun k' => if k' = k then v else f k'

theorem upd_same [DecidableEq κ] (f : κ → D) (k : κ) (v : D) : upd f k v k = v := by
  simp [upd]

theorem upd_other [DecidableEq κ] (f : κ → D) (k k' : κ) (v : D) (h : k ≠ k') :
    upd f k' v k = f k := by
  simp [upd, h]

theorem upd_upd [DecidableEq κ] (f : κ → D) (k : κ) (v w : D) :
    upd (upd f k v) k w = upd f k w := by
  funext x; by_cases hx : x = k <;> simp [upd, hx]

theorem upd_self [DecidableEq κ] (f : κ → D) (k : κ) : upd f k (f k) = f := by
  funext x; by_cases hx : x = k <;> simp [upd, hx]

theorem upd_comm [DecidableEq κ] (f : κ → D) (k k' : κ) (v w : D) (h : k ≠ k') :
    upd (upd f k v) k' w = upd (upd f k' w) k v := by
  funext x
  by_cases hx : x = k
  · subst hx; simp [upd, h]
  · by_cases hy : x = k'
    · subst hy; simp [upd, hx]
    · simp [upd, hx, hy]

inductive WOp (O1 O2 κ : Type) where
  | main : O1 → WOp O1 O2 κ
  | cell : κ → O2 → WOp O1 O2 κ

open OTAlg in
def WOp.app [DecidableEq κ] [OTAlg O1 D1] [OTAlg O2 D2] :
    WOp O1 O2 κ → D1 × (κ → D2) → D1 × (κ → D2)
  | .main o, w => (OTAlg.app o w.1, w.2)
  | .cell k o, w => (w.1, upd w.2 k (OTAlg.app o (w.2 k)))

def WOp.Valid [OTAlg O1 D1] [OTAlg O2 D2] :
    WOp O1 O2 κ → D1 × (κ → D2) → Prop
  | .main o, w => OTAlg.Valid o w.1
  | .cell k o, w => OTAlg.Valid o (w.2 k)

def WOp.inv [OTAlg O1 D1] [OTAlg O2 D2] : WOp O1 O2 κ → WOp O1 O2 κ
  | .main o => .main (OTAlg.inv o)
  | .cell k o => .cell k (OTAlg.inv o)

def WOp.xf [DecidableEq κ] [OTAlg O1 D1] [OTAlg O2 D2] :
    WOp O1 O2 κ → WOp O1 O2 κ → Side → WOp O1 O2 κ
  | .main a, .main b, s => .main (OTAlg.xf a b s)
  | .main a, .cell _ _, _ => .main a
  | .cell k a, .main _, _ => .cell k a
  | .cell k a, .cell k' b, s => if k = k' then .cell k (OTAlg.xf a b s) else .cell k a

theorem WOp.tp1 [DecidableEq κ] [OTAlg O1 D1] [OTAlg O2 D2]
    (a b : WOp O1 O2 κ) (s : Side) (w : D1 × (κ → D2))
    (ha : a.Valid w) (hb : b.Valid w) :
    (a.xf b s).app (b.app w) = (b.xf a s.flip).app (a.app w) := by
  cases a with
  | main a =>
    cases b with
    | main b =>
      simp only [WOp.Valid] at ha hb
      simp [WOp.xf, WOp.app, OTAlg.tp1 a b s w.1 ha hb]
    | cell k b => simp [WOp.xf, WOp.app]
  | cell k a =>
    cases b with
    | main b => simp [WOp.xf, WOp.app]
    | cell k' b =>
      simp only [WOp.Valid] at ha hb
      by_cases h : k = k'
      · subst h
        simp [WOp.xf, WOp.app, upd_same, upd_upd, OTAlg.tp1 a b s (w.2 k) ha hb]
      · have h' : ¬ k' = k := fun e => h e.symm
        simp [WOp.xf, WOp.app, h, h', upd_other _ _ _ _ h, upd_other _ _ _ _ h', upd_comm _ _ _ _ _ h]

theorem WOp.valid_xf [DecidableEq κ] [OTAlg O1 D1] [OTAlg O2 D2]
    (a b : WOp O1 O2 κ) (s : Side) (w : D1 × (κ → D2))
    (ha : a.Valid w) (hb : b.Valid w) : (a.xf b s).Valid (b.app w) := by
  cases a with
  | main a =>
    cases b with
    | main b => exact OTAlg.valid_xf a b s w.1 ha hb
    | cell k b => simpa [WOp.xf, WOp.Valid, WOp.app] using ha
  | cell k a =>
    cases b with
    | main b => simpa [WOp.xf, WOp.Valid, WOp.app] using ha
    | cell k' b =>
      simp only [WOp.Valid] at ha hb
      by_cases h : k = k'
      · subst h
        simp only [WOp.xf, WOp.Valid, WOp.app, if_true, upd_same]
        exact OTAlg.valid_xf a b s (w.2 k) ha hb
      · simp [WOp.xf, WOp.Valid, WOp.app, h, upd_other _ _ _ _ h, ha]

theorem WOp.inv_app [DecidableEq κ] [OTAlg O1 D1] [OTAlg O2 D2]
    (o : WOp O1 O2 κ) (w : D1 × (κ → D2)) (h : o.Valid w) :
    o.inv.app (o.app w) = w := by
  cases o with
  | main o => simp [WOp.inv, WOp.app, OTAlg.inv_app o w.1 h]
  | cell k o =>
    simp only [WOp.Valid] at h
    simp [WOp.inv, WOp.app, upd_same, upd_upd, OTAlg.inv_app o (w.2 k) h, upd_self]

theorem WOp.inv_valid [DecidableEq κ] [OTAlg O1 D1] [OTAlg O2 D2]
    (o : WOp O1 O2 κ) (w : D1 × (κ → D2)) (h : o.Valid w) :
    o.inv.Valid (o.app w) := by
  cases o with
  | main o => exact OTAlg.inv_valid o w.1 h
  | cell k o =>
    simp only [WOp.Valid] at h
    simp only [WOp.inv, WOp.Valid, WOp.app, upd_same]
    exact OTAlg.inv_valid o (w.2 k) h

instance [DecidableEq κ] [OTAlg O1 D1] [OTAlg O2 D2] :
    OTAlg (WOp O1 O2 κ) (D1 × (κ → D2)) where
  app := WOp.app
  Valid := WOp.Valid
  inv := WOp.inv
  xf := WOp.xf
  tp1 := WOp.tp1
  valid_xf := WOp.valid_xf
  inv_app := WOp.inv_app
  inv_valid := WOp.inv_valid

end World

/-! ## Demo: a table reference in the text, cells edited concurrently -/

inductive Inline where
  | ch : Char → Inline
  | table : Nat → Inline         -- reference to a table by id

abbrev CellKey := Nat × Nat × Nat   -- (table id, row, column)
abbrev CellDoc := List (Block Inline Kind)
abbrev WorldDoc := CellDoc × (CellKey → CellDoc)
abbrev WorldOp := WOp (BOp Inline Kind) (BOp Inline Kind) CellKey

def showInline : Inline → String
  | .ch c => c.toString
  | .table n => s!"[table {n}]"

def showDoc (d : CellDoc) : List String :=
  d.map fun b => String.join (b.text.map showInline)

def emptyCell : CellDoc := [⟨.para, []⟩]

def worldDemo : Server WorldOp WorldDoc :=
  { init := ([⟨.para, [.ch 'a', .table 7]⟩], fun _ => emptyCell), log := [] }

def typeInCell (key : CellKey) (txt : String) : List WorldOp :=
  txt.toList.zipIdx.map fun (c, i) => .cell key (.blk 0 (.inl (.ins i (.ch c))))

-- Two users, both at revision 0: one types in cell (7,0,0) and the other types in
-- cell (7,0,1) and in the main text. Then the cell edit is undone.
#eval
  let (s1, _) := worldDemo.submit 0 (typeInCell (7, 0, 0) "hi")
  let (s2, _) := s1.submit 0 (typeInCell (7, 0, 1) "yo" ++ ([.main (.blk 0 (.inl (.ins 0 (.ch '>'))))] : List WorldOp))
  let s3 := s2.undo 0
  let (m2, c2) := s2.doc
  let (m3, c3) := s3.doc
  ((showDoc m2, showDoc (c2 (7, 0, 0)), showDoc (c2 (7, 0, 1))),
   (showDoc m3, showDoc (c3 (7, 0, 0)), showDoc (c3 (7, 0, 1))))

end OT
