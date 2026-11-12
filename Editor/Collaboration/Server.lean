import Editor.Collaboration

open OT

/-!
# Revisioned collaboration server core

The server is the single serialization point for concurrent edits. A request
contains the revision of the snapshot on which its operations were built.
Accepted operations are transformed over every server-log entry since that
revision using the verified centralized-server algorithm in `OT.Server.submit`.

This module is deliberately transport-independent: HTTP/WebSocket framing,
authentication, request de-duplication, and persistence belong in the adapter.
-/

/-- Stable client/request metadata carried through the acceptance boundary. -/
structure SubmitRequest where
  clientId : String
  requestId : String
  baseRevision : Nat
  edit : BOps

/-- Receipt for one edit accepted into the total server order. -/
structure SubmitReceipt where
  clientId : String
  requestId : String
  revision : Nat
  acceptedEdit : BOps
  document : BDoc

/-- A server snapshot together with the proof that its complete log replays. -/
structure CollaborationServer where
  srv : BSrv
  wf : srv.Wf
  /-- Accepted edit revisions available to the room-wide undo command. -/
  undoHistory : List Nat
  /-- Pairs of (original revision, undo-record revision) available to redo. -/
  redoHistory : List (Nat × Nat)
  /-- Client/request identity for each server-log revision; empty for room undo/redo. -/
  receipts : List (String × String)

namespace CollaborationServer

/-- Start a collaboration room at revision zero. -/
def init (doc : BDoc) : CollaborationServer where
  srv := ⟨doc, []⟩
  wf := trivial
  undoHistory := []
  redoHistory := []
  receipts := []

/-- Current monotonically increasing server revision. -/
def revision (s : CollaborationServer) : Nat :=
  s.srv.log.length

/-- Accept an edit created against an earlier revision.

The caller must establish that the revision exists and that the edit is valid
against that historical snapshot. The accepted edit is transformed over the
intervening server log; the resulting server retains its replay-validity proof.
-/
def submit (s : CollaborationServer) (base : Nat) (edit : BOps)
    (_hbase : base ≤ s.revision)
    (hedit : ValidSeq edit (s.srv.docAt base)) :
    CollaborationServer × BOps := by
  let next := s.srv.submit base edit
  have hnext : next.1.Wf := s.srv.submit_wf s.wf base edit hedit
  exact (⟨next.1, hnext, s.revision :: s.undoHistory, [], s.receipts ++ [("", "")]⟩, next.2)

/-- The transformed edit returned by submit is valid at the previous head. -/
theorem submit_accepted_valid (s : CollaborationServer) (base : Nat)
    (edit : BOps) (hbase : base ≤ s.revision)
    (hedit : ValidSeq edit (s.srv.docAt base)) :
    ValidSeq (s.submit base edit hbase hedit).2 s.srv.doc := by
  change ValidSeq
    (xformSeq edit (flat (s.srv.log.drop base)) .right).1 s.srv.doc
  exact (s.srv.submit_converges s.wf base edit hedit).1

/-- Process a typed request and return a receipt identifying exactly which
client request was serialized at the new revision. -/
def accept (s : CollaborationServer) (request : SubmitRequest)
    (hbase : request.baseRevision ≤ s.revision)
    (hedit : ValidSeq request.edit (s.srv.docAt request.baseRevision)) :
    CollaborationServer × SubmitReceipt := by
  let (next, accepted) :=
    s.submit request.baseRevision request.edit hbase hedit
  let next := { next with receipts := s.receipts ++ [(request.clientId, request.requestId)] }
  exact (next, {
    clientId := request.clientId
    requestId := request.requestId
    revision := next.revision
    acceptedEdit := accepted
    document := next.srv.doc
  })


/-- Undo the most recently accepted edit in the shared room. The inverse is
transformed over every later server operation by the verified selective-undo
algorithm in `Server.undo`. -/
def undo (s : CollaborationServer) : Option CollaborationServer :=
  match s.undoHistory with
  | [] => none
  | target :: rest =>
    match h : s.srv.log[target]? with
    | none => none
    | some edit =>
      let next := s.srv.undo target
      some {
        srv := next
        wf := Server.undo_wf s.srv s.wf target edit h
        undoHistory := rest
        redoHistory := (target, s.revision) :: s.redoHistory
        receipts := s.receipts ++ [("", "")]
      }

/-- Redo the most recently undone edit by selectively undoing its undo record. -/
def redo (s : CollaborationServer) : Option CollaborationServer :=
  match s.redoHistory with
  | [] => none
  | (target, undoRevision) :: rest =>
    match h : s.srv.log[undoRevision]? with
    | none => none
    | some undoEdit =>
      let next := s.srv.undo undoRevision
      some {
        srv := next
        wf := Server.undo_wf s.srv s.wf undoRevision undoEdit h
        undoHistory := target :: s.undoHistory
        redoHistory := rest
        receipts := s.receipts ++ [("", "")]
      }

end CollaborationServer

/-! ## Two stale-base submissions

Both clients edit revision zero. The server accepts the first edit, then
transforms the second over it and serializes both without discarding either.
-/

def collaborationServerSmoke : CollaborationServer := by
  let s0 := CollaborationServer.init initialDoc
  let alice : BOps := [.blk 0 (.inl (.ins 0 '!'))]
  let bob : BOps := [.blk 2 (.inl (.ins 0 '?'))]
  have ha : ValidSeq alice initialDoc := by decide
  have hb : ValidSeq bob initialDoc := by decide
  let s1 := (s0.submit 0 alice (by decide) ha).1
  have hbase1 : 0 ≤ s1.revision := by
    simp [s1, s0, CollaborationServer.revision, CollaborationServer.submit,
      CollaborationServer.init, Server.submit]
  have hb1 : ValidSeq bob (s1.srv.docAt 0) := by
    simpa [s1, s0, Server.docAt, CollaborationServer.submit,
      CollaborationServer.init, Server.submit, flat, applyAll] using hb
  let s2 := (s1.submit 0 bob hbase1 hb1).1
  exact s2

#eval (collaborationServerSmoke.revision,
  String.intercalate "\\n\\n"
    (collaborationServerSmoke.srv.doc.map fun b => String.ofList b.text))
