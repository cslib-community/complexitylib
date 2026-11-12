/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.MPC.OTCommitment.Session
public import CslibFrontier.Computability.Interactive.StrategyEffect
public import CslibFrontier.Languages.Probabilistic.Oracle.Simulation

/-!
# A serial role-local OT commitment world

An original serial adapter of the existing atomic `ot14World`. The sender submits one private
table; the receiver consumes it with one private selection. A second table or a seal while that
row remains unanswered aborts, never overwrites it. Selecting without a pending row returns
`none`. Selection also requires the pre-seal phase. Sealing and abort therefore close later
selections before any opening can be read.

Sender command semantics otherwise reuse `Session.advance`: early opening is ignored, tables
and repeated seals after sealing are ignored, and the first post-seal opening attempt is terminal
even when malformed or rejected. The receiver may read that first raw attempt, including a
rejected one; explicit abort has no opening payload. Polls and opening reads do not change state.

This is a concrete execution world, not a security predicate or a claim about arbitrary schedules.
The complete-sender and fixed receiver bridges use explicit honest-party schedulers. In
particular, the honest receiver consumes a row before the complete sender resumes.

## Main definitions

* `ReceiverQuery`, `senderSpec`, `receiverSpec`: separate party interfaces.
* `Store`, `Store.send`: private serial storage and sender transitions.
* `handler`, `world`: actual OT execution with role-local replies.

## Main results

* `Store.send_receipts`: sender commands cannot change the receiver's retained OT answers.
* `handler_select_closed`: selection is disabled after sealing or termination.
* `senderOnly_output`: sender-only computation learns nothing from the world's private storage.
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.MPC.OTCommitment.Serial

open Probability Crypto.Protocols.Commitment

/-- Receiver operations. Selection consumes the next pending row, not an indexed old row. -/
inductive ReceiverQuery where
  | select (index : Fin 4)
  | poll
  | readOpening
  deriving DecidableEq

/-- Sender commands return no receiver information. -/
abbrev senderSpec : OracleSpec (SenderOperation × List Bool) := fun _ => Unit

/-- Polling retains both receipt history and the current observation. Only the receiver can
read an OT answer or the first submitted opening payload. -/
abbrev receiverSpec : OracleSpec ReceiverQuery
  | .select _ => Option Bool
  | .poll => Phased.Observation × Phased.Observation
  | .readOpening => Option (Bool × List Bool)

/-- Private functionality storage. Neither role receives this record. -/
structure Store where
  /-- Sender phase and immutable first opening attempt. -/
  session : Session := .initial
  /-- At most one unanswered OT row. -/
  pending : Option (Fin 4 → Bool) := none
  /-- Full receiver indices and actual OT answers, in execution order. -/
  receipts : List (Fin 4 × Bool) := []
  deriving DecidableEq

/-- Receiver-only public observations, retaining whether a receipt was issued. -/
def Store.observations (k : ℕ) (s : Store) : Phased.Observation × Phased.Observation :=
  (s.session.receipt, s.session.observation k
    (s.receipts.map fun r => (fin4ToBoolPair r.1).2) (s.receipts.map Prod.snd))

/-- A terminal attempted opening remains readable even if verification rejects it. An unopened
session or explicit abort has no opening payload. -/
def Store.readOpening (s : Store) : Option (Bool × List Bool) :=
  if s.session.stopped && s.session.sealed then s.session.submission else none

/-- Process sender commands with a single pending-row slot. Unanswered rows cannot be overwritten
or sealed. Terminal states are immutable; all other phase rules are the existing session rules. -/
def Store.send (k : ℕ) (request : SenderOperation × List Bool) (s : Store) : Store :=
  if s.session.stopped then s else
  if s.session.sealed then { s with session := s.session.advance k request, pending := none } else
  match request.1 with
  | .table values =>
      match s.pending with
      | some _ => { s with session := s.session.advance k (.abort, []), pending := none }
      | none =>
          { s with
            session := s.session.advance k request
            pending := if s.session.tables.length < k then some values else none }
  | .seal =>
      match s.pending with
      | some _ => { s with session := s.session.advance k (.abort, []), pending := none }
      | none => { s with session := s.session.advance k request }
  | .open _ => s
  | .abort => { s with session := s.session.advance k request, pending := none }

/-- Every sender command preserves a terminal store, including its first raw opening. -/
theorem Store.send_stopped (k : ℕ) (request : SenderOperation × List Bool) (s : Store)
    (h : s.session.stopped = true) : s.send k request = s := by
  simp [send, h]

/-- Sender calls never alter the receiver's retained indices or answers. -/
theorem Store.send_receipts (k : ℕ) (request : SenderOperation × List Bool) (s : Store) :
    (s.send k request).receipts = s.receipts := by
  rcases request with ⟨op, word⟩
  cases op <;> unfold send
  all_goals split <;> try rfl
  all_goals split <;> try rfl
  all_goals cases s.pending <;> rfl

/-- The role-local handler calls the existing OT world exactly when a fresh row is consumed. -/
noncomputable def handler (k : ℕ) :
    (q : (SenderOperation × List Bool) ⊕ ReceiverQuery) →
      StateT Store ProbComp ((senderSpec ⊕ₒ receiverSpec) q) :=
  OracleComp.sumHandler
    (fun request s => pure ((), s.send k request))
    (fun query s => match query with
      | .select index => do
          if s.session.stopped || s.session.sealed then return (none, s)
          match s.pending with
          | none => return (none, s)
          | some values =>
              let answer ← ot14World () (Fin.cases values (fun _ => index))
              let value : Bool := answer 1
              return (some value, { s with
                pending := none
                receipts := s.receipts ++ [(index, value)] })
      | .poll => pure (s.observations k, s)
      | .readOpening => pure (s.readOpening, s))

/-- The single serial session starts with no table, receipt, or opening. Its final private store
is discarded by `World.eval`. -/
noncomputable abbrev world (k : ℕ) : Interactive.World senderSpec receiverSpec where
  State := Store
  init := {}
  impl q s := ProbComp.eval (handler k q s)

/-- Sealing or termination structurally disables further selection, even in a malformed store
that still contains a pending row. -/
theorem handler_select_closed (k : ℕ) (index : Fin 4) (s : Store)
    (h : s.session.stopped = true ∨ s.session.sealed = true) :
    handler k (.inr (.select index)) s = pure (none, s) := by
  rcases h with h | h <;> simp [handler, OracleComp.sumHandler, h]

/-- Every sender-only program sees constant unit replies, independently of private receiver
indices, answers or pending storage. This does not assert hiding against sender-controlled timing
or against receiver observations after opening. -/
theorem senderOnly_output {Output : Type} (k : ℕ)
    (program : ProbOracleComp senderSpec Output) (s : Store) :
    (ProbOracleComp.runWith (fun q => (world k).impl (.inl q)) program s).map Prod.fst =
      OracleComp.evalWith (OracleComp.sumHandler ProbComp.unifOracle (fun _ => pure ()))
        program := by
  have h := ProbOracleComp.runWith_map_state
    (fun q state => (world k).impl (.inl q) state)
    (fun _ (_ : Unit) => PMF.pure ((), ())) (fun _ => ())
    (fun q state => by simp [world, handler, OracleComp.sumHandler]) program s
  have hh := congrArg (PMF.map Prod.fst) h
  have hr := ProbOracleComp.runWith_lift (fun _ : SenderOperation × List Bool =>
    PMF.pure ()) program ()
  have hu : (fun (_ : SenderOperation × List Bool) (_ : Unit) => PMF.pure ((), ())) =
      (fun _ => StateT.lift (σ := Unit) (PMF.pure ())) := by
    funext q st
    cases st
    simp [StateT.lift]
  rw [hu, hr] at hh
  simp only [PMF.map_comp, Function.comp_def] at hh
  change (ProbOracleComp.runWith (fun q => (world k).impl (.inl q)) program s).map Prod.fst =
    PMF.map id _ at hh
  rw [PMF.map_id] at hh
  exact hh

end Cslib.Crypto.Protocols.MPC.OTCommitment.Serial
