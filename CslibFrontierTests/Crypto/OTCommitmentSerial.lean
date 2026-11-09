/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.MPC.OTCommitment.Serial.CompleteSender
public import CslibFrontier.Crypto.Protocols.MPC.OTCommitment.Serial.Receiver

/-! # Serial OT scheduling and joint execution clients -/

public section

open Cslib Cslib.Probability Cslib.Crypto.Protocols.MPC
open Cslib.Crypto.Protocols.MPC.OTCommitment Cslib.Crypto.Protocols.Commitment
open Cslib.Crypto.Protocols.MPC.OTCommitment.Serial

namespace OTCommitmentSerialTests

private def send (request : SenderOperation × List Bool) :
    ProbOracleComp (senderSpec ⊕ₒ receiverSpec) Unit :=
  ProbOracleComp.query (spec := senderSpec ⊕ₒ receiverSpec) (.inl request)

private def select (index : Fin 4) :
    ProbOracleComp (senderSpec ⊕ₒ receiverSpec) (Option Bool) :=
  ProbOracleComp.query (spec := senderSpec ⊕ₒ receiverSpec) (.inr (.select index))

private def inspect : ProbOracleComp (senderSpec ⊕ₒ receiverSpec)
    ((Phased.Observation × Phased.Observation) × Option (Bool × List Bool)) := do
  let observed ← ProbOracleComp.query (spec := senderSpec ⊕ₒ receiverSpec) (.inr .poll)
  let raw ← ProbOracleComp.query (spec := senderSpec ⊕ₒ receiverSpec) (.inr .readOpening)
  return (observed, raw)

private theorem ot_row (values : Fin 4 → Bool) (index : Fin 4) :
    ot14World () (Fin.cases values (fun _ => index)) =
      pure (Fin.cases () (fun _ => values index)) := rfl

private theorem answer_one (value : Bool) : (Fin.cases () (fun _ : Fin 1 => value) :
    (i : Fin 2) → ot14Spec.Answer () i) 1 = value := rfl

-- One row can be consumed only once. Slot 3 uses the same parity component as slot 1.
example : (world 1).eval (do
    let before ← select 3
    send (.table (table true false), [])
    let first ← select 3
    let again ← select 2
    send (.seal, [])
    send (.open true, [false, true])
    let after ← select 2
    let view ← inspect
    return (before, first, again, after, view)) =
    pure (none, some true, none, none,
      ((Phased.Observation.receipt, .opened true), some (true, [false, true]))) := by
  simp [Interactive.World.eval, send, select, inspect, ProbOracleComp.runWith_bind,
    world, handler, OracleComp.sumHandler, Store.send, Session.advance, Session.initial,
    Store.observations, Store.readOpening, Session.receipt, Session.observation, Session.opening,
    openPairs, ot_row, answer_one, table, fin4ToBoolPair]

-- A second pending row aborts instead of overwriting the first; a pending seal also aborts.
example : (world 1).eval (do
    send (.table (table false false), [])
    send (.table (table true true), [])
    let late ← select 0
    let view ← inspect
    return (late, view)) = pure (none, ((Phased.Observation.idle, .aborted), none)) := by
  simp [Interactive.World.eval, send, select, inspect, ProbOracleComp.runWith_bind,
    world, handler, OracleComp.sumHandler, Store.send, Session.advance, Session.initial,
    Store.observations, Store.readOpening, Session.receipt, Session.observation]

example : (world 1).eval (do
    send (.table (table false false), [])
    send (.seal, [])
    let late ← select 0
    let view ← inspect
    return (late, view)) = pure (none, ((Phased.Observation.idle, .aborted), none)) := by
  simp [Interactive.World.eval, send, select, inspect, ProbOracleComp.runWith_bind,
    world, handler, OracleComp.sumHandler, Store.send, Session.advance, Session.initial,
    Store.observations, Store.readOpening, Session.receipt, Session.observation]

-- An early opening is ignored. Repeated seal, post-seal table, and post-opening abort cannot
-- replace the first released bit; zero rows still produce the actual opened-bit observation.
example : (world 0).eval (do
    send (.open false, [true])
    send (.seal, [])
    send (.seal, [])
    send (.table (table false false), [])
    send (.open true, [])
    send (.abort, [])
    inspect) = pure ((Phased.Observation.receipt, .opened true), some (true, [])) := by
  simp [Interactive.World.eval, send, inspect, ProbOracleComp.runWith_bind,
    world, handler, OracleComp.sumHandler, Store.send, Session.advance, Session.initial,
    Store.observations, Store.readOpening, Session.receipt, Session.observation, Session.opening,
    openPairs]

-- A malformed first attempt is terminal and remains readable, even after a valid retry.
example : (world 0).eval (do
    send (.seal, [])
    send (.open true, [false])
    let first ← inspect
    send (.open false, [])
    let second ← inspect
    return (first, second)) = pure
      (((Phased.Observation.receipt, .aborted), some (true, [false])),
        ((Phased.Observation.receipt, .aborted), some (true, [false]))) := by
  simp [Interactive.World.eval, send, inspect, ProbOracleComp.runWith_bind,
    world, handler, OracleComp.sumHandler, Store.send, Session.advance, Session.initial,
    Store.observations, Store.readOpening, Session.receipt, Session.observation, Session.opening,
    openPairs]

-- Even an unreachable malformed store cannot enable selection after sealing.
example : handler 1 (.inr (.select 0))
    { session := { sealed := true }, pending := some (table true false) } =
    pure (none, { session := { sealed := true }, pending := some (table true false) }) :=
  handler_select_closed _ _ _ (Or.inr rfl)

-- The attempted opening (false,true) for a constant-false table is accepted for choice 0
-- and rejected for choice 1. Choosing after seeing that opening would change the law.
example : openPairs [false] [false] (some (true, [(false, true)])) = some true ∧
    openPairs [true] [false] (some (true, [(false, true)])) = none := by decide

-- The actual world freezes the already selected component; a later choice cannot repair it.
example : (world 1).eval (do
    send (.table (table false false), [])
    let _ ← select 1
    send (.seal, [])
    send (.open true, [false, true])
    let late ← select 0
    let view ← inspect
    return (late, view)) =
    pure (none, ((Phased.Observation.receipt, .aborted), some (true, [false, true]))) := by
  simp [Interactive.World.eval, send, select, inspect, ProbOracleComp.runWith_bind,
    world, handler, OracleComp.sumHandler, Store.send, Session.advance, Session.initial,
    Store.observations, Store.readOpening, Session.receipt, Session.observation, Session.opening,
    openPairs, ot_row, answer_one, table, fin4ToBoolPair]

private def commands : List (SenderOperation × List Bool) → WordOracleComp SenderOperation Unit
  | [] => pure ()
  | request :: rest => do
      let _ ← ProbOracleComp.query request
      commands rest

-- The complete adversary adapter really routes its commands through the shared world.
example : (world 0).eval (senderAdapter 0
    (commands [(.seal, []), (.open true, [false]), (.open false, [])])) =
    pure (Phased.Observation.receipt, .aborted, ()) := by
  rw [eval_senderAdapter]
  have hs : sessionProgram 0
      (commands [(.seal, []), (.open true, [false]), (.open false, [])]) =
      pure ((), { sealed := true, stopped := true, submission := some (true, [false]) }) := rfl
  simp [eval_completeSenderReal, hs, Session.receipt, Session.observation, Session.opening,
    selectedBits, openPairs]

-- A private coin chooses the duplicate slot, and the previous selected answer chooses parity.
noncomputable def choose (_ : ℕ) (state : Bool × List Bool) :
    ProbComp (Fin 4 × (Bool × List Bool)) := do
  let coin ← ProbComp.uniform Bool
  return (boolPairToFin4 (coin, state.1), (coin, state.2))

def receive (state : Bool × List Bool) (answer : Bool) : ProbComp (Bool × List Bool) :=
  pure (answer, answer :: state.2)

-- The actual serial commit retains adaptive slots 2 and 3 and both sampled masks.
theorem adaptive_slots_support :
    ((![true, true]), (![(2, true), (3, false)]), (false, [false, true])) ∈
    ((world 2).eval (receiverCommitAdapter choose receive true 2 (false, []))).support := by
  rw [eval_receiverCommitAdapter]
  simp [receiverCommitProgram, receiverCommitWith, choose, receive, ProbComp.eval_bind,
    ot_row, answer_one, table, boolPairToFin4, fin4ToBoolPair, funext_iff,
    Fin.forall_fin_succ]

noncomputable def plan (_ : Fin 2 → Fin 4 × Bool) (state : Bool × List Bool) :
    ProbComp (Bool × (Bool × List Bool)) := do
  let release ← ProbComp.uniform Bool
  return (release, (release, state.2))

noncomputable def finish (_ : Fin 2 → Fin 4 × Bool) (_ : Bool × List Bool)
    (_ : Bool × List Bool) (observed : Phased.Observation) (pairs : Option (Opening 2)) :
    ProbComp (Bool × Phased.Observation × Option (List (Bool × Bool))) := do
  let coin ← ProbComp.uniform Bool
  return (coin, observed, pairs.map fun o => List.ofFn fun i => (o i false, o i true))

-- The exact full bridge retains adaptive private state, randomized release and continuation,
-- and the raw opening correlated with the actual OT answers.
example : (Phased.Observation.receipt, .opened true, (![ (2, true), (3, false)]),
      (false, [false, true]), (true, [false, true]), some (true, [true, true, false, false]),
      (false, Phased.Observation.opened true, some [(true, false), (true, false)])) ∈
    ((world 2).eval (receiverAdapter choose receive true 2 (false, []) plan finish)).support := by
  rw [eval_receiverAdapter]
  simp only [receiverReal, PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff]
  refine ⟨(![true, true], ![(2, true), (3, false)], (false, [false, true])), ?_, ?_⟩
  · rw [← eval_receiverCommitProgram, ← eval_receiverCommitAdapter]
    exact adaptive_slots_support
  · simp [plan, finish, opening, openingWord, List.ofFn_succ]

-- The opened bit is not lost when the opening word is empty; abort exposes no raw payload.
example (release : Bool) : (world 0).eval
    (receiverAdapter choose receive true 0 (false, [])
      (fun _ _ => pure (release, ()))
      (fun _ _ _ observed _ => pure observed)) =
    pure (Phased.Observation.receipt, if release then .opened true else .aborted,
      (Fin.elim0 : Fin 0 → Fin 4 × Bool), (false, []), (),
      if release then some (true, []) else none,
      if release then Phased.Observation.opened true else .aborted) := by
  rw [eval_receiverAdapter]
  cases release <;> simp [receiverReal, receiverCommit_zero, openingWord]

end OTCommitmentSerialTests
