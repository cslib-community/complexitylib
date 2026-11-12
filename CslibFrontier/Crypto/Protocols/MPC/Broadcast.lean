/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.MPC.AllToAll

/-!
# Synchronous Broadcast Combinator for Multiparty Protocols

This module defines broadcast as the special case of the all-to-all message layer
(`CslibFrontier.Crypto.Protocols.MPC.AllToAll`) in which the message does not depend on the
receiver. In `broadcastSteps m payload finish`, every sender `s : Fin m` sends the same
`payload s (st s) : Msg` to every receiver over `allToAllSchedule m Msg`, and each party `i`
outputs `finish i (st i) msgs` from the vector `msgs : Fin m → Msg` of all broadcast values.

## Main definitions

* `Cslib.Crypto.Protocols.MPC.broadcastSteps`: synchronous broadcast step combinator.

## Main results

* `Cslib.Crypto.Protocols.MPC.evalWith_broadcastSteps`,
  `Cslib.Crypto.Protocols.MPC.outputAt_broadcastSteps`: specializations of
  `evalWith_allToAllStepsWith` and `outputAt_allToAllStepsWith` to `broadcastSteps`.
-/

public section

namespace Cslib.Crypto.Protocols.MPC

/-- Synchronous broadcast step combinator: each party `s` broadcasts `payload s (st s)` to every
party, and each party `i` computes `finish i (st i) msgs` from the vector `msgs : Fin m → Msg` of
all broadcast values. -/
def broadcastSteps (m : ℕ) {spec : MultiOracleSpec} {Msg : Type} [AddCommMonoid Msg]
    {State Out : Fin m → Type} (payload : (i : Fin m) → State i → Msg)
    (finish : (i : Fin m) → State i → (Fin m → Msg) → Out i) :
    Steps State Out (allToAllSchedule m (spec := spec) Msg) :=
  allToAllStepsWith m (fun s st _ => payload s st) finish

/-- Evaluating `broadcastSteps` in any world `W` deterministically delivers all broadcast values. -/
@[simp] theorem evalWith_broadcastSteps (m : ℕ) {spec : MultiOracleSpec} {Msg : Type}
    [AddCommMonoid Msg] {State Out : Fin m → Type}
    (payload : (i : Fin m) → State i → Msg)
    (finish : (i : Fin m) → State i → (Fin m → Msg) → Out i)
    (W : MultiOracleWorld spec) (st : (i : Fin m) → State i) :
    (broadcastSteps m payload finish).evalWith W st =
      PMF.pure (fun i => receivedScheduleOfInbox i (fun s => payload s (st s)) (allPairs m)) :=
  evalWith_allToAllStepsWith m (fun s st _ => payload s st) finish W st

/-- On the transcript of the broadcast values `msgs`, party `i` outputs `finish i st_i msgs`. -/
@[simp] theorem outputAt_broadcastSteps (m : ℕ) {spec : MultiOracleSpec} {Msg : Type}
    [AddCommMonoid Msg] {State Out : Fin m → Type}
    (payload : (i : Fin m) → State i → Msg)
    (finish : (i : Fin m) → State i → (Fin m → Msg) → Out i)
    (i : Fin m) (st_i : State i) (msgs : Fin m → Msg) :
    (broadcastSteps m payload finish).outputAt i st_i
        (receivedScheduleOfInbox (spec := spec) i msgs (allPairs m)) =
      finish i st_i msgs :=
  outputAt_allToAllStepsWith m (fun s st _ => payload s st) finish i st_i msgs

end Cslib.Crypto.Protocols.MPC
