/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Crypto.Protocols.MPC.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.Fintype.Fin

/-!
# Synchronous All-to-All Broadcast Combinator for Multiparty Protocols

This module defines a synchronous all-to-all broadcast schedule (`broadcastSchedule`) and step
combinator (`broadcastSteps`) over `Complexity.Crypto.Protocols.MPC.Basic`:

* In `broadcastSteps m payload finish`, every sender `s : Fin m` sends `payload s (st s) : Msg`
  to every receiver `r : Fin m` along `broadcastPairs m`.
* Each party `i : Fin m` accumulates the vector `msgs : Fin m → Msg` of broadcast payloads via
  single-slot indicator vectors `Pi.single s (payload s (st s))` (using `[AddCommMonoid Msg]`)
  and computes its continuation output `finish i (st i) msgs`.
* Unlike `GMWCircuit.allToAllStepsWith` in `Complexity.Crypto.Protocols.MPC.CircuitEval` (which
  takes a binary accumulator `Msg → State i → State i` without passing the sender index),
  `broadcastSteps` delivers the sender-indexed vector `Fin m → Msg` to `finish`.

## Main definitions

* `Cslib.Crypto.Protocols.MPC.broadcastPairs`,
  `Cslib.Crypto.Protocols.MPC.broadcastRound`,
  `Cslib.Crypto.Protocols.MPC.broadcastPairsSchedule`,
  `Cslib.Crypto.Protocols.MPC.broadcastSchedule`: canonical ordered pair list and all-to-all
  point-to-point message schedule.
* `Cslib.Crypto.Protocols.MPC.broadcastSteps`,
  `Cslib.Crypto.Protocols.MPC.deliverBroadcast`: synchronous broadcast step combinator and
  received-transcript constructor.

## Main results

* `Cslib.Crypto.Protocols.MPC.evalWith_broadcastSteps`: evaluating `broadcastSteps` in any world
  `W` deterministically yields `PMF.pure (deliverBroadcast (fun s => payload s (st s)))`.
* `Cslib.Crypto.Protocols.MPC.outputAt_broadcastSteps`: extracting party `i`'s output after
  `deliverBroadcast msgs` applies `finish i st_i msgs`.
-/

public section

namespace Cslib.Crypto.Protocols.MPC

/-- Canonical list of all ordered `(sender, receiver)` pairs in `Fin m × Fin m`. -/
@[expose] def broadcastPairs (m : ℕ) : List (Fin m × Fin m) :=
  (List.finRange m).flatMap fun s => (List.finRange m).map fun r => (s, r)

/-- Single point-to-point message round carrying `Msg` from `p.1` to `p.2`. -/
@[expose, reducible] def broadcastRound {m : ℕ} (spec : MultiOracleSpec) (Msg : Type)
    (p : Fin m × Fin m) : Round m spec :=
  .message p.1 p.2 Msg

/-- Schedule of point-to-point message rounds along a list `L` of `(sender, receiver)` pairs. -/
@[expose, reducible] def broadcastPairsSchedule (m : ℕ) (spec : MultiOracleSpec) (Msg : Type)
    (L : List (Fin m × Fin m)) : Schedule m spec :=
  L.map (broadcastRound spec Msg)

/-- Schedule in which every party sends a message of type `Msg` to every party across all pairs. -/
@[expose, reducible] def broadcastSchedule (m : ℕ) (spec : MultiOracleSpec) (Msg : Type) :
    Schedule m spec :=
  broadcastPairsSchedule m spec Msg (broadcastPairs m)

/-- Extract the sender's single-slot vector `Pi.single p.1 msg` at the intended receiver `p.2`
(`0` at all other parties). -/
private def extractBroadcast {m : ℕ} {spec : MultiOracleSpec} {Msg : Type} [Zero Msg]
    (p : Fin m × Fin m) (i : Fin m)
    (recv : (broadcastRound spec Msg p).Received i) : Fin m → Msg :=
  if h : i = p.2 then Pi.single p.1 (recv h) else 0

/-- Auxiliary step-by-step execution accumulating received messages along `L`. -/
private def broadcastStepsAux {m : ℕ} {spec : MultiOracleSpec} {Msg : Type} [AddCommMonoid Msg]
    {State Out : Fin m → Type} (payload : (i : Fin m) → State i → Msg)
    (finish : (i : Fin m) → State i → (Fin m → Msg) → Out i) :
    (L : List (Fin m × Fin m)) →
      Steps (fun i : Fin m => State i × (Fin m → Msg)) Out (broadcastPairsSchedule m spec Msg L)
  | [] => .done fun i st => finish i st.1 st.2
  | p :: L =>
    .message (sender := p.1) (receiver := p.2)
      (fun st => payload p.1 st.1)
      ((broadcastStepsAux payload finish L).mapState fun i ((st_i, acc), recv) =>
        (st_i, acc + extractBroadcast p i recv))

/-- Synchronous broadcast step combinator: each party `s` broadcasts `payload s (st s)` to every
party, and each party `i` computes `finish i (st i) msgs` from the vector `msgs : Fin m → Msg` of
all broadcast values. -/
def broadcastSteps (m : ℕ) {spec : MultiOracleSpec} {Msg : Type} [AddCommMonoid Msg]
    {State Out : Fin m → Type} (payload : (i : Fin m) → State i → Msg)
    (finish : (i : Fin m) → State i → (Fin m → Msg) → Out i) :
    Steps State Out (broadcastSchedule m spec Msg) :=
  (broadcastStepsAux payload finish (broadcastPairs m)).mapState fun _ st => (st, 0)

/-- Auxiliary received-transcript constructor along a pair list `L`. -/
private def deliverBroadcastAux {m : ℕ} {spec : MultiOracleSpec} {Msg : Type}
    (msgs : Fin m → Msg) (i : Fin m) :
    (L : List (Fin m × Fin m)) → (broadcastPairsSchedule m spec Msg L).Received i
  | [] => ()
  | p :: L => (fun _ => msgs p.1, deliverBroadcastAux msgs i L)

/-- Received transcript for party `i` along `broadcastSchedule m spec Msg` when party `s`
broadcasts `msgs s`. -/
def deliverBroadcast {m : ℕ} {spec : MultiOracleSpec} {Msg : Type}
    (msgs : Fin m → Msg) (i : Fin m) :
    (broadcastSchedule m spec Msg).Received i :=
  deliverBroadcastAux (spec := spec) msgs i (broadcastPairs m)

/-- Sum of party `i`'s received single-slot vectors across `L`. -/
private def sumReceivedBroadcast {m : ℕ} {spec : MultiOracleSpec} {Msg : Type}
    [AddCommMonoid Msg] :
    (L : List (Fin m × Fin m)) → (i : Fin m) →
      (broadcastPairsSchedule m spec Msg L).Received i → Fin m → Msg
  | [], _, _ => 0
  | p :: L, i, r => extractBroadcast p i r.1 + sumReceivedBroadcast L i r.2

private theorem outputAt_broadcastStepsAux {m : ℕ} {spec : MultiOracleSpec} {Msg : Type}
    [AddCommMonoid Msg] {State Out : Fin m → Type}
    (payload : (i : Fin m) → State i → Msg)
    (finish : (i : Fin m) → State i → (Fin m → Msg) → Out i)
    (L : List (Fin m × Fin m)) (i : Fin m) (st_i : State i × (Fin m → Msg))
    (recv_i : (broadcastPairsSchedule m spec Msg L).Received i) :
    (broadcastStepsAux payload finish L).outputAt i st_i recv_i =
      finish i st_i.1 (st_i.2 + sumReceivedBroadcast L i recv_i) := by
  induction L generalizing st_i with
  | nil =>
    cases recv_i
    simp [broadcastStepsAux, Steps.outputAt, sumReceivedBroadcast]
  | cons p L ih =>
    rcases recv_i with ⟨r_head, r_tail⟩
    simp [broadcastStepsAux, Steps.outputAt, ih, sumReceivedBroadcast, add_assoc]

private theorem evalWith_broadcastStepsAux {m : ℕ} {spec : MultiOracleSpec} {Msg : Type}
    [AddCommMonoid Msg] {State Out : Fin m → Type}
    (payload : (i : Fin m) → State i → Msg)
    (finish : (i : Fin m) → State i → (Fin m → Msg) → Out i)
    (L : List (Fin m × Fin m)) (W : MultiOracleWorld spec)
    (st : (i : Fin m) → State i × (Fin m → Msg)) :
    (broadcastStepsAux payload finish L).evalWith W st =
      PMF.pure (fun i => deliverBroadcastAux (spec := spec) (fun s => payload s (st s).1) i L) := by
  induction L generalizing st with
  | nil => rfl
  | cons p L ih =>
    simp only [broadcastStepsAux, Steps.evalWith_message, Steps.evalWith_mapState, ih,
      PMF.pure_map]
    rfl

private theorem sumReceivedBroadcast_deliverBroadcast {m : ℕ} {spec : MultiOracleSpec}
    {Msg : Type} [AddCommMonoid Msg] (msgs : Fin m → Msg) (i : Fin m) :
    sumReceivedBroadcast (spec := spec) (broadcastPairs m) i
      (deliverBroadcastAux (spec := spec) msgs i (broadcastPairs m)) = msgs := by
  have hL : ∀ L : List (Fin m × Fin m),
      sumReceivedBroadcast (spec := spec) L i (deliverBroadcastAux (spec := spec) msgs i L) =
        (L.map fun p => extractBroadcast (spec := spec) p i (fun _ => msgs p.1)).sum := by
    intro L
    induction L with
    | nil => rfl
    | cons p L ih => simp [sumReceivedBroadcast, deliverBroadcastAux, ih]
  rw [hL]
  ext s₀
  have hextr : ∀ p : Fin m × Fin m,
      extractBroadcast (spec := spec) p i (fun _ => msgs p.1) =
        if i = p.2 then Pi.single p.1 (msgs p.1) else 0 := by
    intro p
    by_cases h : i = p.2 <;> simp [extractBroadcast, h]
  simp [broadcastPairs, hextr, List.flatMap_def, Function.comp_def, ← Fin.sum_univ_def,
    Finset.sum_apply, Pi.single_apply]

/-- Evaluating `broadcastSteps` in any world `W` deterministically delivers all broadcast values. -/
@[simp] theorem evalWith_broadcastSteps (m : ℕ) {spec : MultiOracleSpec} {Msg : Type}
    [AddCommMonoid Msg] {State Out : Fin m → Type}
    (payload : (i : Fin m) → State i → Msg)
    (finish : (i : Fin m) → State i → (Fin m → Msg) → Out i)
    (W : MultiOracleWorld spec) (st : (i : Fin m) → State i) :
    (broadcastSteps m payload finish).evalWith W st =
      PMF.pure (deliverBroadcast (fun s => payload s (st s))) :=
  (Steps.evalWith_mapState _ _ W st).trans
    (evalWith_broadcastStepsAux payload finish (broadcastPairs m) W (fun i => (st i, 0)))

/-- Extracting party `i`'s output after `deliverBroadcast msgs` applies `finish i st_i msgs`. -/
@[simp] theorem outputAt_broadcastSteps (m : ℕ) {spec : MultiOracleSpec} {Msg : Type}
    [AddCommMonoid Msg] {State Out : Fin m → Type}
    (payload : (i : Fin m) → State i → Msg)
    (finish : (i : Fin m) → State i → (Fin m → Msg) → Out i)
    (i : Fin m) (st_i : State i) (msgs : Fin m → Msg) :
    (broadcastSteps m payload finish).outputAt i st_i
        (deliverBroadcast (spec := spec) msgs i) =
      finish i st_i msgs := by
  simp [broadcastSteps, deliverBroadcast, outputAt_broadcastStepsAux,
    sumReceivedBroadcast_deliverBroadcast]

end Cslib.Crypto.Protocols.MPC
