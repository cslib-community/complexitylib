/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.MPC.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.Fintype.Fin

/-!
# Synchronous All-to-All Pairwise and Broadcast Combinators for Multiparty Protocols

This module defines a synchronous all-to-all schedule (`broadcastSchedule`) and step combinators
for receiver-dependent point-to-point delivery (`pairwiseSteps`) and uniform broadcast
(`broadcastSteps`) over `CslibFrontier.Crypto.Protocols.MPC.Basic`:

* In `pairwiseSteps m send finish`, every sender `s : Fin m` sends `send s (st s) r : Msg`
  to every receiver `r : Fin m` along `broadcastPairs m`.
* In `broadcastSteps m payload finish` (the special case `send s st _ := payload s st`), every
  sender `s : Fin m` sends the same `payload s (st s) : Msg` to every receiver `r : Fin m`.
* Each party `i : Fin m` accumulates its sender-indexed inbox vector `msgs : Fin m → Msg` via
  single-slot indicator vectors `Pi.single s msg` (using `[AddCommMonoid Msg]`) and computes its
  continuation output `finish i (st i) msgs`.
* Unlike `GMWCircuit.allToAllStepsWith` in `CslibFrontier.Crypto.Protocols.MPC.CircuitEval` (which
  takes a binary accumulator `Msg → State i → State i` without passing the sender index),
  `pairwiseSteps` and `broadcastSteps` deliver the sender-indexed vector `Fin m → Msg` to `finish`.

## Main definitions

* `Cslib.Crypto.Protocols.MPC.broadcastPairs`,
  `Cslib.Crypto.Protocols.MPC.broadcastRound`,
  `Cslib.Crypto.Protocols.MPC.broadcastPairsSchedule`,
  `Cslib.Crypto.Protocols.MPC.broadcastSchedule`: canonical ordered pair list and all-to-all
  point-to-point message schedule.
* `Cslib.Crypto.Protocols.MPC.pairwiseSteps`,
  `Cslib.Crypto.Protocols.MPC.broadcastSteps`,
  `Cslib.Crypto.Protocols.MPC.deliverBroadcast`: synchronous point-to-point and broadcast step
  combinators and inbox/received-transcript constructor.

## Main results

* `Cslib.Crypto.Protocols.MPC.evalWith_pairwiseSteps`,
  `Cslib.Crypto.Protocols.MPC.outputAt_pairwiseSteps`: evaluating `pairwiseSteps` in any world `W`
  deterministically delivers each party `i`'s inbox `fun s => send s (st s) i`, and extracting
  party `i`'s output after `deliverBroadcast msgs i` applies `finish i st_i msgs`.
* `Cslib.Crypto.Protocols.MPC.evalWith_broadcastSteps`,
  `Cslib.Crypto.Protocols.MPC.outputAt_broadcastSteps`: specializations of
  `evalWith_pairwiseSteps` and `outputAt_pairwiseSteps` to `broadcastSteps`.
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
private def pairwiseStepsAux {m : ℕ} {spec : MultiOracleSpec} {Msg : Type} [AddCommMonoid Msg]
    {State Out : Fin m → Type} (send : (i : Fin m) → State i → Fin m → Msg)
    (finish : (i : Fin m) → State i → (Fin m → Msg) → Out i) :
    (L : List (Fin m × Fin m)) →
      Steps (fun i : Fin m => State i × (Fin m → Msg)) Out (broadcastPairsSchedule m spec Msg L)
  | [] => .done fun i st => finish i st.1 st.2
  | p :: L =>
    .message (sender := p.1) (receiver := p.2)
      (fun st => send p.1 st.1 p.2)
      ((pairwiseStepsAux send finish L).mapState fun i ((st_i, acc), recv) =>
        (st_i, acc + extractBroadcast p i recv))

/-- Synchronous pairwise point-to-point all-to-all step combinator over `broadcastSchedule`:
every sender `s : Fin m` sends `send s (st s) r` to every receiver `r : Fin m`, and each party `i`
computes `finish i (st i) inbox_i` from the sender-indexed vector `inbox_i : Fin m → Msg` of
messages addressed to `i`. -/
def pairwiseSteps (m : ℕ) {spec : MultiOracleSpec} {Msg : Type} [AddCommMonoid Msg]
    {State Out : Fin m → Type} (send : (i : Fin m) → State i → Fin m → Msg)
    (finish : (i : Fin m) → State i → (Fin m → Msg) → Out i) :
    Steps State Out (broadcastSchedule m spec Msg) :=
  (pairwiseStepsAux send finish (broadcastPairs m)).mapState fun _ st => (st, 0)

/-- Synchronous broadcast step combinator: each party `s` broadcasts `payload s (st s)` to every
party, and each party `i` computes `finish i (st i) msgs` from the vector `msgs : Fin m → Msg` of
all broadcast values. -/
def broadcastSteps (m : ℕ) {spec : MultiOracleSpec} {Msg : Type} [AddCommMonoid Msg]
    {State Out : Fin m → Type} (payload : (i : Fin m) → State i → Msg)
    (finish : (i : Fin m) → State i → (Fin m → Msg) → Out i) :
    Steps State Out (broadcastSchedule m spec Msg) :=
  pairwiseSteps m (fun s st _ => payload s st) finish

/-- Auxiliary received-transcript constructor along a pair list `L`. -/
private def deliverBroadcastAux {m : ℕ} {spec : MultiOracleSpec} {Msg : Type}
    (msgs : Fin m → Msg) (i : Fin m) :
    (L : List (Fin m × Fin m)) → (broadcastPairsSchedule m spec Msg L).Received i
  | [] => ()
  | p :: L => (fun _ => msgs p.1, deliverBroadcastAux msgs i L)

/-- Received transcript for party `i` along `broadcastSchedule m spec Msg` when party `i` receives
`msgs s` from each sender `s : Fin m`.

This serves both as the received transcript of `broadcastSteps` (when `msgs s` is the value
broadcast by sender `s`) and as the inbox transcript of `pairwiseSteps` (when `msgs s` is the
point-to-point message sent by `s` to `i`): because `Round.Received (.message s r Msg) i` has
proof domain `i = r`, rounds with `i ≠ r` carry an empty function domain and do not depend on
messages sent to other receivers `r ≠ i`. -/
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

private theorem outputAt_pairwiseStepsAux {m : ℕ} {spec : MultiOracleSpec} {Msg : Type}
    [AddCommMonoid Msg] {State Out : Fin m → Type}
    (send : (i : Fin m) → State i → Fin m → Msg)
    (finish : (i : Fin m) → State i → (Fin m → Msg) → Out i)
    (L : List (Fin m × Fin m)) (i : Fin m) (st_i : State i × (Fin m → Msg))
    (recv_i : (broadcastPairsSchedule m spec Msg L).Received i) :
    (pairwiseStepsAux send finish L).outputAt i st_i recv_i =
      finish i st_i.1 (st_i.2 + sumReceivedBroadcast L i recv_i) := by
  induction L generalizing st_i with
  | nil =>
    cases recv_i
    simp [pairwiseStepsAux, Steps.outputAt, sumReceivedBroadcast]
  | cons p L ih =>
    rcases recv_i with ⟨r_head, r_tail⟩
    simp [pairwiseStepsAux, Steps.outputAt, ih, sumReceivedBroadcast, add_assoc]

private theorem evalWith_pairwiseStepsAux {m : ℕ} {spec : MultiOracleSpec} {Msg : Type}
    [AddCommMonoid Msg] {State Out : Fin m → Type}
    (send : (i : Fin m) → State i → Fin m → Msg)
    (finish : (i : Fin m) → State i → (Fin m → Msg) → Out i)
    (L : List (Fin m × Fin m)) (W : MultiOracleWorld spec)
    (st : (i : Fin m) → State i × (Fin m → Msg)) :
    (pairwiseStepsAux send finish L).evalWith W st =
      PMF.pure (fun i => deliverBroadcastAux (spec := spec) (fun s => send s (st s).1 i) i L) := by
  induction L generalizing st with
  | nil => rfl
  | cons p L ih =>
    simp only [pairwiseStepsAux, Steps.evalWith_message, Steps.evalWith_mapState, ih,
      PMF.pure_map]
    refine congrArg PMF.pure (funext fun i => Prod.ext ?_ rfl)
    funext h
    subst h
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

/-- Evaluating `pairwiseSteps` in any world `W` deterministically delivers each party `i`'s inbox
`fun s => send s (st s) i`. -/
@[simp] theorem evalWith_pairwiseSteps (m : ℕ) {spec : MultiOracleSpec} {Msg : Type}
    [AddCommMonoid Msg] {State Out : Fin m → Type}
    (send : (i : Fin m) → State i → Fin m → Msg)
    (finish : (i : Fin m) → State i → (Fin m → Msg) → Out i)
    (W : MultiOracleWorld spec) (st : (i : Fin m) → State i) :
    (pairwiseSteps m send finish).evalWith W st =
      PMF.pure (fun i => deliverBroadcast (fun s => send s (st s) i) i) :=
  (Steps.evalWith_mapState _ _ W st).trans
    (evalWith_pairwiseStepsAux send finish (broadcastPairs m) W (fun i => (st i, 0)))

/-- Extracting party `i`'s output after `deliverBroadcast inbox i` applies `finish i st_i inbox`. -/
@[simp] theorem outputAt_pairwiseSteps (m : ℕ) {spec : MultiOracleSpec} {Msg : Type}
    [AddCommMonoid Msg] {State Out : Fin m → Type}
    (send : (i : Fin m) → State i → Fin m → Msg)
    (finish : (i : Fin m) → State i → (Fin m → Msg) → Out i)
    (i : Fin m) (st_i : State i) (inbox : Fin m → Msg) :
    (pairwiseSteps m send finish).outputAt i st_i
        (deliverBroadcast (spec := spec) inbox i) =
      finish i st_i inbox := by
  simp [pairwiseSteps, deliverBroadcast, outputAt_pairwiseStepsAux,
    sumReceivedBroadcast_deliverBroadcast]

/-- Evaluating `broadcastSteps` in any world `W` deterministically delivers all broadcast values. -/
@[simp] theorem evalWith_broadcastSteps (m : ℕ) {spec : MultiOracleSpec} {Msg : Type}
    [AddCommMonoid Msg] {State Out : Fin m → Type}
    (payload : (i : Fin m) → State i → Msg)
    (finish : (i : Fin m) → State i → (Fin m → Msg) → Out i)
    (W : MultiOracleWorld spec) (st : (i : Fin m) → State i) :
    (broadcastSteps m payload finish).evalWith W st =
      PMF.pure (deliverBroadcast (fun s => payload s (st s))) :=
  evalWith_pairwiseSteps m (fun s st _ => payload s st) finish W st

/-- Extracting party `i`'s output after `deliverBroadcast msgs` applies `finish i st_i msgs`. -/
@[simp] theorem outputAt_broadcastSteps (m : ℕ) {spec : MultiOracleSpec} {Msg : Type}
    [AddCommMonoid Msg] {State Out : Fin m → Type}
    (payload : (i : Fin m) → State i → Msg)
    (finish : (i : Fin m) → State i → (Fin m → Msg) → Out i)
    (i : Fin m) (st_i : State i) (msgs : Fin m → Msg) :
    (broadcastSteps m payload finish).outputAt i st_i
        (deliverBroadcast (spec := spec) msgs i) =
      finish i st_i msgs :=
  outputAt_pairwiseSteps m (fun s st _ => payload s st) finish i st_i msgs

end Cslib.Crypto.Protocols.MPC
