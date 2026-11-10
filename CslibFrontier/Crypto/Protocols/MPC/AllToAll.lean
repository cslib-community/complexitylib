/-
Copyright (c) 2026 Samuel Schlesinger, Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.MPC.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.Fintype.Fin

/-!
# Synchronous All-to-All Point-to-Point Messages

This module defines the all-to-all message layer of `CslibFrontier.Crypto.Protocols.MPC.Basic`:
every party `s : Fin m` sends one message of type `Msg` to every party `r : Fin m` (including
itself), one `.message s r Msg` round per ordered pair in `allPairs m`.

* In `allToAllStepsWith m send finish`, sender `s` sends `send s (st s) r` to receiver `r`, and
  party `i` outputs `finish i (st i) inbox_i`, where `inbox_i : Fin m → Msg` is the
  sender-indexed vector of the messages addressed to `i`. Each party builds its inbox by adding
  the single-slot vectors `Pi.single s msg` (using `[AddCommMonoid Msg]`).
* `receivedScheduleOfInbox i inbox_i (allPairs m)` is party `i`'s received transcript when it
  receives `inbox_i s` from each sender `s`. Since `Round.Received (.message s r Msg) i` has the
  proof domain `i = r`, the transcript does not depend on messages addressed to other parties.

Broadcast (`CslibFrontier.Crypto.Protocols.MPC.Broadcast`) is the special case of a message that
does not depend on the receiver. The input-sharing step of
`CslibFrontier.Crypto.Protocols.MPC.CircuitEval` is another instance.

## Main definitions

* `Cslib.Crypto.Protocols.MPC.allPairs`, `Cslib.Crypto.Protocols.MPC.msgRound`,
  `Cslib.Crypto.Protocols.MPC.msgSchedule`, `Cslib.Crypto.Protocols.MPC.allToAllSchedule`: the
  ordered pair list and the point-to-point message schedules along a pair list and along all
  pairs.
* `Cslib.Crypto.Protocols.MPC.msgStepsWith`, `Cslib.Crypto.Protocols.MPC.allToAllStepsWith`:
  step combinators along a pair list and along all pairs.
* `Cslib.Crypto.Protocols.MPC.receivedMsgOfInbox`,
  `Cslib.Crypto.Protocols.MPC.receivedScheduleOfInbox`: received records and transcripts built
  from an inbox.

## Main results

* `Cslib.Crypto.Protocols.MPC.evalWith_allToAllStepsWith`: in any world `W`, evaluating
  `allToAllStepsWith` deterministically delivers to each party `i` its inbox
  `fun s => send s (st s) i`.
* `Cslib.Crypto.Protocols.MPC.outputAt_allToAllStepsWith`: on the transcript of inbox `inbox`,
  party `i` outputs `finish i st_i inbox`.
-/

public section

namespace Cslib.Crypto.Protocols.MPC

/-- All ordered sender-receiver pairs `(s, r) : Fin m × Fin m` (including `(s, s)` self-pairs). -/
@[expose] def allPairs (m : ℕ) : List (Fin m × Fin m) :=
  (List.finRange m).flatMap fun s => (List.finRange m).map fun r => (s, r)

/-- Point-to-point message round from `p.1` to `p.2` carrying `Msg`. -/
@[expose, reducible] def msgRound {m : ℕ} {spec : MultiOracleSpec} (Msg : Type)
    (p : Fin m × Fin m) : Round m spec :=
  .message p.1 p.2 Msg

/-- Schedule of point-to-point message rounds along `L : List (Fin m × Fin m)`. -/
@[expose, reducible] def msgSchedule {m : ℕ} {spec : MultiOracleSpec} (Msg : Type)
    (L : List (Fin m × Fin m)) : Schedule m spec :=
  L.map (msgRound Msg)

/-- Schedule of all-to-all point-to-point messages of type `Msg`. -/
@[expose, reducible] def allToAllSchedule (m : ℕ) {spec : MultiOracleSpec} (Msg : Type) :
    Schedule m spec :=
  msgSchedule Msg (allPairs m)

/-- Extract party `i`'s inbox update from message round `p = (s, r)`: the single-slot vector
`Pi.single s msg` at the receiver `r`, and `0` at every other party. -/
def extractMsg {m : ℕ} {spec : MultiOracleSpec} {Msg : Type} [Zero Msg]
    (p : Fin m × Fin m) (i : Fin m)
    (recv : (msgRound (spec := spec) Msg p).Received i) : Fin m → Msg :=
  if h : i = p.2 then Pi.single p.1 (recv h) else 0

/-- Execute point-to-point message rounds along `L`: in round `(s, r)` party `s` sends
`send s st_s r`. Each party accumulates its received messages into the second component of its
state and applies `finish` at `.done`. -/
@[expose] def msgStepsWith {m : ℕ} {spec : MultiOracleSpec} {Msg : Type} [AddCommMonoid Msg]
    {State Out : Fin m → Type} (send : (i : Fin m) → State i → Fin m → Msg)
    (finish : (i : Fin m) → State i → (Fin m → Msg) → Out i) :
    (L : List (Fin m × Fin m)) →
      Steps (fun i : Fin m => State i × (Fin m → Msg)) Out (msgSchedule (spec := spec) Msg L)
  | [] => .done fun i st => finish i st.1 st.2
  | p :: L =>
    .message (sender := p.1) (receiver := p.2)
      (fun st => send p.1 st.1 p.2)
      ((msgStepsWith send finish L).mapState fun i ((st_i, acc), recv) =>
        (st_i, acc + extractMsg p i recv))

/-- All-to-all message exchange: party `s` sends `send s (st s) r` to party `r`, and party `i`
outputs `finish i (st i) inbox_i` from the vector `inbox_i : Fin m → Msg` of the messages
addressed to it. -/
@[expose] def allToAllStepsWith (m : ℕ) {spec : MultiOracleSpec} {Msg : Type}
    [AddCommMonoid Msg] {State Out : Fin m → Type}
    (send : (i : Fin m) → State i → Fin m → Msg)
    (finish : (i : Fin m) → State i → (Fin m → Msg) → Out i) :
    Steps State Out (allToAllSchedule m (spec := spec) Msg) :=
  (msgStepsWith send finish (allPairs m)).mapState fun _ st => (st, 0)

/-- Received record for party `i` in round `p = (s, r)` constructed from party `i`'s inbox
`inbox_i : Fin m → Msg`. -/
@[expose] def receivedMsgOfInbox {m : ℕ} {spec : MultiOracleSpec} {Msg : Type}
    (p : Fin m × Fin m) (i : Fin m) (inbox_i : Fin m → Msg) :
    (msgRound (spec := spec) Msg p).Received i :=
  fun _ => inbox_i p.1

/-- Received transcript for party `i` along `msgSchedule Msg L` constructed from `inbox_i`. -/
@[expose] def receivedScheduleOfInbox {m : ℕ} {spec : MultiOracleSpec} {Msg : Type}
    (i : Fin m) (inbox_i : Fin m → Msg) :
    (L : List (Fin m × Fin m)) → (msgSchedule (spec := spec) Msg L).Received i
  | [] => ()
  | p :: L => (receivedMsgOfInbox p i inbox_i, receivedScheduleOfInbox i inbox_i L)

theorem deliverMessage_eq_receivedMsgOfInbox {m : ℕ} {spec : MultiOracleSpec} {Msg : Type}
    (toSend : (s : Fin m) → Fin m → Msg) (p : Fin m × Fin m) (i : Fin m) :
    Round.deliverMessage (spec := spec) (sender := p.1) (receiver := p.2) (toSend p.1 p.2) i =
      receivedMsgOfInbox p i (fun s => toSend s i) := by
  funext h
  subst h
  rfl

/-- Sum of party `i`'s received message updates along `L`. -/
private def sumReceivedMsgs {m : ℕ} {spec : MultiOracleSpec} {Msg : Type} [AddCommMonoid Msg] :
    (L : List (Fin m × Fin m)) → (i : Fin m) →
      (msgSchedule (spec := spec) Msg L).Received i → Fin m → Msg
  | [], _, _ => 0
  | p :: L, i, r => extractMsg p i r.1 + sumReceivedMsgs L i r.2

private theorem outputAt_msgStepsWith {m : ℕ} {spec : MultiOracleSpec} {Msg : Type}
    [AddCommMonoid Msg] {State Out : Fin m → Type}
    (send : (i : Fin m) → State i → Fin m → Msg)
    (finish : (i : Fin m) → State i → (Fin m → Msg) → Out i)
    (L : List (Fin m × Fin m)) (i : Fin m) (st_i : State i × (Fin m → Msg))
    (recv_i : (msgSchedule (spec := spec) Msg L).Received i) :
    (msgStepsWith send finish L).outputAt i st_i recv_i =
      finish i st_i.1 (st_i.2 + sumReceivedMsgs L i recv_i) := by
  induction L generalizing st_i with
  | nil =>
    cases recv_i
    simp [msgStepsWith, Steps.outputAt, sumReceivedMsgs]
  | cons p L ih =>
    rcases recv_i with ⟨r_head, r_tail⟩
    simp [msgStepsWith, Steps.outputAt, ih, sumReceivedMsgs, add_assoc]

private theorem evalWith_msgStepsWith {m : ℕ} {spec : MultiOracleSpec} {Msg : Type}
    [AddCommMonoid Msg] {State Out : Fin m → Type}
    (send : (i : Fin m) → State i → Fin m → Msg)
    (finish : (i : Fin m) → State i → (Fin m → Msg) → Out i)
    (L : List (Fin m × Fin m)) (W : MultiOracleWorld spec)
    (st : (i : Fin m) → State i × (Fin m → Msg)) :
    (msgStepsWith send finish L).evalWith W st =
      PMF.pure (fun i => receivedScheduleOfInbox i (fun s => send s (st s).1 i) L) := by
  induction L generalizing st with
  | nil => rfl
  | cons p L ih =>
    simp [msgStepsWith, ih,
      deliverMessage_eq_receivedMsgOfInbox (fun s => send s (st s).1) p, receivedScheduleOfInbox]

private theorem sumReceivedMsgs_receivedScheduleOfInbox {m : ℕ} {spec : MultiOracleSpec}
    {Msg : Type} [AddCommMonoid Msg] (i : Fin m) (inbox_i : Fin m → Msg) :
    sumReceivedMsgs (spec := spec) (allPairs m) i
      (receivedScheduleOfInbox i inbox_i (allPairs m)) = inbox_i := by
  have hL : ∀ L : List (Fin m × Fin m),
      sumReceivedMsgs (spec := spec) L i (receivedScheduleOfInbox i inbox_i L) =
        (L.map fun p => extractMsg (spec := spec) p i (receivedMsgOfInbox p i inbox_i)).sum := by
    intro L
    induction L with
    | nil => rfl
    | cons p L ih => simp [sumReceivedMsgs, receivedScheduleOfInbox, ih]
  have hextr : ∀ p : Fin m × Fin m,
      extractMsg (spec := spec) p i (receivedMsgOfInbox p i inbox_i) =
        if i = p.2 then Pi.single p.1 (inbox_i p.1) else 0 := by
    intro p
    by_cases h : i = p.2 <;> simp [extractMsg, receivedMsgOfInbox, h]
  rw [hL]
  ext s₀
  simp [allPairs, hextr, List.flatMap_def, Function.comp_def, ← Fin.sum_univ_def,
    Finset.sum_apply, Pi.single_apply]

/-- Evaluating `allToAllStepsWith` in any world `W` deterministically delivers to each party `i`
its inbox `fun s => send s (st s) i`. -/
@[simp] theorem evalWith_allToAllStepsWith (m : ℕ) {spec : MultiOracleSpec} {Msg : Type}
    [AddCommMonoid Msg] {State Out : Fin m → Type}
    (send : (i : Fin m) → State i → Fin m → Msg)
    (finish : (i : Fin m) → State i → (Fin m → Msg) → Out i)
    (W : MultiOracleWorld spec) (st : (i : Fin m) → State i) :
    (allToAllStepsWith m send finish).evalWith W st =
      PMF.pure (fun i => receivedScheduleOfInbox i (fun s => send s (st s) i) (allPairs m)) :=
  (Steps.evalWith_mapState _ _ W st).trans
    (evalWith_msgStepsWith send finish (allPairs m) W (fun i => (st i, 0)))

/-- On the transcript of inbox `inbox`, party `i` outputs `finish i st_i inbox`. -/
@[simp] theorem outputAt_allToAllStepsWith (m : ℕ) {spec : MultiOracleSpec} {Msg : Type}
    [AddCommMonoid Msg] {State Out : Fin m → Type}
    (send : (i : Fin m) → State i → Fin m → Msg)
    (finish : (i : Fin m) → State i → (Fin m → Msg) → Out i)
    (i : Fin m) (st_i : State i) (inbox : Fin m → Msg) :
    (allToAllStepsWith m send finish).outputAt i st_i
        (receivedScheduleOfInbox (spec := spec) i inbox (allPairs m)) =
      finish i st_i inbox := by
  simp [allToAllStepsWith, outputAt_msgStepsWith, sumReceivedMsgs_receivedScheduleOfInbox]

end Cslib.Crypto.Protocols.MPC
