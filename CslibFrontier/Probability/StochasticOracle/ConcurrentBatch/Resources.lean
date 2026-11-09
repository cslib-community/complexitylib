/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.ConcurrentBatch.Codec
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic

/-!
# Concurrent call trajectories, cutoffs and accrued cancellation bills

[Wang2027], model PDF pp. 4--6. All calls start at the same batch issuance time.
Each call stops at its return, prescribed cutoff or remaining absolute deadline.
Cancellation retains accrued tokens and has no completed visible response. The
batch bill is the sum and physical duration is the maximum of these actual stop
times; an earlier acceptable response does not stop the other calls.

The joint trajectory law is supplied by the oracle later, without component
independence. Cumulative natural token counts are explicitly monotone. No
bounded-total-cost or integrability premise is used.

## Main results

* `CallTrace.canceled_stop`: canceled calls run through their actual allotment.
* `observe_tokens`: the batch bill sums charges accrued through each actual stopping time.
* `observe_duration_le`: every concurrent batch finishes within the remaining deadline.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle.ConcurrentBatch
open scoped NNReal

/-- A potential relative-time call trajectory, including billed hidden tokens. -/
structure CallTrace where
  /-- Return time and full visible response, or a call which never returns. -/
  returned : Option (ℝ≥0 × Word)
  /-- Tokens charged up to each relative elapsed time, including query tokens. -/
  accrued : ℝ≥0 → ℕ
  /-- Cancellation cannot erase already charged tokens. -/
  monotone : Monotone accrued

namespace CallTrace
/-- The call runs until its response or its own fixed allotment. -/
@[expose] def stop (t : CallTrace) (allot : ℝ≥0) : ℝ≥0 :=
  match t.returned with | none => allot | some (time, _) => min allot time

/-- The visible response is unavailable when cutoff/deadline cancels first. -/
@[expose] def response (t : CallTrace) (allot : ℝ≥0) : Option Word :=
  match t.returned with
  | none => none
  | some (time, word) => if time ≤ allot then some word else none

/-- The same trajectory supplies both the visible result and the actual invoice. -/
@[expose] def report (t : CallTrace) (allot : ℝ≥0) : CallReport :=
  (t.response allot, t.accrued (t.stop allot))

/-- Actual return/cancellation never exceeds its allotment. -/
theorem stop_le (t : CallTrace) (allot : ℝ≥0) : t.stop allot ≤ allot := by
  cases hr : t.returned <;> simp [stop, hr]

/-- A canceled call runs through the allotment and is billed through cancellation. -/
theorem canceled_stop (t : CallTrace) (allot : ℝ≥0) (h : t.response allot = none) :
    t.stop allot = allot ∧ (t.report allot).2 = t.accrued allot := by
  cases hr : t.returned with
  | none => simp [stop, report, hr]
  | some result =>
    rcases result with ⟨time, word⟩
    have hn : ¬time ≤ allot := by simpa [response, hr] using h
    simp [stop, report, hr, min_eq_left (le_of_not_ge hn)]

/-- Already accrued tokens are not free on cancellation. -/
theorem bill_le_allot (t : CallTrace) (allot : ℝ≥0) :
    (t.report allot).2 ≤ t.accrued allot := t.monotone (t.stop_le allot)
end CallTrace

/-- Fixed oracle/cutoff configurations and the global resource budgets. -/
structure Limits (n : ℕ) where
  /-- Each labeled opportunity fixes its cutoff before any response. -/
  cutoff : Fin n → ℝ≥0
  /-- Source cutoffs are strictly positive. -/
  cutoff_pos : ∀ i, 0 < cutoff i
  /-- Absolute oracle response deadline; local native computation is excluded. -/
  deadline : ℝ≥0
  /-- Maximum number of issued batches, including unsuccessful batches. -/
  turns : ℕ

/-- A full completed/canceled batch receipt, with no unused-call observations. -/
structure Exchange (n : ℕ) where
  /-- All query words were fixed before the joint trajectory sample. -/
  batch : Batch n
  /-- Active-call words/cancellations and accrued invoices. -/
  report : Report n
  /-- Actual active-call stop times; unused entries are zero. -/
  time : Fin n → ℝ≥0

namespace Exchange
/-- Batch token costs add, even when calls are canceled or another call succeeds. -/
@[expose] def tokens {n : ℕ} (x : Exchange n) : ℕ :=
  ∑ i ∈ active x.batch.slots, ((x.report i).getD (none, 0)).2

/-- Concurrent physical batch latency is the maximum active call latency. -/
@[expose] def duration {n : ℕ} (x : Exchange n) : ℝ≥0 :=
  (active x.batch.slots).sup x.time
end Exchange

/-- Observe one jointly sampled vector of call trajectories at the actual
per-call cutoff/deadline. No other call's response controls this stopping time. -/
@[expose] def observe {n : ℕ} (limits : Limits n) (remaining : ℝ≥0) (b : Batch n)
    (paths : Fin n → CallTrace) : Exchange n :=
  ⟨b, fun i => (b.slots i).map fun _ => (paths i).report (min (limits.cutoff i) remaining),
    fun i => if (b.slots i).isSome then (paths i).stop (min (limits.cutoff i) remaining) else 0⟩

/-- Only actually selected opportunities have reports. -/
theorem observe_active {n : ℕ} (limits : Limits n) (remaining : ℝ≥0) (b : Batch n)
    (paths : Fin n → CallTrace) (i : Fin n) :
    ((observe limits remaining b paths).report i).isSome = (b.slots i).isSome := by
  cases hs : b.slots i <;> simp [observe, hs]

/-- The actual invoice is derived by summing the actual accrued per-call charges. -/
theorem observe_tokens {n : ℕ} (limits : Limits n) (remaining : ℝ≥0) (b : Batch n)
    (paths : Fin n → CallTrace) :
    (observe limits remaining b paths).tokens =
      ∑ i ∈ active b.slots,
        (paths i).accrued ((paths i).stop (min (limits.cutoff i) remaining)) := by
  simp only [Exchange.tokens, observe]
  apply Finset.sum_congr rfl
  intro i hi
  cases hs : b.slots i with
  | none => simp [active, hs] at hi
  | some word => simp [CallTrace.report]

/-- Every selected or unused call's recorded duration is within the remaining deadline. -/
theorem observe_time_le {n : ℕ} (limits : Limits n) (remaining : ℝ≥0) (b : Batch n)
    (paths : Fin n → CallTrace) (i : Fin n) :
    (observe limits remaining b paths).time i ≤ remaining := by
  change (if (b.slots i).isSome then (paths i).stop (min (limits.cutoff i) remaining) else 0) ≤ _
  by_cases hi : (b.slots i).isSome
  · rw [ite_eq_left hi]
    exact ((paths i).stop_le _).trans (min_le_right _ _)
  · simp [hi]

/-- Maximum concurrent latency, rather than summed call latency, fits the deadline. -/
theorem observe_duration_le {n : ℕ} (limits : Limits n) (remaining : ℝ≥0) (b : Batch n)
    (paths : Fin n → CallTrace) : (observe limits remaining b paths).duration ≤ remaining := by
  exact Finset.sup_le fun i _ => observe_time_le limits remaining b paths i

/-- Actual cutoff/deadline cancellation preserves every accrued token. -/
theorem observe_canceled {n : ℕ} (limits : Limits n) (remaining : ℝ≥0) (b : Batch n)
    (paths : Fin n → CallTrace) (i : Fin n) (hi : i ∈ active b.slots)
    (hc : (paths i).response (min (limits.cutoff i) remaining) = none) :
    (observe limits remaining b paths).report i =
      some (none, (paths i).accrued (min (limits.cutoff i) remaining)) := by
  cases hs : b.slots i with
  | none => simp [active, hs] at hi
  | some word =>
    simp [observe, hs, CallTrace.report, hc, ((paths i).canceled_stop _ hc).1]

end Cslib.Probability.StochasticOracle.ConcurrentBatch
