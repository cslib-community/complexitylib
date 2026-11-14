/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.ConcurrentBatch.Protocol
import Mathlib.Tactic

/-!
# Actual source batch duration bounds

Theorem 5 of [Wang2027] (PDF p. 12, Appendix A.5 p. 16) bounds the actual
concurrent batch latency. A configured cutoff can be longer than that bound
when the source returns sooner. `HasDurationBound` is a uniform supported-draw
envelope over source states and batches, sufficient for the source's along-execution
bound. It makes no policy termination, success or total-cost assumption.

## Main definitions

* `HasDurationBound`: actual observed batch duration is bounded on source support.

## Main results

* `hasDurationBound_of_cutoff`: bounded cutoffs are a sufficient special case.
* `hasDurationBound_of_returned`: bounded actual returns allow larger cutoffs.
* `HasDurationBound.reply`: guarded actual source replies respect the bound.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle.ConcurrentBatch
open NativeOpenExecution
open scoped NNReal
variable {n : ℕ} {Private : Type}

/-- Every supported source draw has concurrent return/cancellation duration at
most `ell`, at the actual remaining deadline. The bound concerns only one selected
batch, not policy stopping, completion or its accumulated duration. -/
@[expose] def HasDurationBound (limits : Limits n) (sample : Sampler n Private)
    (ell : ℝ≥0) : Prop :=
  ∀ state batch draw, draw ∈ (sample state batch).support →
    (observe limits (limits.deadline - state.elapsed) batch draw.1).duration ≤ ell

/-- Configured cutoff bounds imply the actual duration envelope, independently
of the source's correlations, private state and return-time distributions. -/
theorem hasDurationBound_of_cutoff (limits : Limits n) (sample : Sampler n Private)
    (ell : ℝ≥0) (hcut : ∀ i, limits.cutoff i ≤ ell) :
    HasDurationBound limits sample ell := by
  intro state batch draw _
  apply Finset.sup_le
  intro i _
  change (if (batch.slots i).isSome then
    (draw.1 i).stop (min (limits.cutoff i) (limits.deadline - state.elapsed)) else 0) ≤ ell
  split_ifs
  · exact ((draw.1 i).stop_le _).trans ((min_le_left _ _).trans (hcut i))
  · exact zero_le

/-- Bounded actual return times imply the duration envelope even when the
configured cutoffs are larger. Only active calls need the return guarantee. -/
theorem hasDurationBound_of_returned (limits : Limits n) (sample : Sampler n Private)
    (ell : ℝ≥0)
    (H : ∀ state batch draw, draw ∈ (sample state batch).support →
      ∀ i ∈ active batch.slots, ∃ time word,
        (draw.1 i).returned = some (time, word) ∧ time ≤ ell) :
    HasDurationBound limits sample ell := by
  intro state batch draw hd
  apply Finset.sup_le
  intro i _
  change (if (batch.slots i).isSome then
    (draw.1 i).stop (min (limits.cutoff i) (limits.deadline - state.elapsed)) else 0) ≤ ell
  split_ifs with hi
  · obtain ⟨time, word, hr, ht⟩ := H state batch draw hd i (by simp [active, hi])
    simp only [CallTrace.stop, hr]
    exact (min_le_right _ _).trans ht
  · exact zero_le

/-- Guarded admission preserves the primitive actual-duration envelope; rejected
requests have zero duration and sample no source trajectory. -/
theorem HasDurationBound.reply {limits : Limits n} {sample : Sampler n Private}
    {ell : ℝ≥0} (h : HasDurationBound limits sample ell) (q : Unit × Word)
    (memory : Memory Unit (ServerState n Private)) (reply : Reply) (next : ServerState n Private)
    (hr : (reply, next) ∈ (environment limits sample q memory).support) :
    reply.duration ≤ ell := by
  change (reply, next) ∈ (serve limits sample q.2 memory.privateState).support at hr
  cases ha : admit limits memory.privateState q.2 with
  | none =>
    rw [serve_rejected _ _ _ _ ha, PMF.mem_support_pure_iff] at hr
    cases hr
    exact zero_le
  | some batch =>
    rw [serve_accepted _ _ _ _ _ ha, PMF.mem_support_map_iff] at hr
    obtain ⟨draw, hd, he⟩ := hr
    cases he
    exact h _ _ _ hd

end Cslib.Probability.StochasticOracle.ConcurrentBatch
