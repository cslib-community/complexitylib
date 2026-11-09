/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (addition to `Cslib/Probability/StatisticalDistance.lean`)

public import Cslib.Probability.StatisticalDistance
public import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.StatisticalDistance

/-!
# Events and relabeling under statistical distance

Statistical distance bounds the change in the probability of every event
(`abs_toOuterMeasure_toReal_sub_le_dist`), in particular the probability that a randomized
distinguisher outputs any given value (`abs_bind_apply_toReal_sub_le_dist`), and relabeling both
distributions by the same injective map preserves it (`dist_map_of_injective`).

## Main results

* `Cslib.Probability.PMF.abs_toOuterMeasure_toReal_sub_le_dist`: event probabilities move by at
  most the statistical distance.
* `Cslib.Probability.PMF.abs_bind_apply_toReal_sub_le_dist`: the advantage of a randomized
  distinguisher is at most the statistical distance.
* `Cslib.Probability.PMF.dist_map_of_injective`: injective relabeling preserves statistical
  distance.
-/

public section

namespace Cslib.Probability.PMF

variable {α β : Type*}

/-- Statistical distance bounds the change in the probability of every event. -/
theorem abs_toOuterMeasure_toReal_sub_le_dist [Fintype α] (p q : PMF α) (event : Set α) :
    |(p.toOuterMeasure event).toReal - (q.toOuterMeasure event).toReal| ≤ dist p q := by
  classical
  let score : α → ℝ := fun a => (if a ∈ event then 1 else 0) - 1 / 2
  have hscore (a : α) : |score a| ≤ 1 / 2 := by
    by_cases ha : a ∈ event <;> norm_num [score, ha]
  have hmean (r : PMF α) :
      ∑ a, (r a).toReal * score a = (r.toOuterMeasure event).toReal - 1 / 2 := by
    simp only [score, mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib,
      ← Finset.sum_mul, sum_toReal, one_mul, toOuterMeasure_apply_toReal]
  have h := abs_sum_mul_sub_le p q score hscore
  rwa [hmean, hmean, sub_sub_sub_cancel_right, show (2 : ℝ) * (1 / 2) = 1 by norm_num,
    one_mul] at h

/-- A randomized distinguisher `T` outputs any given value `b` with probabilities, under `p` and
under `q`, that differ by at most the statistical distance of `p` and `q`. -/
theorem abs_bind_apply_toReal_sub_le_dist [Fintype α] [Finite β] (p q : PMF α) (T : α → PMF β)
    (b : β) : |(p.bind T b).toReal - (q.bind T b).toReal| ≤ dist p q := by
  cases nonempty_fintype β
  have h := abs_toOuterMeasure_toReal_sub_le_dist (p.bind T) (q.bind T) {b}
  rw [PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_apply_singleton] at h
  exact h.trans (dist_bind_le _ _ T)

/-- Relabeling both distributions by the same injective map preserves statistical distance. -/
theorem dist_map_of_injective [Fintype α] [Fintype β] (p q : PMF α) {f : α → β}
    (hf : Function.Injective f) : dist (p.map f) (q.map f) = dist p q := by
  classical
  have hmass (r : PMF α) (a : α) : (r.map f) (f a) = r a := by
    simp only [PMF.map_apply, hf.eq_iff, tsum_ite_eq']
  have hzero (r : PMF α) (b : β) (hb : b ∉ Set.range f) : (r.map f) b = 0 := by
    rw [PMF.apply_eq_zero_iff, PMF.support_map]
    exact fun ⟨a, _, ha⟩ => hb ⟨a, ha⟩
  rw [dist_eq, dist_eq]
  congr 1
  refine (Fintype.sum_of_injective f hf _ _ (fun b hb => ?_) fun a => ?_).symm
  · rw [hzero p b hb, hzero q b hb, sub_self, abs_zero]
  · rw [hmass, hmass]

end Cslib.Probability.PMF
