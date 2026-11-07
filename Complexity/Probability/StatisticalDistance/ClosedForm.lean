/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (addition to `Cslib/Probability/StatisticalDistance.lean`)

public import Cslib.Probability.StatisticalDistance
public import Complexity.Probability.PMF

/-!
# Closed forms for statistical distance

Two closed forms for cslib's statistical distance `dist` on finite PMFs. The distance from a point
mass `PMF.pure a` is the mass the other distribution places off `a` (`dist_pure_left`). On `Bool`,
the distance is the difference of the probabilities of `true` (`dist_bool`).

## Main results

* `Cslib.Probability.PMF.dist_pure_left`: distance from a point mass.
* `Cslib.Probability.PMF.dist_bool`: distance on `Bool`.
-/

public section

open scoped Cslib.Probability.PMF

namespace Cslib.Probability.PMF

variable {α : Type*}

/-- The statistical distance from a point mass is the mass the other distribution places
elsewhere. -/
theorem dist_pure_left [Fintype α] (a : α) (q : PMF α) :
    dist (PMF.pure a) q = 1 - (q a).toReal := by
  classical
  rw [dist_eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ a)]
  have hrest : ∑ b ∈ Finset.univ.erase a, |((PMF.pure a) b).toReal - (q b).toReal| =
      ∑ b ∈ Finset.univ.erase a, (q b).toReal := by
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [PMF.pure_apply_of_ne _ _ (Finset.ne_of_mem_erase hb), ENNReal.toReal_zero, zero_sub,
      abs_neg, abs_of_nonneg ENNReal.toReal_nonneg]
  have hsum : (q a).toReal + ∑ b ∈ Finset.univ.erase a, (q b).toReal = 1 := by
    rw [Finset.add_sum_erase _ (fun b => (q b).toReal) (Finset.mem_univ a)]
    exact sum_toReal q
  have hle : (q a).toReal ≤ 1 := by
    linarith [Finset.sum_nonneg fun b (_ : b ∈ Finset.univ.erase a) =>
      (ENNReal.toReal_nonneg : 0 ≤ (q b).toReal)]
  rw [hrest, PMF.pure_apply_self, ENNReal.toReal_one, abs_of_nonneg (by linarith)]
  linarith

/-- Statistical distance on `Bool` is the difference of the probabilities of `true`. -/
theorem dist_bool (p q : PMF Bool) :
    dist p q = |(p true).toReal - (q true).toReal| := by
  have hfalse (r : PMF Bool) : (r false).toReal = 1 - (r true).toReal := by
    have h := sum_toReal r
    rw [Fintype.sum_bool] at h
    linarith
  rw [dist_eq, Fintype.sum_bool, hfalse p, hfalse q,
    show 1 - (p true).toReal - (1 - (q true).toReal) = -((p true).toReal - (q true).toReal) by
      ring, abs_neg]
  ring

end Cslib.Probability.PMF
