/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Probability.KWiseIndependent
import Complexity.Foundations.Data.Finset.OffDiag

/-!
# Second moments under pairwise independence

For a pairwise independent hash family `h` with seed `i` drawn uniformly and scores
`Z x : Y → ℝ` of average zero at the points `x` of a finite set `S`, the average square of the sum
`∑ x ∈ S, Z x (h i x)` is the sum of the average squares
(`Cslib.Probability.IsKWiseIndependentHash.expect_sq_sum`): the cross terms vanish. This gives the
unbiasedness of the tug-of-war estimator of Alon, Matias and Szegedy [AlonMatiasSzegedy1999] and
the variance of an average of independent samples.

## Main results

* `Cslib.Probability.IsKWiseIndependentHash.expect_sq_sum`: second moments of sums of centered
  scores add under pairwise independence.

## References

* [N. Alon, Y. Matias, M. Szegedy, *The space complexity of approximating the frequency
  moments*, Theorem 2.2][AlonMatiasSzegedy1999]
-/

public section

open Finset
open scoped BigOperators

namespace Cslib.Probability

variable {ι X Y : Type*} [Fintype ι] [Fintype Y] [DecidableEq Y]

namespace IsKWiseIndependentHash

variable {h : ι → X → Y}

/-- **Second moments add under pairwise independence**: for scores `Z x : Y → ℝ` of average zero at
the points of a finite set `S`, the average square of `∑ x ∈ S, Z x (h i x)` is the sum of the
average squares. -/
theorem expect_sq_sum (hh : IsKWiseIndependentHash 2 h) (S : Finset X) (Z : X → Y → ℝ)
    (hZ : ∀ x ∈ S, 𝔼 y, Z x y = 0) :
    𝔼 i, (∑ x ∈ S, Z x (h i x)) ^ 2 = ∑ x ∈ S, 𝔼 y, Z x y ^ 2 := by
  classical
  simp only [sq_sum_eq_sum_sq_add_sum_offDiag, expect_add_distrib, expect_sum_comm]
  have hdiag : ∀ x ∈ S, 𝔼 i, Z x (h i x) ^ 2 = 𝔼 y, Z x y ^ 2 := fun x _ => by
    have := hh.expect_prod (T := {x}) (by simp) fun x y => Z x y ^ 2
    simpa only [prod_singleton] using this
  have hoff : ∀ p ∈ S.offDiag, 𝔼 i, Z p.1 (h i p.1) * Z p.2 (h i p.2) = 0 := fun p hp => by
    obtain ⟨h1, -, hne⟩ := mem_offDiag.1 hp
    have := hh.expect_prod (T := {p.1, p.2}) card_le_two fun x y => Z x y
    simp only [prod_pair hne, hZ _ h1, zero_mul] at this
    exact this
  rw [sum_congr rfl hdiag, sum_congr rfl hoff, sum_const_zero, add_zero]

end IsKWiseIndependentHash

end Cslib.Probability
