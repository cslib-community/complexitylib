/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate (general mathematics for Mathlib)

public import CslibFrontier.Init
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Bounds for products of independent failure factors

For factors in the unit interval, the probability of at least one success lies
between the sum minus half its square and the sum. The proof is an elementary
finite induction, requiring no exponential approximation or analytic hypotheses.

## Main results

* `Finset.one_sub_prod_one_sub_bounds`: simultaneous union and quadratic lower bounds.
-/

public section
namespace Finset

/-- Union and second-order Bonferroni bounds for independent event probabilities,
expressed algebraically in any linearly ordered field. -/
theorem one_sub_prod_one_sub_bounds {ι K : Type*}
    [Field K] [LinearOrder K] [IsStrictOrderedRing K] (A : Finset ι) (p : ι → K)
    (hp : ∀ i ∈ A, 0 ≤ p i ∧ p i ≤ 1) :
    (∑ i ∈ A, p i) - (∑ i ∈ A, p i)^2 / 2 ≤ 1 - ∏ i ∈ A, (1 - p i) ∧
      1 - ∏ i ∈ A, (1 - p i) ≤ ∑ i ∈ A, p i := by
  classical
  induction A using Finset.induction_on with
  | empty => simp
  | @insert i A hi ih =>
    have hpi := hp i (mem_insert_self ..)
    have ih := ih (fun j hj => hp j (mem_insert_of_mem hj))
    have hs : 0 ≤ ∑ j ∈ A, p j := sum_nonneg (fun j hj => (hp j (mem_insert_of_mem hj)).1)
    have hmul := mul_le_mul_of_nonneg_left ih.1 (sub_nonneg.mpr hpi.2)
    have hmul' := mul_le_mul_of_nonneg_left ih.2 (sub_nonneg.mpr hpi.2)
    rw [sum_insert hi, prod_insert hi]
    constructor <;> nlinarith [sq_nonneg (p i), mul_nonneg hpi.1 (sq_nonneg (∑ j ∈ A, p j)),
      mul_nonneg hpi.1 hs]

end Finset
