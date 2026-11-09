/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Submodular.Basic
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic

/-!
# Two-batch stochastic-oracle savings

[Wang2027], Theorem 2(1), PDF p. 7: the exact savings function is nonnegative
and submodular. The finite type indexes all oracles, `p` gives their independent
success probabilities, and `c` their nonnegative expected token costs. This endpoint
is an algebraic property of the stated function; neither the scheduling reduction
nor the FPTAS in Theorem 2(2) is asserted here.

## Main results

* `savings_nonneg`: nonnegative savings for probabilities in the unit interval.
* `savings_isSubmodular`: diminishing returns, without a monotonicity assumption.
-/

public section
noncomputable section
namespace Cslib.Algorithms.Lean.Submodular.OracleSavings
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Probability that all selected independent calls fail. -/
@[expose] def failureProbability (p : ι → ℝ) (A : Finset ι) : ℝ := ∏ i ∈ A, (1 - p i)

/-- Cost of the oracles left for the second batch. -/
@[expose] def remainingCost (c : ι → ℝ) (A : Finset ι) : ℝ := ∑ i ∈ Aᶜ, c i

/-- Expected saving relative to querying all oracles in one batch. -/
@[expose] def savings (p c : ι → ℝ) (A : Finset ι) : ℝ :=
  (1 - failureProbability p A) * remainingCost c A

omit [Fintype ι] [DecidableEq ι] in
theorem failure_nonneg {p : ι → ℝ} (hp : ∀ i, p i ≤ 1) (A : Finset ι) :
    0 ≤ failureProbability p A := prod_nonneg fun i _ => sub_nonneg.mpr (hp i)

omit [Fintype ι] [DecidableEq ι] in
theorem failure_le_one {p : ι → ℝ} (hp₀ : ∀ i, 0 ≤ p i) (hp₁ : ∀ i, p i ≤ 1)
    (A : Finset ι) : failureProbability p A ≤ 1 := by
  exact prod_le_one₀ (fun i _ => sub_nonneg.mpr (hp₁ i)) (fun i _ => by linarith [hp₀ i])

omit [Fintype ι] [DecidableEq ι] in
theorem failure_antitone {p : ι → ℝ} (hp₀ : ∀ i, 0 ≤ p i) (hp₁ : ∀ i, p i ≤ 1) :
    Antitone (failureProbability p) := by
  intro A B hAB
  exact prod_le_prod_of_subset_of_le_one₀ hAB (fun i _ => sub_nonneg.mpr (hp₁ i))
    (fun i _ _ => by linarith [hp₀ i])

theorem remaining_nonneg {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i) (A : Finset ι) :
    0 ≤ remainingCost c A := sum_nonneg fun i _ => hc i

theorem remaining_antitone {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i) :
    Antitone (remainingCost c) := by
  intro A B hAB
  exact sum_le_sum_of_subset_of_nonneg (compl_subset_compl.mpr hAB) (fun i _ _ => hc i)

theorem savings_nonneg {p c : ι → ℝ} (hp₀ : ∀ i, 0 ≤ p i) (hp₁ : ∀ i, p i ≤ 1)
    (hc : ∀ i, 0 ≤ c i) (A : Finset ι) : 0 ≤ savings p c A :=
  mul_nonneg (sub_nonneg.mpr (failure_le_one hp₀ hp₁ A)) (remaining_nonneg hc A)

private theorem remaining_insert (c : ι → ℝ) (A : Finset ι) (i : ι) (hi : i ∉ A) :
    remainingCost c (insert i A) = remainingCost c A - c i := by
  have heq : Aᶜ = insert i (insert i A)ᶜ := by
    ext j
    by_cases h : j = i
    · subst j; simp [hi]
    · simp [h]
  have hn : i ∉ (insert i A)ᶜ := by simp
  unfold remainingCost
  rw [heq, sum_insert hn]
  ring

/-- Exact marginal saving, valid even when the marginal is negative. -/
theorem marginal_savings (p c : ι → ℝ) (A : Finset ι) (i : ι) (hi : i ∉ A) :
    marginalGain (savings p c) A i =
      failureProbability p A * (p i * remainingCost c (insert i A) + c i) - c i := by
  unfold marginalGain savings
  rw [show failureProbability p (insert i A) = (1 - p i) * failureProbability p A from
      prod_insert hi,
    remaining_insert c A i hi]
  ring

/-- The complete savings-function endpoint, for arbitrary finite oracle populations. -/
theorem savings_isSubmodular {p c : ι → ℝ} (hp₀ : ∀ i, 0 ≤ p i)
    (hp₁ : ∀ i, p i ≤ 1) (hc : ∀ i, 0 ≤ c i) : IsSubmodular (savings p c) := by
  apply isSubmodular_iff_marginalGain_le.mpr
  intro A B i hAB hiB
  have hiA : i ∉ A := fun h => hiB (hAB h)
  rw [marginal_savings p c B i hiB, marginal_savings p c A i hiA]
  apply sub_le_sub_right
  exact mul_le_mul (failure_antitone hp₀ hp₁ hAB)
    (add_le_add (mul_le_mul_of_nonneg_left
      (remaining_antitone hc (insert_subset_insert i hAB)) (hp₀ i)) le_rfl)
    (add_nonneg (mul_nonneg (hp₀ i) (remaining_nonneg hc _)) (hc i))
    (failure_nonneg hp₁ A)

end Cslib.Algorithms.Lean.Submodular.OracleSavings
