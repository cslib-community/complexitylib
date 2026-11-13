/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.Randomized.ZeroError

/-!
# Distributional expected query cost

A deterministic tree's `distributionalCost` averages its executed query count over an input
simplex. The averaging direction of expected-cost Yao holds even without a finite coordinate
type: an always-correct randomized tree with a worst-input expected bound supplies a correct
pure tree with that distributional bound against every finitely supported input distribution.

## Main definitions

* `Cslib.DecisionTree.distributionalCost`: average executed queries under an input distribution.

## Main results

* `Cslib.RandomizedDecisionTree.Computes.exists_distributionalCost_le`: fix a random choice
  while preserving correctness and a distributional expected-cost bound.

## References

* [AroraBarak07], Definitions 11.13, 11.15–11.16 and Theorem 11.17.
-/

public section

namespace Cslib

open Convexity Finset

namespace DecisionTree

variable {ι β : Type*}

/-- Expected executed-query cost under a finitely supported input distribution. Coordinate
finiteness is unnecessary for this definition. -/
noncomputable def distributionalCost (t : DecisionTree ι β)
    (ν : StdSimplex ℝ (ι → Bool)) : ℝ :=
  ν.weights.sum fun x w => w * (t.cost x : ℝ)

/-- Expand the expected cost as a finite weighted sum over inputs. -/
theorem distributionalCost_eq_sum (t : DecisionTree ι β) (ν : StdSimplex ℝ (ι → Bool)) :
    t.distributionalCost ν = ν.weights.sum (fun x w => w * (t.cost x : ℝ)) := by
  unfold distributionalCost
  rfl

theorem distributionalCost_nonneg (t : DecisionTree ι β)
    (ν : StdSimplex ℝ (ι → Bool)) : 0 ≤ t.distributionalCost ν :=
  Finset.sum_nonneg fun x _ => mul_nonneg (ν.weights_nonneg x) (Nat.cast_nonneg _)

/-- Pointwise domination of executed query costs implies domination of expected costs. -/
theorem distributionalCost_mono {s t : DecisionTree ι β}
    (h : ∀ x, s.cost x ≤ t.cost x) (ν : StdSimplex ℝ (ι → Bool)) :
    s.distributionalCost ν ≤ t.distributionalCost ν :=
  Finset.sum_le_sum fun x _ =>
    mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (h x)) (ν.weights_nonneg x)

@[simp] theorem distributionalCost_single (t : DecisionTree ι β) (x : ι → Bool) :
    t.distributionalCost (StdSimplex.single x) = t.cost x := by
  simp [distributionalCost]

@[simp] theorem distributionalCost_leaf (b : β) (ν : StdSimplex ℝ (ι → Bool)) :
    (DecisionTree.leaf b : DecisionTree ι β).distributionalCost ν = 0 := by
  simp [distributionalCost]

end DecisionTree

namespace RandomizedDecisionTree

private theorem mean_distributionalCost_eq_mean_expectedCost {ι β : Type*}
    (μ : RandomizedDecisionTree ι β) (ν : StdSimplex ℝ (ι → Bool)) :
    (μ.weights.sum fun t w => w * t.distributionalCost ν) =
      ν.weights.sum (fun x w => w * μ.expectedCost x) := by
  simp only [DecisionTree.distributionalCost, expectedCost_eq_sum, Finsupp.sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => mul_left_comm _ _ _

/-- An always-correct randomized tree with a worst-input expected bound supplies a correct
pure tree with that distributional cost bound against any input distribution. -/
theorem Computes.exists_distributionalCost_le {ι β : Type*}
    {μ : RandomizedDecisionTree ι β} {f : (ι → Bool) → β} {c : ℝ}
    (hμ : μ.Computes 0 f) (ν : StdSimplex ℝ (ι → Bool))
    (hc : ∀ x, μ.expectedCost x ≤ c) :
    ∃ t : DecisionTree ι β, t.Computes f ∧ t.distributionalCost ν ≤ c := by
  obtain ⟨t, ht, hle⟩ := StdSimplex.exists_mem_support_le_sum_mul μ
    (fun t => t.distributionalCost ν)
  refine ⟨t, computes_zero_iff.mp hμ t ht, hle.trans ?_⟩
  rw [mean_distributionalCost_eq_mean_expectedCost]
  exact StdSimplex.sum_mul_le_of_forall_le fun x _ => hc x

end RandomizedDecisionTree

end Cslib
