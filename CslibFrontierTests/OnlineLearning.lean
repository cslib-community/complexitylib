/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.MachineLearning.OnlineLearning.Hedge
import CslibFrontier.MachineLearning.OnlineLearning.WeightedMajority
import CslibFrontier.MachineLearning.OnlineLearning.ZeroSum
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Checks for learning with experts: concrete multiplicative-weights and Hedge distributions,
weighted majority with a perfect expert, a failure of the mistake bound without the
weighted-majority hypothesis, the range of the quadratic `exp` estimate, the value of matching
pennies, the algorithmic minimax theorem on it, and the conditions of the tuned regret bounds. -/

namespace ComplexityTests.OnlineLearning

open Finset Real Cslib.MachineLearning.OnlineLearning.Experts Cslib.Probability Convexity

/-! ### Concrete distributions -/

/-- After one round of MW with `η = 1 / 2` and losses `(1, 0)`, the weights are `(1 / 2, 1)`, so
the distribution is `(1 / 3, 2 / 3)`. -/
example : prob (mwFactor (1 / 2)) (fun _ (i : Bool) => if i then 1 else 0) 1 true = 1 / 3 := by
  norm_num [prob, potential, weight, Fintype.sum_bool]

/-- Against zero losses, Hedge plays the uniform distribution. -/
example {ι : Type*} [Fintype ι] (η : ℝ) (t : ℕ) (i : ι) :
    prob (hedgeFactor η) (fun _ _ => 0) t i = 1 / Fintype.card ι := by
  simp only [prob, potential, weight, hedgeFactor_apply, mul_zero, neg_zero, exp_zero,
    prod_const_one, sum_const, card_univ, nsmul_eq_mul, mul_one]

/-- The weight of an expert that erred twice in three rounds is `(1 - η) ^ 2`. -/
example (η : ℝ) :
    weight (mwFactor η) (expertLoss (fun t (_ : Unit) => decide (t = 1)) fun _ => true) 3 () =
      (1 - η) ^ 2 := by
  rw [weight_mwFactor_expertLoss]
  rfl

/-! ### Weighted majority -/

/-- With a perfect expert, weighted majority makes at most `2 ln n / η` mistakes. -/
example {ι : Type*} [Fintype ι] (advice : ℕ → ι → Bool) (outcome : ℕ → Bool) (i : ι)
    (hi : ∀ t, advice t i = outcome t) (T : ℕ) :
    (#{t ∈ range T | weightedMajority advice outcome (1 / 2) t ≠ outcome t} : ℝ) ≤
      4 * log (Fintype.card ι) := by
  have h := weightedMajority_mistakes_le (T := T) (advice := advice) (outcome := outcome)
    (by norm_num : (0 : ℝ) < 1 / 2) le_rfl i
  simp only [hi, ne_eq, not_true_eq_false, filter_false, card_empty, Nat.cast_zero,
    mul_zero, zero_add] at h
  linarith

/-- Without the weighted-majority hypothesis the mistake bound fails: one expert, always right,
and a learner that is always wrong. -/
example : ¬ (#{t ∈ range 1 | (fun _ => false) t ≠ (fun _ => true) t} : ℝ) ≤
    2 * (1 + 1 / 2) * #{t ∈ range 1 | (fun _ (_ : Unit) => true) t () ≠ (fun _ => true) t} +
      2 * log (Fintype.card Unit) / (1 / 2) := by
  norm_num

/-! ### The quadratic `exp` estimate needs `y ≥ -1` (up to a constant) -/

/-- `exp (-y) ≤ 1 - y + y ^ 2` fails at `y = -2`: `exp 2 > 7`. -/
example : ¬ exp (-(-2 : ℝ)) ≤ 1 - (-2) + (-2) ^ 2 := by
  have h := exp_one_gt_d9
  have h2 : exp (-(-2 : ℝ)) = exp 1 * exp 1 := by
    rw [← exp_add]
    norm_num
  rw [h2]
  nlinarith

/-! ### Matching pennies -/

/-- Matching pennies: the row player pays `1` when the coins match. -/
noncomputable def pennies (i j : Bool) : ℝ := if i = j then 1 else 0

/-- The uniform distribution on `Bool`. -/
noncomputable def uniform : StdSimplex ℝ Bool :=
  .duple true false (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)

theorem isMinimaxValue_pennies : IsMinimaxValue pennies (1 / 2) := by
  refine ⟨⟨uniform, fun j => ?_⟩, uniform, fun i => ?_⟩
  · cases j <;> norm_num [uniform, pennies, StdSimplex.duple, Fintype.sum_bool]
  · cases i <;> norm_num [uniform, pennies, StdSimplex.duple, Fintype.sum_bool]

/-- The value of matching pennies is not `2 / 5`. -/
example : ¬ IsMinimaxValue pennies (2 / 5) := fun h => by
  have := h.unique isMinimaxValue_pennies
  norm_num at this

theorem pennies_mem_Icc (i j : Bool) : pennies i j ∈ Set.Icc (0 : ℝ) 1 := by
  unfold pennies
  split_ifs <;> norm_num

/-- The algorithmic minimax theorem on matching pennies with `ε = 1 / 4`: after
`⌈4 ln 2 / (1 / 4) ^ 2⌉` rounds of multiplicative weights against best responses, the average row
strategy pays at most `3 / 4` against both columns, and the empirical column strategy collects at
least `1 / 4` against both rows. -/
example :
    let T := ⌈4 * log (Fintype.card Bool) / (1 / 4) ^ 2⌉₊
    (∀ j, ∑ k, averageProb (prob (mwFactor (1 / 4 / 2))
        (fun s i => pennies i (bestResponsePlay pennies (1 / 4 / 2) s))) T k * pennies k j ≤
          1 / 2 + 1 / 4) ∧
      ∀ i, 1 / 2 - 1 / 4 ≤
        ∑ l, empirical (bestResponsePlay pennies (1 / 4 / 2)) T l * pennies i l :=
  bestResponsePlay_approx_optimal (by simp only [Fintype.card_bool, le_refl]) pennies_mem_Icc
    (by norm_num) (by norm_num) isMinimaxValue_pennies

/-! ### Tuned regret -/

/-- With two experts, `T = 4` rounds already satisfy `T ≥ 4 ln n`. -/
example (ℓ : ℕ → Bool → ℝ) (hℓ : ∀ s < 4, ∀ i, |ℓ s i| ≤ 1) (i : Bool) :
    ∑ t ∈ range 4, ∑ j, prob (mwFactor √(log (Fintype.card Bool) / (4 : ℕ))) ℓ t j * ℓ t j ≤
      ∑ t ∈ range 4, ℓ t i + 2 * √((4 : ℕ) * log (Fintype.card Bool)) :=
  mw_regret_le_sqrt (by simp only [Fintype.card_bool, le_refl])
    (by
      have := log_two_lt_d9
      simp only [Fintype.card_bool, Nat.cast_ofNat]
      linarith) hℓ i

/-- With two experts, `T = 1` round already satisfies `T ≥ ln n`, the condition of tuned Hedge. -/
example (ℓ : ℕ → Bool → ℝ) (hℓ : ∀ s < 1, ∀ i, |ℓ s i| ≤ 1) (i : Bool) :
    ∑ t ∈ range 1, ∑ j, prob (hedgeFactor √(log (Fintype.card Bool) / (1 : ℕ))) ℓ t j * ℓ t j ≤
      ∑ t ∈ range 1, ℓ t i + 2 * √((1 : ℕ) * log (Fintype.card Bool)) :=
  hedge_regret_le_sqrt (by simp only [Fintype.card_bool, le_refl])
    (by
      have := log_two_lt_d9
      simp only [Fintype.card_bool, Nat.cast_ofNat, Nat.cast_one]
      linarith) hℓ i

end ComplexityTests.OnlineLearning
