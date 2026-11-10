/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.MachineLearning.OnlineLearning.SwapRegret
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Checks for swap regret: a play sequence with zero external regret but positive swap regret,
a concrete stationary vector, the Blum–Mansour learner against zero losses, external regret as
the constant-swap special case, and the conditions of the tuned swap-regret bound. -/

namespace CslibFrontierTests.SwapRegret

open Finset Matrix Real Cslib.MachineLearning.OnlineLearning.Experts

/-! ### Swap regret is stronger than external regret -/

/-- The loss vectors `(1, 0, 2)`, `(2, 1, 0)` and `(0, 2, 1)` in rounds `0`, `1` and `2`. -/
noncomputable def sepLoss (t : ℕ) : Fin 3 → ℝ :=
  if t = 0 then ![1, 0, 2] else if t = 1 then ![2, 1, 0] else ![0, 2, 1]

/-- The learner plays action `t` in round `t`. -/
noncomputable def sepPlay (t : ℕ) : Fin 3 → ℝ :=
  if t = 0 then ![1, 0, 0] else if t = 1 then ![0, 1, 0] else ![0, 0, 1]

/-- Every action has total loss `3`, the learner's total loss: zero external regret. -/
example (k : Fin 3) :
    ∑ t ∈ range 3, ∑ i, sepPlay t i * sepLoss t i ≤ ∑ t ∈ range 3, sepLoss t k := by
  fin_cases k <;> norm_num [sepPlay, sepLoss, sum_range_succ, Fin.sum_univ_three]

/-- Swapping `0 ↦ 1`, `1 ↦ 2`, `2 ↦ 0` would have lost nothing: swap regret `3`. -/
example :
    ∑ t ∈ range 3, ∑ i, sepPlay t i * sepLoss t i =
      ∑ t ∈ range 3, ∑ i, sepPlay t i * sepLoss t (![1, 2, 0] i) + 3 := by
  norm_num [sepPlay, sepLoss, sum_range_succ, Fin.sum_univ_three]

/-! ### Stationary vectors -/

/-- The Markov chain with rows `(1 / 2, 1 / 2)` and `(1 / 4, 3 / 4)`. -/
noncomputable def chain : Matrix (Fin 2) (Fin 2) ℝ := !![1 / 2, 1 / 2; 1 / 4, 3 / 4]

/-- Its only stationary distribution is `(1 / 3, 2 / 3)`, so that is the chosen one. -/
example : stationaryVec chain 0 = 1 / 3 := by
  have hM : chain ∈ rowStochastic ℝ (Fin 2) := by
    rw [mem_rowStochastic_iff_sum]
    constructor
    · intro i j
      fin_cases i <;> fin_cases j <;> norm_num [chain]
    · intro i
      fin_cases i <;> norm_num [chain, Fin.sum_univ_two]
  have h1 := sum_stationaryVec hM
  have h2 := congrFun (stationaryVec_vecMul hM) 0
  generalize stationaryVec chain = p at h1 h2 ⊢
  simp only [Fin.sum_univ_two] at h1
  simp [vecMul_apply_eq_sum, Fin.sum_univ_two, chain] at h2
  linarith

/-! ### The Blum–Mansour learner -/

/-- Against zero losses every copy plays the uniform distribution, whose only stationary vector
is uniform: the learner plays the uniform distribution. -/
example {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (η : ℝ) (t : ℕ) (i : ι) :
    blumMansourProb η (fun _ _ => 0) t i = 1 / Fintype.card ι := by
  have h := congrFun (blumMansourProb_vecMul η (fun _ (_ : ι) => 0) t) i
  have h1 := sum_blumMansourProb η (fun _ (_ : ι) => (0 : ℝ)) t
  simp only [vecMul_apply_eq_sum, blumMansourMatrix_eq_prob, prob, potential, weight,
    blumMansourLoss_apply, mul_zero, hedgeFactor_apply, neg_zero, exp_zero, prod_const_one,
    sum_const, card_univ, nsmul_eq_mul, mul_one, ← sum_mul, h1, one_mul] at h
  exact h.symm

/-- A constant swapping function recovers an external-regret bound. -/
example {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {η : ℝ} (hη : 0 < η) (hη' : η ≤ 1)
    {T : ℕ} (ℓ : ℕ → ι → ℝ) (hℓ : ∀ s < T, ∀ i, |ℓ s i| ≤ 1) (k : ι) :
    ∑ t ∈ range T, ∑ i, blumMansourProb η ℓ t i * ℓ t i ≤
      ∑ t ∈ range T, ℓ t k + (η * T + Fintype.card ι * log (Fintype.card ι) / η) := by
  have h := blumMansour_swap_regret_le hη hη' hℓ fun _ => k
  simp only [← sum_mul, sum_blumMansourProb, one_mul] at h
  exact h

/-- With two experts, `T = 2` rounds already satisfy `T ≥ n ln n`, the condition of the tuned
bound. -/
example (ℓ : ℕ → Bool → ℝ) (hℓ : ∀ s < 2, ∀ i, |ℓ s i| ≤ 1) (δ : Bool → Bool) :
    ∑ t ∈ range 2, ∑ i, blumMansourProb
        √(Fintype.card Bool * log (Fintype.card Bool) / (2 : ℕ)) ℓ t i * ℓ t i ≤
      ∑ t ∈ range 2, ∑ i, blumMansourProb
          √(Fintype.card Bool * log (Fintype.card Bool) / (2 : ℕ)) ℓ t i * ℓ t (δ i) +
        2 * √((2 : ℕ) * (Fintype.card Bool * log (Fintype.card Bool))) :=
  blumMansour_swap_regret_le_sqrt (by simp only [Fintype.card_bool, le_refl])
    (by
      have := log_two_lt_d9
      simp only [Fintype.card_bool, Nat.cast_ofNat]
      linarith) hℓ δ

end CslibFrontierTests.SwapRegret
