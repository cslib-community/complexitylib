/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.QueryComplexity.ApproximateDegree.Or
import Complexity.Computability.QueryComplexity.Midrijanis
import Complexity.Foundations.Analysis.MarkovBrothersInequality
import Complexity.Foundations.BooleanAnalysis.Symmetrization
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema

/-! Markov's inequality and its discrete forms, Minsky–Papert symmetrization, approximate degree
and the Nisan–Szegedy bounds on concrete instances: Chebyshev polynomials attain Markov's bound,
layer averages of monomials, the disjunction of `n` bits, parity and majority. Non-vacuity
witnesses for the hypotheses. -/

namespace ComplexityTests.QueryComplexity.Approximate

open Cslib Cslib.BitString Cslib.QueryComplexity Polynomial

/-! ### Markov's inequality and symmetrization -/

/-- Markov's bound is attained on `Chebyshev.T`, Bernstein's inequality at the center, Markov's
inequality on `[0, 2]` for `X²`, the Nisan–Szegedy slope witness on `{0, 1}`, Ehlich–Zeller on
`[0, 4]`, Chebyshev growth beyond `1`, and Minsky–Papert layer averages. -/
example (n : ℕ) {p : ℝ[X]} (hp : p.natDegree ≤ n) {M : ℝ}
    (hM : ∀ y ∈ Set.Icc (-1 : ℝ) 1, |p.eval y| ≤ M)
    (x₂ : ℝ) (hx₂ : x₂ ∈ Set.Icc (0 : ℝ) 2)
    (x₄ : ℝ) (hx₄ : x₄ ∈ Set.Icc (0 : ℝ) (4 : ℕ))
    {μ : ℝ} (hμ : 0 ≤ μ) :
    ((∀ x ∈ Set.Icc (-1 : ℝ) 1, |(Polynomial.derivative (Chebyshev.T ℝ n)).eval x| ≤ n ^ 2 * 1) ∧
      (Polynomial.derivative (Chebyshev.T ℝ n)).eval 1 = n ^ 2) ∧
    |(Polynomial.derivative p).eval 0| ≤ n * M ∧
    (2 - 0) * |(Polynomial.derivative (X ^ 2 : ℝ[X])).eval x₂| ≤ 2 * (2 : ℕ) ^ 2 * 4 ∧
    (1 : ℝ) * (1 : ℕ) ≤ (1 : ℕ) ^ 2 * (1 + (1 - 0)) ∧
    ((4 : ℕ) - (1 : ℕ) ^ 2) * |(X : ℝ[X]).eval x₄| ≤ (4 : ℕ) * 4 ∧
    1 + (2 : ℕ) ^ 2 * μ ≤ (Chebyshev.T ℝ (2 : ℕ)).eval (1 + μ) ∧
    layerAverage (monomial ℝ ({0} : Finset (Fin 3))) 1 = 1 / 3 ∧
    (∃ q : ℝ[X], q.natDegree ≤ 1 ∧
      ∀ k ≤ Fintype.card (Fin 4), q.eval (k : ℝ) = layerAverage (fun x : Fin 4 → Bool =>
        (weight x : ℝ)) k) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, Chebyshev.one_add_sq_mul_le_eval_T 2 hμ, ?_,
    exists_natDegree_le_eval_eq_layerAverage weight_mem_lowDegree⟩
  · refine ⟨fun x hx => abs_eval_derivative_le_sq_mul (Chebyshev.natDegree_T ℝ n).le
      (fun y hy => Chebyshev.abs_eval_T_real_le_one n (abs_le.2 hy)) hx, ?_⟩
    exact_mod_cast Chebyshev.derivative_T_eval_one (R := ℝ) n
  · simpa using sqrt_mul_abs_eval_derivative_le hp hM (x := 0) (by norm_num)
  · exact sub_mul_abs_eval_derivative_le (by simp) (by norm_num) (fun y hy => by
      simp only [eval_pow, eval_X]
      rw [abs_of_nonneg (by positivity)]
      nlinarith [hy.1, hy.2]) hx₂
  · exact mul_le_sq_mul_of_le_abs_eval_derivative (q := X) (by simp) one_pos
      (b₁ := 0) (b₂ := 1) (fun k hk => by interval_cases k <;> simp)
      (ξ := 0) (by simp) zero_le_one (by simp)
  · exact sub_mul_abs_eval_le_of_forall_nat (by simp) (by norm_num) (fun k hk => by
      simp only [eval_X, Nat.abs_cast]
      exact_mod_cast hk) hx₄
  · rw [layerAverage_monomial _ (by simp)]
    simp

/-! ### Approximate degree and the Nisan–Szegedy bounds -/

/-- A single bit has approximate degree `1`: `1 ≤ 6 adeg²` and `adeg ≤ deg = 1`. -/
private theorem approxDegree_threshold_one_one : approxDegree (1 / 3) (threshold 1 1) = 1 := by
  have h₁ := card_le_six_mul_approxDegree_threshold_one_right_sq (n := 1)
  have h₂ := (approxDegree_le_degree (f := threshold 1 1) (by norm_num : (0 : ℝ) ≤ 1 / 3)).trans
    degree_threshold_one_right.le
  interval_cases h : approxDegree (1 / 3) (threshold 1 1) <;> simp_all

/-- Approximate degree of general Boolean functions, negated thresholds, the `Θ(√n)` disjunction
bounds, the concrete `n = 100` separation (`5 ≤ adeg ≤ 15 < deg = 100`), and the Nisan–Szegedy
polynomial relations with block sensitivity and decision-tree complexity. -/
example {n : ℕ} (f : BooleanFunction n) :
    approxDegree 0 f = degree f ∧
    approxDegree (1 / 2) f = 0 ∧
    (approxDegree (1 / 3) f ≤ degree f ∧ degree f ≤ DecisionTree.complexity f) ∧
    approxDegree (1 / 3) (fun x => !threshold 1 1 x) = 1 ∧
    (n ≤ 6 * approxDegree (1 / 3) (fun x => !threshold n 1 x) ^ 2 ∧
      approxDegree (1 / 3) (fun x => !threshold n 1 x) ≤ n) ∧
    (n ≤ 6 * approxDegree (1 / 3) (threshold n 1) ^ 2 ∧
      approxDegree (1 / 3) (threshold n 1) ≤ Nat.sqrt (2 * n) + 1) ∧
    (5 ≤ approxDegree (1 / 3) (threshold 100 1) ∧ approxDegree (1 / 3) (threshold 100 1) ≤ 15 ∧
      degree (threshold 100 1) = 100) ∧
    (blockSensitivity f ≤ 2 * degree f ^ 2 ∧ blockSensitivity f ≤ 6 * approxDegree (1 / 3) f ^ 2 ∧
      blockSensitivity f ≤ 2 * sensitivity f ^ 4) ∧
    (DecisionTree.complexity f ≤ 2 * degree f ^ 3 ∧
      DecisionTree.complexity f ≤ 216 * approxDegree (1 / 3) f ^ 6) ∧
    (1 / 2 : ℝ) * blockSensitivity f ≤ 2 * approxDegree (1 / 4) f ^ 2 ∧
    blockSensitivity (majority 3) ≤ 2 * degree (majority 3) ^ 2 := by
  refine ⟨approxDegree_zero, approxDegree_eq_zero_of_le le_rfl,
    ⟨approxDegree_le_degree (by norm_num), DecisionTree.degree_le_complexity f⟩,
    (approxDegree_not _ _).trans approxDegree_threshold_one_one, ?_,
    ⟨card_le_six_mul_approxDegree_threshold_one_right_sq, approxDegree_threshold_one_right_le_sqrt⟩,
    ?_,
    ⟨blockSensitivity_le_two_mul_degree_sq f, blockSensitivity_le_six_mul_approxDegree_sq f,
      blockSensitivity_le_two_mul_sensitivity_pow_four f⟩,
    ⟨DecisionTree.complexity_le_two_mul_degree_pow_three f,
      DecisionTree.complexity_le_mul_approxDegree_pow_six f⟩,
    ?_, blockSensitivity_le_two_mul_degree_sq _⟩
  · refine ⟨?_, approxDegree_le_card (by norm_num)⟩
    rw [approxDegree_not]
    exact card_le_six_mul_approxDegree_threshold_one_right_sq
  · refine ⟨?_, approxDegree_threshold_one_right_le (by norm_num), degree_threshold_one_right⟩
    have := card_le_six_mul_approxDegree_threshold_one_right_sq (n := 100)
    by_contra h
    push Not at h
    interval_cases approxDegree (1 / 3) (threshold 100 1) <;> omega
  · have := one_sub_two_mul_mul_blockSensitivity_le (by norm_num : (0 : ℝ) ≤ 1 / 4) f
    norm_num at this ⊢
    linarith

end ComplexityTests.QueryComplexity.Approximate
