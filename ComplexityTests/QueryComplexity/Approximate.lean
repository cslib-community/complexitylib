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

/-! ### Markov's inequality -/

/-- Markov's bound is attained: `T n` is bounded by `1` on `[-1, 1]`, its derivative is bounded by
`n²` there, with equality at `1`. -/
example (n : ℕ) :
    (∀ x ∈ Set.Icc (-1 : ℝ) 1, |(Polynomial.derivative (Chebyshev.T ℝ n)).eval x| ≤ n ^ 2 * 1) ∧
      (Polynomial.derivative (Chebyshev.T ℝ n)).eval 1 = n ^ 2 := by
  refine ⟨fun x hx => abs_eval_derivative_le_sq_mul (Chebyshev.natDegree_T ℝ n).le
    (fun y hy => Chebyshev.abs_eval_T_real_le_one n (abs_le.2 hy)) hx, ?_⟩
  exact_mod_cast Chebyshev.derivative_T_eval_one (R := ℝ) n

/-- Bernstein's inequality at the center: `|p'(0)| ≤ n M`. -/
example {n : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ n) {M : ℝ}
    (hM : ∀ y ∈ Set.Icc (-1 : ℝ) 1, |p.eval y| ≤ M) :
    |(Polynomial.derivative p).eval 0| ≤ n * M := by
  simpa using sqrt_mul_abs_eval_derivative_le hp hM (x := 0) (by norm_num)

/-- Markov's inequality on `[0, 2]` for `X²`, bounded by `4`: `2 |2x| ≤ 2 · 2² · 4`. -/
example (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 2) :
    (2 - 0) * |(Polynomial.derivative (X ^ 2 : ℝ[X])).eval x| ≤ 2 * (2 : ℕ) ^ 2 * 4 :=
  sub_mul_abs_eval_derivative_le (by simp) (by norm_num) (fun y hy => by
    simp only [eval_pow, eval_X]
    rw [abs_of_nonneg (by positivity)]
    nlinarith [hy.1, hy.2]) hx

/-- The hypotheses of the Nisan–Szegedy lemma are satisfiable: `X` on `{0, 1}` has values in
`[0, 1]` and slope `1`, and the lemma gives `1 · 1 ≤ 1² · (1 + 1)`. -/
example : (1 : ℝ) * (1 : ℕ) ≤ (1 : ℕ) ^ 2 * (1 + (1 - 0)) :=
  mul_le_sq_mul_of_le_abs_eval_derivative (q := X) (by simp) one_pos
    (b₁ := 0) (b₂ := 1) (fun k hk => by
      interval_cases k <;> simp)
    (ξ := 0) (by simp) zero_le_one (by simp)

/-- The Ehlich–Zeller bound for `X` on `[0, 4]`, bounded by `4` at the integers. -/
example (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) (4 : ℕ)) :
    ((4 : ℕ) - (1 : ℕ) ^ 2) * |(X : ℝ[X]).eval x| ≤ (4 : ℕ) * 4 :=
  sub_mul_abs_eval_le_of_forall_nat (by simp) (by norm_num) (fun k hk => by
    simp only [eval_X, Nat.abs_cast]
    exact_mod_cast hk) hx

/-- Chebyshev polynomials grow beyond `1`: `T₂(1 + μ) = 2(1 + μ)² - 1 ≥ 1 + 4μ`. -/
example {μ : ℝ} (hμ : 0 ≤ μ) : 1 + (2 : ℕ) ^ 2 * μ ≤ (Chebyshev.T ℝ (2 : ℕ)).eval (1 + μ) :=
  Chebyshev.one_add_sq_mul_le_eval_T 2 hμ

/-! ### Symmetrization -/

/-- A single bit of three averages to `1 / 3` over the inputs of weight `1`. -/
example : layerAverage (monomial ℝ ({0} : Finset (Fin 3))) 1 = 1 / 3 := by
  rw [layerAverage_monomial _ (by simp)]
  simp

/-- The weight is a polynomial of degree `1` in itself, and its layer averages are the weights. -/
example : ∃ q : ℝ[X], q.natDegree ≤ 1 ∧
    ∀ k ≤ Fintype.card (Fin 4), q.eval (k : ℝ) = layerAverage (fun x : Fin 4 → Bool =>
      (weight x : ℝ)) k :=
  exists_natDegree_le_eval_eq_layerAverage weight_mem_lowDegree

/-! ### Approximate degree -/

example {n : ℕ} (f : BooleanFunction n) : approxDegree 0 f = degree f := approxDegree_zero

/-- From `ε = 1/2` on, every Boolean function has approximate degree `0`. -/
example {n : ℕ} (f : BooleanFunction n) : approxDegree (1 / 2) f = 0 :=
  approxDegree_eq_zero_of_le le_rfl

example {n : ℕ} (f : BooleanFunction n) :
    approxDegree (1 / 3) f ≤ degree f ∧ degree f ≤ DecisionTree.complexity f :=
  ⟨approxDegree_le_degree (by norm_num), DecisionTree.degree_le_complexity f⟩

/-- A single bit has approximate degree `1`: `1 ≤ 6 adeg²` and `adeg ≤ deg = 1`. -/
private theorem approxDegree_threshold_one_one : approxDegree (1 / 3) (threshold 1 1) = 1 := by
  have h₁ := card_le_six_mul_approxDegree_threshold_one_right_sq (n := 1)
  have h₂ := (approxDegree_le_degree (f := threshold 1 1) (by norm_num : (0 : ℝ) ≤ 1 / 3)).trans
    degree_threshold_one_right.le
  interval_cases h : approxDegree (1 / 3) (threshold 1 1) <;> simp_all

/-- Negation preserves approximate degree: the negated bit also has approximate degree `1`. -/
example : approxDegree (1 / 3) (fun x => !threshold 1 1 x) = 1 :=
  (approxDegree_not _ _).trans approxDegree_threshold_one_one

/-- The negated disjunction of `n` bits has approximate degree at least `√(n / 6)`, as the
disjunction does, and at most its number of bits `n`. -/
example {n : ℕ} : n ≤ 6 * approxDegree (1 / 3) (fun x => !threshold n 1 x) ^ 2 ∧
    approxDegree (1 / 3) (fun x => !threshold n 1 x) ≤ n := by
  refine ⟨?_, approxDegree_le_card (by norm_num)⟩
  rw [approxDegree_not]
  exact card_le_six_mul_approxDegree_threshold_one_right_sq

/-- The disjunction of `n` bits has approximate degree `Θ(√n)`. -/
example {n : ℕ} : n ≤ 6 * approxDegree (1 / 3) (threshold n 1) ^ 2 ∧
    approxDegree (1 / 3) (threshold n 1) ≤ Nat.sqrt (2 * n) + 1 :=
  ⟨card_le_six_mul_approxDegree_threshold_one_right_sq, approxDegree_threshold_one_right_le_sqrt⟩

/-- The disjunction of `100` bits has approximate degree between `5` and `15`, far below its degree
`100`. -/
example : 5 ≤ approxDegree (1 / 3) (threshold 100 1) ∧ approxDegree (1 / 3) (threshold 100 1) ≤ 15 ∧
    degree (threshold 100 1) = 100 := by
  refine ⟨?_, approxDegree_threshold_one_right_le (by norm_num), degree_threshold_one_right⟩
  have := card_le_six_mul_approxDegree_threshold_one_right_sq (n := 100)
  by_contra h
  push Not at h
  interval_cases approxDegree (1 / 3) (threshold 100 1) <;> omega

/-! ### The Nisan–Szegedy bounds -/

example {n : ℕ} (f : BooleanFunction n) :
    blockSensitivity f ≤ 2 * degree f ^ 2 ∧ blockSensitivity f ≤ 6 * approxDegree (1 / 3) f ^ 2 ∧
      blockSensitivity f ≤ 2 * sensitivity f ^ 4 :=
  ⟨blockSensitivity_le_two_mul_degree_sq f, blockSensitivity_le_six_mul_approxDegree_sq f,
    blockSensitivity_le_two_mul_sensitivity_pow_four f⟩

example {n : ℕ} (f : BooleanFunction n) :
    DecisionTree.complexity f ≤ 2 * degree f ^ 3 ∧
      DecisionTree.complexity f ≤ 216 * approxDegree (1 / 3) f ^ 6 :=
  ⟨DecisionTree.complexity_le_two_mul_degree_pow_three f,
    DecisionTree.complexity_le_mul_approxDegree_pow_six f⟩

/-- The bound at a general error: `(1 - 2ε) bs(f) ≤ 2 adeg_ε(f)²`, here at `ε = 1/4`. -/
example {n : ℕ} (f : BooleanFunction n) :
    (1 / 2 : ℝ) * blockSensitivity f ≤ 2 * approxDegree (1 / 4) f ^ 2 := by
  have := one_sub_two_mul_mul_blockSensitivity_le (by norm_num : (0 : ℝ) ≤ 1 / 4) f
  norm_num at this ⊢
  linarith

/-- Majority of three bits: `bs = 2 ≤ 2 deg² = 18`. -/
example : blockSensitivity (majority 3) ≤ 2 * degree (majority 3) ^ 2 :=
  blockSensitivity_le_two_mul_degree_sq _

end ComplexityTests.QueryComplexity.Approximate
