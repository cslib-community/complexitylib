/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Statistics.LeastSquares.PolynomialDecision
import ComplexityTests.PaperEndpoints.RoundingExecution
import Mathlib.Tactic

/-! Finite rational isolation and a nonvacuous least-squares output bridge.
The sign formula and separation are supplied explicitly in this scalar example;
no general elimination backend or paper-wide exact-output claim is tested. -/

open Cslib.Polynomial.ThresholdIsolation Cslib.LeastSquares
open Cslib.Algorithms.Lean Matrix Set

namespace ComplexityTests.ExactOutput1326

private def sqrtQuery (r : ℚ) : TimeM ℕ Bool := ⟨decide (0 ≤ r ∧ 2 ≤ r * r), 1⟩

-- Actual rational execution, with the exact count and an irrational boundary.
example : (bisect sqrtQuery 4 1 2).ret = (11/8, 23/16) ∧
    (bisect sqrtQuery 4 1 2).time = 16 := by decide +kernel

private theorem sqrtQuery_correct (r : ℚ) :
    (sqrtQuery r).ret = true ↔ Real.sqrt 2 ≤ (r : ℝ) := by
  simp only [sqrtQuery, decide_eq_true_eq]
  rw [Real.sqrt_le_iff]
  norm_cast
  simp only [pow_two]

example : (isolate (Polynomial.X ^ 2 - 2) sqrtQuery 4 1 2).ret.Represents (Real.sqrt 2) := by
  apply isolate_represents _ (by
    intro h
    have he := congrArg (Polynomial.eval (0 : ℚ)) h
    norm_num at he) sqrtQuery (Real.sqrt 2) 2
    (by norm_num [Polynomial.IsRoot]) ?_ 4 1 2
    (fun r _ => sqrtQuery_correct r) (by norm_num) (by norm_num) (by norm_num)
  intro a b ha hb hab
  norm_num [Polynomial.IsRoot] at ha hb
  have hfactor : (a - b) * (a + b) = 0 := by nlinarith
  have hsum : a + b = 0 := (mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr hab)
  have hsq : 4 ≤ (a - b) ^ 2 := by nlinarith
  have hsq' := sq_abs (a - b)
  nlinarith [abs_nonneg (a - b)]

-- The zero polynomial never represents an exact isolated root.
example (l u : ℚ) (s : ℝ) : ¬ (⟨0, l, u⟩ : RootInterval).Represents s := by
  intro h
  exact h.1 rfl

public def x : Fin 4 → Fin 1 → ℚ := fun _ _ => 1
public def y : Fin 4 → ℚ := ![-1, -1, -1, 6]
private noncomputable def weights : Fin 4 → ℝ := ![1, 1, 1, 1/2]
public noncomputable def p (_ : Fin 1) : Polynomial ℚ := Polynomial.C (1/2) - Polynomial.X
public def query (r : ℚ) : TimeM ℕ Bool := ⟨decide (1/2 ≤ r), 1⟩

private theorem gp : GeneralPosition (fun i j => (x i j : ℝ)) :=
  by simpa only [x, Rat.cast_one] using RoundingExecution.design_generalPosition

private theorem input_feasible : Feasible (fun i j => (x i j : ℝ))
    (fun i => (y i : ℝ)) (fun _ => 1) 0 weights := by
  have hbox : ∀ i, weights i ∈ Icc (0 : ℝ) 1 := by
    intro i; fin_cases i <;> norm_num [weights]
  have hG := gp.weightedGram_posDef _ weights hbox (by norm_num [weights, Fin.sum_univ_four])
  refine ⟨hbox, hG, ?_⟩
  rw [weightedEstimate_eq_of_normal _ _ weights (fun _ => 0) hG (by
    ext j; fin_cases j
    norm_num [weights, x, y, dotProduct, Fin.sum_univ_one, Fin.sum_univ_four])]
  simp

private theorem full_violation : (0 : ℝ) < (fun _ : Fin 1 => (1 : ℝ)) ⬝ᵥ
    weightedEstimate 0 0 Finset.univ (fun i j => (x i j : ℝ))
      (fun i => (y i : ℝ)) (fun _ => 1) := by
  have hG := gp.weightedGram_posDef _ (fun _ => 1) (by simp) (by norm_num [Fin.sum_univ_four])
  rw [weightedEstimate_eq_of_normal _ _ (fun _ => 1) (fun _ => 3/4) hG (by
    ext j; fin_cases j
    norm_num [x, y, dotProduct, Fin.sum_univ_one, Fin.sum_univ_four])]
  norm_num [dotProduct, Fin.sum_univ_one]

private theorem normal_iff (r : ℝ) : EqualityNormalDecision
    (fun i j => (x i j : ℝ)) (fun i => (y i : ℝ)) (fun _ => 1) 0 r ↔ 1/2 ≤ r := by
  constructor
  · rintro ⟨v, b, hv, hn, hb, hr⟩
    have hb0 : b 0 = 0 := by simpa [dotProduct, Fin.sum_univ_one] using hb
    have heq := congrFun hn 0
    norm_num [x, y, dotProduct, Fin.sum_univ_one, Fin.sum_univ_four, hb0] at heq
    norm_num [Fin.sum_univ_four] at hr
    linarith [(hv 0).2, (hv 1).2, (hv 2).2]
  · intro hr
    refine ⟨weights, 0, input_feasible.1, ?_, by simp, ?_⟩
    · ext j; fin_cases j
      norm_num [x, y, weights, dotProduct, Fin.sum_univ_one, Fin.sum_univ_four]
    · norm_num [weights, Fin.sum_univ_four]
      exact hr

private theorem optimum : fractionalStability (fun i j => (x i j : ℝ))
    (fun i => (y i : ℝ)) (fun _ => 1) 0 = 1/2 := by
  have hu := fractionalStability_le _ _ _ _ weights input_feasible
  norm_num [weights, Fin.sum_univ_four] at hu
  have hi := (equalityNormalDecision_iff _ gp _ _ _ weights input_feasible
    (by norm_num [weights, Fin.sum_univ_four]) full_violation
    (fractionalStability (fun i j => (x i j : ℝ)) (fun i => (y i : ℝ)) (fun _ => 1) 0)
    (by simpa using hu.trans (by norm_num : (1/2 : ℝ) ≤ 4 - 1))).mpr le_rfl
  exact le_antisymm hu ((normal_iff _).mp hi)

-- The bridge takes actual normal decisions and a polynomial sign description;
-- its inputs include no optimizer-returning oracle.
public theorem exact_fractional_output : (isolate (∏ i : Fin 1, p i) query 2 0 1).ret.Represents
    (fractionalStability (fun i j => (x i j : ℝ)) (fun i => (y i : ℝ)) (fun _ => 1) 0) := by
  simpa only [Rat.cast_one, Rat.cast_zero] using
    (PolynomialDecision.isolate_fractional_of_sign_description x gp y
      (fun _ => 1) 0 weights (by simpa using input_feasible)
      (by norm_num [weights, Fin.sum_univ_four]) (by simpa using full_violation) p
      (by intro i h; have he := congrArg (Polynomial.eval (0 : ℚ)) h; norm_num [p] at he)
      (fun bits => bits 0) 0 1
      (by simpa only [Rat.cast_one, Rat.cast_zero, optimum] using
        (show (0 : ℝ) < 1/2 by norm_num))
      (by simpa only [Rat.cast_one, Rat.cast_zero, optimum] using
        (show (1/2 : ℝ) ≤ 1 by norm_num)) (by norm_num)
      (by
        intro r _
        simp only [Rat.cast_one, Rat.cast_zero]
        rw [normal_iff]
        norm_num [p]) query
      (by
        intro r _
        simp only [Rat.cast_one, Rat.cast_zero]
        rw [normal_iff]
        simp only [query, decide_eq_true_eq]
        have hhalf : ((1/2 : ℚ) : ℝ) = 1/2 := by norm_num
        rw [← hhalf]
        exact Rat.cast_le.symm) 1
      (by
        intro a b ha hb hab
        norm_num [p, Fin.prod_univ_one, Polynomial.IsRoot] at ha hb
        exact (hab (by linarith)).elim) 2 (by norm_num))

example : (isolate (∏ i : Fin 1, p i) query 2 0 1).ret.lower = 1/4 ∧
    (isolate (∏ i : Fin 1, p i) query 2 0 1).ret.upper = 1/2 ∧
    (isolate (∏ i : Fin 1, p i) query 2 0 1).time = 8 := by decide +kernel

end ComplexityTests.ExactOutput1326
