/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Privacy.DifferentialPrivacy.Composition
import CslibFrontier.Privacy.DifferentialPrivacy.DiscreteLaplace
import CslibFrontier.Privacy.DifferentialPrivacy.RandomizedResponse
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Differential privacy: instances, non-instances and clients

* A constant mechanism is `(0, 0)`-private; releasing the input bit is `(ε, δ)`-private for no
  `ε` when `δ < 1`, so the definition is not vacuous in either direction.
* Randomized response: its masses, failure of `(1, 0)`-privacy (`1 < ln 3`), group privacy of the
  survey at Hamming distance two, and `k`-fold composition of the survey.
* Hamming adjacency on concrete datasets, in both directions.
* The count query `x ↦ #{i | x i}` has sensitivity one for Hamming adjacency, so the geometric
  and discrete Laplace mechanisms make it private.
* The two-sided geometric distribution with ratio `1/2`: the mass of `0` is `1/3`, and the
  two-sided tail at `1` is `2/3 = 1 - 1/3`, consistent with the mass of `0`.
-/

namespace CslibFrontierTests.Privacy.DifferentialPrivacy

open Cslib Cslib.Privacy
open scoped ENNReal

/-! ### The definition is not vacuous -/

/-- A mechanism ignoring its input is `(0, 0)`-private for every adjacency relation. -/
example {D R : Type} (Adj : D → D → Prop) (p : PMF R) :
    DifferentiallyPrivate Adj (fun _ => p) 0 0 :=
  DifferentiallyPrivate.of_apply_le fun _ _ _ r => by simp

/-- Releasing the input bit is `(ε, δ)`-private for no `ε` when `δ < 1`. -/
example (ε : ℝ) {δ : ℝ≥0∞} (hδ : δ < 1) :
    ¬ DifferentiallyPrivate (fun _ _ => True) (fun b : Bool => PMF.pure b) ε δ := by
  intro h
  have := h (x := true) (y := false) trivial {true}
  simp only [PMF.toOuterMeasure_pure_apply, Set.mem_singleton_iff, ite_true, Bool.false_eq_true,
    ite_false, mul_zero, zero_add] at this
  exact absurd hδ (not_lt.mpr this)

/-! ### Randomized response -/

example : ProbComp.eval (randomizedResponse true) true = 3 / 4 := by
  rw [eval_randomizedResponse_apply]; rfl

example : ProbComp.eval (randomizedResponse true) false = 1 / 4 := by
  rw [eval_randomizedResponse_apply]; rfl

/-- Randomized response is not `(1, 0)`-private, since `1 < ln 3`. -/
example :
    ¬ DifferentiallyPrivate (fun _ _ => True)
      (fun truth => ProbComp.eval (randomizedResponse truth)) 1 0 := by
  rw [differentiallyPrivate_randomizedResponse_iff, not_le, Real.lt_log_iff_exp_lt (by norm_num)]
  exact Real.exp_one_lt_three

/-- Group privacy: the survey is `(2 ln 3, 0)`-private for datasets differing in two rows. -/
example (n : ℕ) :
    DifferentiallyPrivate (fun x y : Fin n → Bool => hammingDist x y ≤ 2)
      (fun x => ProbComp.eval (randomizedResponseSurvey x)) (2 * Real.log 3) 0 := by
  exact_mod_cast (differentiallyPrivate_randomizedResponseSurvey n).hammingDist_le_of_pure 2

/-- Running the survey `k` times, non-adaptively, is `(k ln 3, 0)`-private. -/
example (n k : ℕ) :
    DifferentiallyPrivate HammingAdjacent
      (adaptiveComposition (fun _ x => ProbComp.eval (randomizedResponseSurvey (n := n) x)) k)
      (k * Real.log 3) 0 := by
  have := DifferentiallyPrivate.adaptiveComposition (ε := fun _ => Real.log 3) (δ := fun _ => 0)
    (M := fun (_ : List (Fin n → Bool)) x => ProbComp.eval (randomizedResponseSurvey x))
    (fun _ => differentiallyPrivate_randomizedResponseSurvey n) k
  simpa using this

/-- The expected number of "Yes" answers when one of two respondents has true answer "Yes". -/
example :
    ∑ answers, (ProbComp.eval (randomizedResponseSurvey ![true, false]) answers).toReal *
        (Finset.univ.filter fun i => answers i = true).card = 1 := by
  have hcard : (Finset.univ.filter fun i => (![true, false] : Fin 2 → Bool) i = true).card = 1 := by
    decide
  rw [sum_eval_randomizedResponseSurvey_mul_card, hcard]
  norm_num

/-! ### Hamming adjacency -/

example : HammingAdjacent ![0, 1, 2] ![0, 5, 2] := by
  rw [hammingAdjacent_iff_hammingDist_le_one]; decide

example : ¬ HammingAdjacent ![0, 1] ![1, 0] := by
  rw [hammingAdjacent_iff_hammingDist_le_one]; decide

/-! ### Count queries under the geometric and discrete Laplace mechanisms -/

/-- The number of `true` rows. -/
def countTrue {n : ℕ} (x : Fin n → Bool) : ℤ := ∑ j, if x j = true then 1 else 0

/-- The count query has sensitivity one for Hamming adjacency. -/
theorem abs_countTrue_sub_le {n : ℕ} {x y : Fin n → Bool} (h : HammingAdjacent x y) :
    |((countTrue x : ℝ)) - countTrue y| ≤ 1 := by
  by_cases hxy : x = y
  · subst hxy; simp
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hxy
  have key (j : Fin n) (hj : j ≠ i) : x j = y j := by
    by_contra hne
    exact hj (h hne hi)
  have hdiff : (countTrue x : ℝ) - countTrue y =
      (if x i = true then 1 else 0) - (if y i = true then 1 else 0) := by
    simp only [countTrue, Int.cast_sum, Int.cast_ite, Int.cast_one, Int.cast_zero]
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i]
    · intro j _ hj
      rw [key j hj, sub_self]
    · simp
  rw [hdiff]
  cases x i <;> cases y i <;> norm_num

/-- The `α`-geometric mechanism on the count query is `(ln α⁻¹, 0)`-private. -/
example {n : ℕ} {α : ℝ} (h0 : 0 < α) (h1 : α < 1) :
    DifferentiallyPrivate HammingAdjacent
      (addNoise (countTrue (n := n)) (twoSidedGeometric α h0.le h1)) (Real.log α⁻¹) 0 := by
  simpa using differentiallyPrivate_addNoise_twoSidedGeometric (Δ := 1)
    (fun _ _ h => abs_countTrue_sub_le h) h0 h1

/-- Discrete Laplace noise of scale `1 / ε` makes the count query `(ε, 0)`-private. -/
example {n : ℕ} {ε : ℝ} (hε : 0 < ε) :
    DifferentiallyPrivate HammingAdjacent
      (addNoise (countTrue (n := n)) (discreteLaplace (1 / ε) (by positivity))) ε 0 :=
  differentiallyPrivate_addNoise_discreteLaplace one_pos (fun _ _ h => abs_countTrue_sub_le h) hε

/-! ### The two-sided geometric distribution with ratio `1/2` -/

example : twoSidedGeometric (1 / 2) (by norm_num) (by norm_num) 0 = ENNReal.ofReal (1 / 3) := by
  rw [twoSidedGeometric_apply]; norm_num

example :
    (twoSidedGeometric (1 / 2) (by norm_num) (by norm_num)).toOuterMeasure {z | 1 ≤ z.natAbs} =
      ENNReal.ofReal (2 / 3) := by
  rw [twoSidedGeometric_toOuterMeasure_le_natAbs _ _ one_ne_zero]; norm_num

example :
    (twoSidedGeometric (1 / 2) (by norm_num) (by norm_num)).toOuterMeasure (Set.Ici 0) =
      ENNReal.ofReal (2 / 3) := by
  rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, twoSidedGeometric_toOuterMeasure_Ici]; norm_num

end CslibFrontierTests.Privacy.DifferentialPrivacy
