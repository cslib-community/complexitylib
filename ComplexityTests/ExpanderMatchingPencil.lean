/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.Combinatorics.Expander.MatchingPaths
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.FinCases

/-!
# Matching-pencil certificates on a four-vertex core

The matrices below are the Laplacian and signless Laplacian of `K₄` with the edge `0--1`
deleted. Vertices zero and one are the matching endpoints; the other two have degree three.
The checked inequalities give Laplacian gap at least two and signless gap at least one half.
Both pencil branches are then nonsingular for an explicit perturbation budget.
The final client uses actual length-ten path parameters over a nonempty interval of angles.
-/

namespace ComplexityTests.ExpanderMatchingPencil

open Matrix Cslib.MatchingPencil

private def coreL : Matrix (Fin 4) (Fin 4) ℝ :=
  !![2, 0, -1, -1; 0, 2, -1, -1; -1, -1, 3, -1; -1, -1, -1, 3]

private def coreW : Fin 4 → ℝ := ![1, 1, 0, 0]

private def pairing : Equiv.Perm (Fin 4) := Equiv.swap 0 1

private theorem coreL_symm : coreL.IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [coreL]

private theorem coreL_one : coreL *ᵥ (1 : Fin 4 → ℝ) = 0 := by
  ext i
  fin_cases i <;> norm_num [coreL, mulVec, dotProduct, Fin.sum_univ_succ]

private theorem coreL_gap (x : Fin 4 → ℝ) (hx : (1 : Fin 4 → ℝ) ⬝ᵥ x = 0) :
    2 * (x ⬝ᵥ x) ≤ x ⬝ᵥ coreL *ᵥ x := by
  have hx3 : x 3 = -x 0 - x 1 - x 2 := by
    norm_num [dotProduct, Fin.sum_univ_succ] at hx
    linarith
  norm_num [coreL, dotProduct, mulVec, Fin.sum_univ_succ]
  rw [hx3]
  nlinarith [sq_nonneg (x 2 - (-x 0 - x 1 - x 2)), sq_nonneg (x 0 + x 1)]

private theorem weight_bounds (v : Fin 4) : 0 ≤ coreW v ∧ coreW v ≤ 1 := by
  fin_cases v <;> norm_num [coreW]

private theorem pairing_involutive : Function.Involutive pairing := by
  intro v
  simp [pairing]

private theorem pairing_weight (v : Fin 4) : coreW (pairing v) = coreW v := by
  fin_cases v <;> norm_num [coreW, pairing, Equiv.swap_apply_def]

-- The positive branch has one negative direction and is positive on the mean-zero hyperplane.
example : Function.Injective (pencil coreL coreW pairing (1 / 16) 0 (-1) (1 / 64)).mulVec := by
  apply laplacianPencil_injective coreL_symm coreL_one coreW pairing pairing_involutive
    (fun v => (weight_bounds v).1) (fun v => (weight_bounds v).2) pairing_weight
    (by norm_num [coreW, Fin.sum_univ_succ]) coreL_gap
  all_goals norm_num

private def coreQ : Matrix (Fin 4) (Fin 4) ℝ :=
  !![2, 0, 1, 1; 0, 2, 1, 1; 1, 1, 3, 1; 1, 1, 1, 3]

-- The two core matrices come from the same degree matrix, as required for a signless branch.
private theorem coreQ_eq : coreQ = (2 : ℝ) • coreDegree coreW - coreL := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [coreQ, coreDegree, coreW, coreL, diagonal]

private theorem coreQ_gap (x : Fin 4 → ℝ) :
    (1 / 2) * (x ⬝ᵥ x) ≤ x ⬝ᵥ coreQ *ᵥ x := by
  norm_num [coreQ, dotProduct, mulVec, Fin.sum_univ_succ]
  nlinarith [sq_nonneg (3 * (x 0 + x 1) + 4 * (x 2 + x 3)),
    sq_nonneg (x 2 + x 3), sq_nonneg (x 0 - x 1), sq_nonneg (x 2 - x 3)]

-- Both parities of a path are accepted by the same signless gap certificate.
example (s : ℝ) (hs : |s| ≤ 1) :
    Function.Injective (pencil coreQ coreW pairing (1 / 16) 0 s (1 / 64)).mulVec := by
  apply signlessPencil_injective coreQ coreW pairing (fun v => (weight_bounds v).1)
    (fun v => (weight_bounds v).2) pairing_weight coreQ_gap
  · norm_num
  · norm_num
  · exact hs
  · norm_num
  · norm_num

private theorem lengthTen_budget :
    2 * (Real.pi / 2) / (10 * Real.sin (Real.pi / 2)) +
        3 * (Real.pi / 2) ^ 2 / (2 * 10 ^ 2) < min (2 : ℝ) (1 / 2) := by
  have hpi2 : Real.pi ^ 2 < 16 := by
    nlinarith [Real.pi_pos, Real.pi_lt_four,
      mul_pos Real.pi_pos (sub_pos.mpr Real.pi_lt_four)]
  norm_num [Real.sin_pi_div_two]
  nlinarith [Real.pi_lt_four]

-- The allowed angle interval is nonempty; these parameters describe actual sine recurrences.
example : 0 < Real.pi / 20 ∧ 10 * (Real.pi / 20) ≤ Real.pi / 2 := by
  constructor
  · positivity
  · linarith

-- No mode exists near either spectral endpoint for this concrete core and length-ten paths.
example {θ r : ℝ} (hθ : 0 < θ) (hθmax : θ ≤ Real.pi / 20)
    (hr : r = Real.cos θ ∨ r = -Real.cos θ) (f : Fin 4 → ℝ) (x : Fin 4 → ℕ → ℝ)
    (hrec : ∀ v, Cslib.ExpanderPath.Recurrence 10 r (x v))
    (hstart : ∀ v, x v 0 = f v) (hend : ∀ v, x v 10 = f (pairing v))
    (hcore : ∀ v, ((coreDegree coreW - coreL) *ᵥ f) v + coreW v * x v 1 =
      3 * r * f v) :
    f = 0 ∧ ∀ v j, j ≤ 10 → x v j = 0 := by
  apply Cslib.matchingPath_mode_eq_zero_of_uniform_budget coreL_symm coreL_one coreW pairing
    pairing_involutive (fun v => (weight_bounds v).1) (fun v => (weight_bounds v).2)
    pairing_weight (by norm_num [coreW, Fin.sum_univ_succ]) (by decide) hθ
    (τ := Real.pi / 2) (by norm_num; linarith)
    (by linarith [Real.pi_pos]) coreL_gap _ lengthTen_budget hr f x hrec hstart hend hcore
  intro z
  rw [← coreQ_eq]
  exact coreQ_gap z

-- The exact negative endpoint is checked through affine interpolation, without a sine division.
example (f : Fin 4 → ℝ) (x : Fin 4 → ℕ → ℝ)
    (hrec : ∀ v, Cslib.ExpanderPath.Recurrence 10 (-1) (x v))
    (hstart : ∀ v, x v 0 = f v) (hend : ∀ v, x v 10 = f (pairing v))
    (hcore : ∀ v, ((coreDegree coreW - coreL) *ᵥ f) v + coreW v * x v 1 = -3 * f v) :
    f = 0 ∧ ∀ v j, j ≤ 10 → x v j = 0 := by
  apply Cslib.matchingPath_neg_one_mode_eq_zero coreL coreW pairing
    (fun v => (weight_bounds v).1) (fun v => (weight_bounds v).2) pairing_weight
    (ν := 1 / 2) (by decide) _ (by norm_num) f x hrec hstart hend hcore
  intro z
  rw [← coreQ_eq]
  exact coreQ_gap z

end ComplexityTests.ExpanderMatchingPencil
