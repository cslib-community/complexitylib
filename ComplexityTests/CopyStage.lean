/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
import Complexity.Foundations.LinearAlgebra.Matrix.CopyStage

/-!
# Tests for one stage of the correction-and-copy hierarchy
-/

namespace ComplexityTests.CopyStage

open Finset Matrix

/-- A walk on three time layers: from `0` to `1` and from `1` to `2`, each with probability
`1 / 2`. Its entries are at most `f = 1 / 2`. -/
private noncomputable def C : Matrix (Fin 3) (Fin 3) ℝ := !![0, 1 / 2, 0; 0, 0, 1 / 2; 0, 0, 0]

/-- The hard cutoff `t ↦ max (t - θ f) 0` with `θ = 1 / 4`, `f = 1 / 2`. -/
private noncomputable def φ : Fin 3 → ℝ → ℝ := fun _ t => max (t - 1 / 8) 0

private theorem hC : C.IsStrictUpperTriangular := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [C]

private theorem hC0 : ∀ x y, 0 ≤ C x y := by
  intro x y; fin_cases x <;> fin_cases y <;> norm_num [C]

private theorem hCf : ∀ x y, C x y ≤ 1 / 2 := by
  intro x y; fin_cases x <;> fin_cases y <;> norm_num [C]

private theorem hC1 : C *ᵥ 1 ≤ 1 := by
  intro x; fin_cases x <;> norm_num [C, mulVec, dotProduct, Fin.sum_univ_three]

private theorem hφ0 : ∀ y t, 0 ≤ φ y t := fun _ _ => le_max_right _ _

private theorem hφθ : ∀ y t, φ y t ≤ max (t - 1 / 4 * (1 / 2)) 0 := fun _ t => by
  norm_num [φ]

private theorem hφm : ∀ y, Monotone (φ y) := fun _ _ _ h => max_le_max (by linarith) le_rfl

private theorem hφL : ∀ y s t, s ≤ t → φ y t - φ y s ≤ 1 * (t - s) := fun _ s t _ => by
  simp only [φ, one_mul]
  have := le_max_left (s - 1 / 8) 0
  have := le_max_right (s - 1 / 8) 0
  have : max (t - 1 / 8) 0 ≤ max (s - 1 / 8) 0 + (t - s) := max_le (by linarith) (by linarith)
  linarith

/-! ### Residual bounds -/

-- One iteration corrects each transition to `1 / 8`, so the row sums are at most one.
example (x : Fin 3) : ∑ y, cutoffCorrectionIter φ C 1 x y ≤ 1 := by
  exact_mod_cast cutoffCorrectionIter_sum_le hC0 hφ0 hφθ (by norm_num) hC1 1 x

example (k : ℕ) (x y : Fin 3) :
    (C - cutoffCorrectionIter φ C k + cutoffCorrectionIter φ C k * C) x y ≤ (k + 1) * (1 / 2) :=
  cutoffCorrection_residual_le_mul hC0 hφ0 hφθ (by norm_num) hCf (by norm_num) hC1 k x y

-- The residual of the first iterate dominates `θ / 2 = 1 / 8` times its unsigned terms.
example (x y : Fin 3) :
    1 / 4 / (2 * ((0 : ℕ) + 1)) * (C + cutoffCorrectionIter φ C 1 +
        cutoffCorrectionIter φ C 1 * C) x y ≤
      (C - cutoffCorrectionIter φ C 1 + cutoffCorrectionIter φ C 1 * C) x y :=
  cutoffCorrection_residual_dominates hC0 hφ0 hφθ (by norm_num) hCf (by norm_num) hC1 hφm
    (by norm_num) (by norm_num) 0 x y

/-! ### Copy fractions -/

/-- A ramp from `0` at `t ≤ 0` to `1` at `t ≥ 1 / 4`. -/
private noncomputable def χ (t : ℝ) : ℝ := min (max (4 * t) 0) 1

private theorem χ0 : ∀ t, 0 ≤ χ t := fun _ => le_min (le_max_right _ _) zero_le_one
private theorem χ1 : ∀ t, χ t ≤ 1 := fun _ => min_le_right _ _
private theorem χ₀ : ∀ t, t ≤ 0 → χ t = 0 := fun t h => by
  simp only [χ]; rw [max_eq_right (by linarith)]; norm_num
private theorem χ₁ : ∀ t, 1 / 4 ≤ t → χ t = 1 := fun t h => by
  simp only [χ]; rw [max_eq_left (by linarith)]; exact min_eq_right (by linarith)

-- A large entry is split evenly between two copies; a small one stays with the primary copy.
example : copyFraction χ 1 (1 / 2) 1 = 1 / 2 := by
  rw [copyFraction_of_eq_one (χ₁ _ (by norm_num))]; norm_num

example (j : Fin 2) : copyFraction χ 1 0 j = if j = 0 then 1 else 0 :=
  copyFraction_of_eq_zero (χ₀ 0 le_rfl) j

/-! ### One stage

Without correction (`k = 0`, so `D = C`) and with every vertex overloaded and both of its copies
active, the stage halves the entries `1 / 2` of `C` and at most doubles the support. -/

private def r : Fin 2 → Fin 3 → ℝ := fun _ _ => 1

-- The split entry from the primary copy of `0` to the second copy of `1` is `1 / 4`.
example : copyStage χ 1 r (C - cutoffCorrectionIter φ C 0 + cutoffCorrectionIter φ C 0 * C)
    ((0 : Fin 3), (0 : Fin 2)) ((1 : Fin 3), (1 : Fin 2)) = 1 / 4 := by
  simp only [copyStage, copySplit, of_apply, cutoffCorrectionIter, Function.iterate_zero, id,
    sub_zero, Matrix.zero_mul, add_zero]
  rw [copyFraction_of_eq_one (χ₁ _ (by norm_num [C]))]
  norm_num [r, C]

private theorem stage :
    let D := C - cutoffCorrectionIter φ C 0 + cutoffCorrectionIter φ C 0 * C
    (∀ a b, copyStage χ 1 r D a b ≤ 1 / 2 / 2) ∧
      copyStage χ 1 r D * copyWeight r = copyWeight r * D ∧
      (∀ a b, copyStage χ 1 r D a b ≠ 0 → a ∈ copyCover univ univ ∧ b ∈ copyCover univ univ) ∧
      #(copyCover (m := 1) (univ : Finset (Fin 3)) univ) ≤ 2 * #(univ : Finset (Fin 3)) :=
  copyStage_rates (m := 1) (q := 2) (L := 1) (θ := 1 / 4) hC hC0 hCf hC1
    hφ0 hφθ hφm hφL (by norm_num) (by norm_num) (by norm_num) 0
    (fun _ _ _ => ⟨mem_univ _, mem_univ _⟩) (fun _ => rfl)
    (fun _ _ => by norm_num [r]) (fun _ _ _ _ => mem_univ _)
    (θ₂ := -(Real.exp (1 / (1 / 4)) * (1 / (1 / 4)) ^ 0 / Nat.factorial 0))
    (fun _ => Or.inr ⟨fun _ => rfl, mem_univ _⟩) (τ₀ := 0) (le_of_eq (by ring)) χ0 χ1 χ₀
    (τ₁ := 1 / 4) χ₁ (by norm_num) (by norm_num) (by simp)

-- Every entry of the stage is at most `f / q = 1 / 4`, and at most `6` copies are active.
example : ∀ a b, copyStage χ 1 r (C - cutoffCorrectionIter φ C 0 +
    cutoffCorrectionIter φ C 0 * C) a b ≤ 1 / 2 / 2 := stage.1

example : #(copyCover (m := 1) (univ : Finset (Fin 3)) univ) ≤ 6 := stage.2.2.2

/-! ### Chaining stages -/

-- The stage output, indexed by the lexicographically ordered copies, is again strictly upper
-- triangular, so it can be the input `C` of the next stage.
example : ((copyStage χ 1 r (C - cutoffCorrectionIter φ C 0 +
    cutoffCorrectionIter φ C 0 * C)).submatrix ofLex ofLex).IsStrictUpperTriangular :=
  copyStage_isStrictUpperTriangular
    (cutoffCorrection_residual_isStrictUpperTriangular hφ0 hφθ (by norm_num) hC 0)

-- Concretely, the copy `(1, 1)` of the middle vertex comes after both copies of vertex `0`, so
-- the entries from it back to them vanish.
example (i : Fin 2) : (copyStage χ 1 r (C - cutoffCorrectionIter φ C 0 +
    cutoffCorrectionIter φ C 0 * C)) (1, 1) (0, i) = 0 :=
  copyStage_isStrictUpperTriangular (V := Fin 3)
    (cutoffCorrection_residual_isStrictUpperTriangular hφ0 hφθ (by norm_num) hC 0)
    (i := toLex (1, 1)) (j := toLex (0, i)) (by simp [Prod.Lex.lt_iff])

/-! ### Incidence counting -/

-- In the walk, both targets `1` and `2` have an entry `1 / 2 > 1 / 4`, so
-- `2 · 1 · (1 / 4) ≤ |rows| · 1` with the two nonzero rows `{0, 1}`.
example :
    ((#({1, 2} : Finset (Fin 3)) * 1 : ℕ) : ℝ) * (1 / 4) ≤ #({0, 1} : Finset (Fin 3)) * 1 := by
  have h := card_mul_le_of_incidences (k := 1) (fun _ => C) (fun _ => hC0) (fun _ => 1)
    (fun _ x => by fin_cases x <;> norm_num [C, Fin.sum_univ_three]) {0, 1}
    (fun _ x y hxy => by fin_cases x <;> fin_cases y <;> simp_all [C]) (δ := 1 / 4)
    (by norm_num) {1, 2} (N := 1) (fun y hy => ⟨0, by
      simp only [mem_insert, mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact card_pos.mpr ⟨0, by norm_num [C]⟩
      · exact card_pos.mpr ⟨1, by norm_num [C]⟩⟩)
  simpa using h

end ComplexityTests.CopyStage
