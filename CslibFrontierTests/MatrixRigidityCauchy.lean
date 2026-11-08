/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Foundations.Combinatorics.KovariSosTuran
import CslibFrontier.Foundations.LinearAlgebra.Matrix.Rigidity.TotallyRegular
import Mathlib.Tactic.NormNum.Prime

/-!
# The Kővári–Sós–Turán bound and rigidity of Cauchy matrices

Checked instances:
* The Kővári–Sós–Turán bound is attained: three cells of a `2 × 2` grid contain no `2 × 2`
  rectangle, and the bound for `s = 2` allows exactly three.
* A derived bound: a `7 × 7` grid set without `2 × 2` rectangles has at most `22` cells (the true
  maximum, attained by the Fano plane, is `21`).
* Untouched rectangles: every `5` cells of a `4 × 4` grid miss some `2 × 2` rectangle.
* Every hypothesis of the totally regular rigidity bound holds for a rectangular `4 × 8` Cauchy
  matrix, and the bound is positive there.
* The `64 × 64` explicit Cauchy matrix over `ℚ` and over `ZMod 131` needs at least `438` changes to
  reach rank at most `6`, well above the trivial bound `64 - 6 = 58` from
  `Matrix.rank_sub_le_rigidity`. Here `64 ≤ 2 ^ 6`, but `log² 64 = 36 > 6`: the parameters lie in
  the range proved here and outside the `log² n ≤ r` stated in [Lokam2009], Theorem 2.5.
-/

namespace ComplexityTests.MatrixRigidityCauchy

open Finset Matrix

/-! ### The Kővári–Sós–Turán bound -/

/-- Three cells of the `2 × 2` grid. -/
def threeCells : Finset (Fin 2 × Fin 2) := {(0, 0), (0, 1), (1, 0)}

-- `threeCells` contains no `2 × 2` rectangle.
theorem threeCells_rectangleFree :
    ∀ I J : Finset (Fin 2), #I = 2 → #J = 2 → ¬ I ×ˢ J ⊆ threeCells := by
  decide

-- The bound for `s = 2` on a `2 × 2` grid allows at most three cells, so it is attained.
example : #threeCells = 3 ∧ ∀ S : Finset (Fin 2 × Fin 2),
    (∀ I J : Finset (Fin 2), #I = 2 → #J = 2 → ¬ I ×ˢ J ⊆ S) → #S ≤ 3 := by
  refine ⟨by decide, fun S hS => ?_⟩
  have h := Cslib.kovari_sos_turan S hS
  simp only [Fintype.card_fin] at h
  by_contra hc
  have h4 : 2 ^ 2 ≤ (#S - (2 - 1) * 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  omega

-- The hypothesis of the bound holds for `threeCells`, and the bound applies to it.
example : 2 * (#threeCells - (2 - 1) * 2) ^ 2 ≤ (2 - 1) * (2 * (2 + 1 - 2)) ^ 2 := by
  simpa using Cslib.kovari_sos_turan threeCells threeCells_rectangleFree

-- A `7 × 7` grid set without `2 × 2` rectangles has at most `22` cells.
example (S : Finset (Fin 7 × Fin 7))
    (hS : ∀ I J : Finset (Fin 7), #I = 2 → #J = 2 → ¬ I ×ˢ J ⊆ S) : #S ≤ 22 := by
  have h := Cslib.kovari_sos_turan S hS
  simp only [Fintype.card_fin] at h
  by_contra hc
  have h16 : 16 ^ 2 ≤ (#S - (2 - 1) * 7) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  omega

/-! ### Untouched rectangles -/

-- Every `5` cells of a `4 × 4` grid miss some `2 × 2` rectangle.
example (S : Finset (Fin 4 × Fin 4)) (hS : #S ≤ 5) :
    ∃ I J : Finset (Fin 4), #I = 2 ∧ #J = 2 ∧ Disjoint (I ×ˢ J) S := by
  refine Cslib.exists_disjoint_product_of_card_lt S (r := 1) (by simp) ?_
  have hL : Real.logb 2 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, Real.logb_rpow (by norm_num) (by norm_num)]
  have hS' : (#S : ℝ) ≤ 5 := by exact_mod_cast hS
  simp only [Fintype.card_fin, Nat.cast_ofNat, Nat.cast_one, div_one]
  rw [hL]
  norm_num
  linarith

/-! ### Rigidity of totally regular and Cauchy matrices -/

/-- A `4 × 8` Cauchy matrix over `ℚ`: the first four rows of `cauchyNat ℚ 8`. -/
noncomputable def cauchyRect : Matrix (Fin 4) (Fin 8) ℚ :=
  (cauchyNat ℚ 8).submatrix (Fin.castLE (by norm_num)) id

-- Every hypothesis of `IsTotallyRegular.le_rigidity` holds for `cauchyRect` at `r = 2`, and the
-- bound `8 (4 - 2) / 6 · log₂ 4 = 16 / 3` is positive: at least `6` changes are needed.
example : 6 ≤ cauchyRect.rigidity 2 := by
  have hA : cauchyRect.IsTotallyRegular :=
    (isTotallyRegular_cauchyNat 8).submatrix (Fin.castLE_injective _) Function.injective_id
  have h := hA.le_rigidity (r := 2) (by simp)
  have hL : Real.logb 2 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, Real.logb_rpow (by norm_num) (by norm_num)]
  simp only [Fintype.card_fin] at h
  norm_num [hL] at h
  have : (5 : ℝ) < cauchyRect.rigidity 2 := by linarith
  exact_mod_cast this

/-- `3 ≤ log₂ (64 / 6)`, since `2 ^ 3 = 8 ≤ 64 / 6`. -/
theorem three_le_logb : (3 : ℝ) ≤ Real.logb 2 (64 / 6) := by
  rw [Real.le_logb_iff_rpow_le (by norm_num) (by norm_num),
    show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  norm_num

-- The explicit `64 × 64` Cauchy matrix over `ℚ` needs at least `438` changes to reach rank `≤ 6`:
-- `64 ^ 2 / 28 · log₂ (64 / 6) ≥ 4096 · 3 / 28 > 438`.
example : 438 ≤ (cauchyNat ℚ 64).rigidity 6 := by
  have h := le_rigidity_cauchyNat (F := ℚ) (N := 64) (r := 6) (by norm_num) (by norm_num)
  have h3 := three_le_logb
  push_cast at h
  have : (438 : ℝ) ≤ (cauchyNat ℚ 64).rigidity 6 := by nlinarith
  exact_mod_cast this

instance : Fact (Nat.Prime 131) := ⟨by norm_num⟩

-- The same bound over the prime field `ZMod 131`, where `131 ≥ 2 · 64`.
example : 438 ≤ (cauchyNat (ZMod 131) 64).rigidity 6 := by
  have h := le_rigidity_cauchyNat_zmod (q := 131) (N := 64) (r := 6) (by norm_num) (by norm_num)
    (by norm_num)
  have h3 := three_le_logb
  push_cast at h
  have : (438 : ℝ) ≤ (cauchyNat (ZMod 131) 64).rigidity 6 := by nlinarith
  exact_mod_cast this

end ComplexityTests.MatrixRigidityCauchy
