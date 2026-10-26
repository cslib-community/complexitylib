/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.Data.Code.Multilinearity
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic

/-!
# Tests: multilinearity testing

Over `ZMod 3` in two variables, the product `x 0 * x 1` is multilinear, so it evaluates the
multilinear extension of its values on the cube and passes the test with probability one. The
square `x 0 ^ 2` is not affine on any line in direction `0` and is affine on every line in
direction `1`, so the test rejects it with probability exactly `1 / 2`. Over `ZMod 5`, corrupting
the product at one point makes one line in each direction wrong, with five wrong points each, and
quantitative soundness then gives a multilinear function within `5 + 2 * 5 = 15` of the `25`
points.
-/

namespace ComplexityTests.Code.Multilinearity

open Cslib Cslib.Code Cslib.BitString Finset MvPolynomial

instance : Fact (Nat.Prime 3) := ⟨by decide⟩
instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The product of the two coordinates. -/
private def prod2 {F : Type*} [Field F] (x : Fin 2 → F) : F := x 0 * x 1

/-- The product of the coordinates is affine on every axis-parallel line. -/
private theorem isMultilinear_prod2 {F : Type*} [Field F] : IsMultilinear (prod2 (F := F)) := by
  intro x i
  obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  · have : lineRestrict prod2 x 0 = fun t => t * x 1 := by
      funext t
      simp [lineRestrict, prod2]
    rw [this]
    exact isAffineFun_id.mul_const _
  · have : lineRestrict prod2 x 1 = fun t => x 0 * t := by
      funext t
      simp [lineRestrict, prod2]
    rw [this]
    exact isAffineFun_id.const_mul _

-- The product evaluates the multilinear extension of its values on the cube.
example (x : Fin 2 → ZMod 3) :
    prod2 x = eval x (multilinearExtension fun b => prod2 (bitPoint b)) :=
  congrFun (isMultilinear_iff_eq_eval_multilinearExtension.mp isMultilinear_prod2) x

-- The product passes the test with probability one.
example : multilinearityTestRejection (prod2 (F := ZMod 3)) = 0 :=
  isMultilinear_prod2.multilinearityTestRejection_eq_zero

/-- The square of the first coordinate. -/
private def sq0 (x : Fin 2 → ZMod 3) : ZMod 3 := x 0 ^ 2

-- `t ↦ t ^ 2` is not affine over `ZMod 3`: it takes the values `0, 1, 1`.
example : ¬IsAffineFun fun t : ZMod 3 => t ^ 2 := by decide

-- Every point is wrong in direction `0` and none in direction `1`.
private theorem card_wrongPoints_sq0_zero : #(wrongPoints sq0 0) = 9 := by decide
private theorem card_wrongPoints_sq0_one : #(wrongPoints sq0 1) = 0 := by decide

-- The square is rejected with probability exactly one half.
example : multilinearityTestRejection sq0 = 1 / 2 := by
  rw [multilinearityTestRejection_eq, Fintype.expect_eq_sum_div_card, Fin.sum_univ_two,
    card_wrongPoints_sq0_zero, card_wrongPoints_sq0_one]
  simp only [Fintype.card_fin, Fintype.card_pi, ZMod.card, prod_const, card_univ]
  norm_num

-- So the square is not multilinear.
example : ¬IsMultilinear sq0 := fun h => by
  have := h.multilinearityTestRejection_eq_zero
  rw [multilinearityTestRejection_eq, Fintype.expect_eq_sum_div_card, Fin.sum_univ_two,
    card_wrongPoints_sq0_zero, card_wrongPoints_sq0_one] at this
  norm_num at this

/-- The product over `ZMod 5`, corrupted at the point `(4, 4)`. -/
private def corrupted (x : Fin 2 → ZMod 5) : ZMod 5 :=
  if x = ![4, 4] then 0 else x 0 * x 1

-- The five points of the row `x 1 = 4` are wrong in direction `0`, and the five points of the
-- column `x 0 = 4` in direction `1`.
private theorem card_wrongPoints_corrupted_zero : #(wrongPoints corrupted 0) = 5 := by decide
private theorem card_wrongPoints_corrupted_one : #(wrongPoints corrupted 1) = 5 := by decide

-- Quantitative soundness: some multilinear function differs from the corrupted product on at
-- most `15` of the `25` points.
example : ∃ g, IsMultilinear g ∧ hammingDist corrupted g ≤ 15 := by
  obtain ⟨g, hg, hd⟩ := exists_isMultilinear_hammingDist_le corrupted
  refine ⟨g, hg, hd.trans_eq ?_⟩
  rw [Fin.sum_univ_two, card_wrongPoints_corrupted_zero, card_wrongPoints_corrupted_one]
  rfl

end ComplexityTests.Code.Multilinearity
