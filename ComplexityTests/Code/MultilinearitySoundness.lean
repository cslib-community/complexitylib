/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.Data.Code.MultilinearitySoundness
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic

/-!
# Tests: polynomial soundness of the multilinearity test

Self-improvement applies to the product over `ZMod 5` corrupted at one point: the product is a
multilinear function within one point, and the lemma bounds the distance by
`5 * (5 + 5) + 2 * 2 ^ 2 * 5 = 90`. The hypotheses of the soundness theorem are satisfiable: over
`ZMod 41` (with `41 ≥ 40 * 1 ^ 2`) in one variable, a coordinate function has no wrong lines, and
the theorem applies with `ε = 1 / 800`.
-/

namespace ComplexityTests.Code.MultilinearitySoundness

open Cslib Cslib.Code Finset

instance : Fact (Nat.Prime 5) := ⟨by decide⟩
instance : Fact (Nat.Prime 41) := ⟨by decide⟩

/-- The product over `ZMod 5`, corrupted at the point `(4, 4)`. -/
private def corrupted (x : Fin 2 → ZMod 5) : ZMod 5 :=
  if x = ![4, 4] then 0 else x 0 * x 1

/-- The product of the two coordinates. -/
private def prod2 (x : Fin 2 → ZMod 5) : ZMod 5 := x 0 * x 1

private theorem isMultilinear_prod2 : IsMultilinear prod2 := by
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

private theorem hammingDist_corrupted : hammingDist corrupted prod2 = 1 := by decide

private theorem card_wrongPoints_corrupted (i : Fin 2) : #(wrongPoints corrupted i) = 5 := by
  fin_cases i <;> decide

-- Self-improvement for the corrupted product: the hypothesis `2 * 1 ≤ 25` holds, and the bound is
-- `90`.
example : hammingDist corrupted prod2 ≤ 90 := by
  have h := isMultilinear_prod2.hammingDist_le_of_two_mul_le (f := corrupted)
    (by rw [hammingDist_corrupted]; decide)
  simp only [Fin.sum_univ_two, card_wrongPoints_corrupted, ZMod.card] at h
  simpa using h

/-- A coordinate function in one variable over `ZMod 41`. -/
private def coord (x : Fin 1 → ZMod 41) : ZMod 41 := x 0

-- The hypotheses of the soundness theorem hold for it, with `ε = 1 / 800`.
example : ∃ g, IsMultilinear g ∧ (hammingDist coord g : ℝ) <
    3 * 1 ^ 2 * (1 / 800 + 1 / 41) * 41 ^ 1 := by
  have hcoord : IsMultilinear coord := by
    intro x i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    have : lineRestrict coord x 0 = fun t => t := by
      funext t
      simp [lineRestrict, coord]
    rw [this]
    exact isAffineFun_id
  have hW (i : Fin 1) : wrongPoints coord i = ∅ := by
    ext x
    simp [wrongPoints, hcoord x i]
  have := exists_isMultilinear_hammingDist_lt coord (ε := 1 / 800) (by norm_num)
    (by simp [ZMod.card]) (by norm_num) fun i => by simp [hW, ZMod.card]
  simpa [ZMod.card] using this

end ComplexityTests.Code.MultilinearitySoundness
