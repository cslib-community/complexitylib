/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.LinearAlgebra.Matrix.RectPermanent
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Tests for `Complexity.Foundations.LinearAlgebra.Matrix.RectPermanent`

Concrete values of `Matrix.rectPerm` and `Matrix.rectPermSurj` on `1 × 2` and `2 × 3` matrices
(nonzero, so neither definition is trivially zero), the square and vanishing cases, the
Binet–Minc identities instantiated at a `2 × 3` matrix, and the right-hand side of the Binet–Minc
identity evaluated directly at a concrete `2 × 3` matrix.
-/

@[expose] public section

namespace Cslib.LinearAlgebra.RectPermanentTests

open Equiv Equiv.Perm Finset Matrix

/-- A `1 × 2` rectangular permanent is the sum of the row. -/
example : !![(2 : ℤ), 3].rectPerm = 5 := by
  rw [rectPerm_eq_sum_injective]
  decide

/-- Requiring column `0` in the image keeps only the injection `0 ↦ 0`. -/
example : !![(2 : ℤ), 3].rectPermSurj {0} = 2 := by
  rw [rectPermSurj_eq_sum_injective]
  decide

/-- A `2 × 3` rectangular permanent: the six injections `Fin 2 ↪ Fin 3`. -/
example : !![(1 : ℤ), 2, 3; 4, 5, 6].rectPerm = 1 * 5 + 1 * 6 + 2 * 4 + 2 * 6 + 3 * 4 + 3 * 5 := by
  rw [rectPerm_eq_sum_injective]
  decide

/-- Requiring column `2` in the image keeps four of the six injections. -/
example : !![(1 : ℤ), 2, 3; 4, 5, 6].rectPermSurj {2} = 1 * 6 + 2 * 6 + 3 * 4 + 3 * 5 := by
  rw [rectPermSurj_eq_sum_injective]
  decide

/-- On square matrices `rectPerm` is the permanent. -/
example : (1 : Matrix (Fin 3) (Fin 3) ℤ).rectPerm = 1 := by
  rw [rectPerm_eq_permanent, permanent_one]

/-- With more rows than columns there are no injections. -/
example (b : Matrix (Fin 3) (Fin 2) ℤ) : b.rectPerm = 0 :=
  rectPerm_eq_zero_of_card_lt b (by simp)

/-- Three required columns cannot be covered by two rows. -/
example (b : Matrix (Fin 2) (Fin 3) ℤ) : b.rectPermSurj univ = 0 :=
  rectPermSurj_eq_zero_of_card_lt univ b (by simp)

example (b : Matrix (Fin 2) (Fin 3) ℤ) : b.rectPermSurj ∅ = b.rectPerm := by
  simp

/-- The Binet–Minc identity at a `2 × 3` matrix over `ℤ`. -/
example (b : Matrix (Fin 2) (Fin 3) ℤ) :
    b.rectPerm = ∑ π : Perm (Fin 2), sign π • ∏ q : Quotient (SameCycle.setoid π),
      ∑ j, ∏ r with Quotient.mk _ r = q, b r j :=
  rectPerm_eq_sum_sign_prod_sameCycle b

/-- Its inclusion–exclusion extension at a `2 × 3` matrix over `ℤ`. -/
example (b : Matrix (Fin 2) (Fin 3) ℤ) (Z : Finset (Fin 3)) :
    b.rectPermSurj Z = ∑ π : Perm (Fin 2), sign π • ∑ Y ∈ Z.powerset, (-1) ^ #Y *
      ∏ q : Quotient (SameCycle.setoid π), ∑ j ∈ Yᶜ, ∏ r with Quotient.mk _ r = q, b r j :=
  rectPermSurj_eq_sum_sign_prod_sameCycle Z b

/-- The right-hand side of the Binet–Minc identity evaluated directly, at the matrix above. -/
example : ∑ π : Perm (Fin 2), sign π • ∏ q : Quotient (SameCycle.setoid π),
      ∑ j, ∏ r with Quotient.mk _ r = q, !![(1 : ℤ), 2, 3; 4, 5, 6] r j = 58 := by
  decide

end Cslib.LinearAlgebra.RectPermanentTests
