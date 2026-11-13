/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Foundations.Algebra.Negacyclic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.FinCases

/-! Checked computations in the negacyclic ring `Negacyclic R n`, which is `R[X] / (X^n + 1)` for
`n ≠ 0`: the wrap `X^n = -1`, a product that differs from the pointwise one, the unit and
constants, the chosen zero ring at `n = 0`, cardinality, and `innerPoly` as a dot product. -/

namespace CslibFrontierTests.Foundations.Algebra.Negacyclic

open Cslib Negacyclic

/-- `X` in `(ZMod 7)[X] / (X^4 + 1)`. -/
abbrev X₇ : Negacyclic (ZMod 7) 4 := ofCoeffs ![0, 1, 0, 0]

/-- `X^4 = -1`: the fourth power wraps with a sign. -/
example : X₇ ^ 4 = -1 := by decide

/-- `X^3 · X = -1` over `ℤ`, with no wrap modulus. -/
example : (ofCoeffs ![0, 0, 0, 1] : Negacyclic ℤ 4) * ofCoeffs ![0, 1, 0, 0] = -1 := by decide

/-- `(1 + X) (1 + X^3) = X + X^3` modulo `X^4 + 1`. -/
example : (ofCoeffs ![1, 1, 0, 0] : Negacyclic ℤ 4) * ofCoeffs ![1, 0, 0, 1] =
    ofCoeffs ![0, 1, 0, 1] := by decide

/-- The same coefficient vectors multiply differently pointwise: `*` is never the Pi product. -/
example : (ofCoeffs ![1, 1, 0, 0] : Negacyclic ℤ 4) * ofCoeffs ![1, 0, 0, 1] ≠
    ofCoeffs (![1, 1, 0, 0] * ![1, 0, 0, 1]) := by decide

/-- `1` is the constant polynomial, and `algebraMap` embeds constants. -/
example : (1 : Negacyclic ℤ 3) = ofCoeffs ![1, 0, 0] := by decide

example : (algebraMap ℤ (Negacyclic ℤ 3) 5).coeffs = ![5, 0, 0] := by
  ext i
  fin_cases i <;> simp

/-- Numerals are constant polynomials. -/
example : (7 : Negacyclic ℤ 2).coeffs = ![7, 0] := by
  ext i
  fin_cases i <;> simp

/-- At `n = 0` the ring is the zero ring by choice; the quotient `ℤ[X] / (2)` is not. -/
example : (1 : Negacyclic ℤ 0) = 0 := by decide

example : Fintype.card (Negacyclic (ZMod 3) 2) = 9 := by
  rw [Fintype.card_congr coeffsEquiv]
  simp

/-- `innerPoly` is the dot product over `Negacyclic`. -/
example : ofCoeffs (innerPoly ![![0, 1], ![1, 1]] ![![0, 1], ![2, 0]] : Fin 2 → ℤ) =
    ![ofCoeffs ![0, 1], ofCoeffs ![1, 1]] ⬝ᵥ ![ofCoeffs ![0, 1], ofCoeffs ![2, 0]] := by
  decide

end CslibFrontierTests.Foundations.Algebra.Negacyclic
