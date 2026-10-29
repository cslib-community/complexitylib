/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import Complexity.Computability.Complexity.Classes.Padding.Polynomial
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.PolynomialPadding
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible

/-! Concrete padding, decoding, acceptance/rejection by the padding guard, and the improved
binary-to-unary resource bound. -/

public section

namespace ComplexityTests.PolynomialPadding

open Turing.MultiTapeTM

private def cubePad (x : List Bool) : List Bool :=
  frame x ++ List.replicate ((x.length + 1) ^ 3) true

private def roundedSquarePad (x : List Bool) : List Bool :=
  frame x ++ List.replicate (2 ^ (2 * Nat.size (x.length + 1))) true

/-- The certified cubic writer keeps its exact output length and decodes without reading padding. -/
example :
    ComputableInO cubePad encBits encBits (fun x => (x.length + 1) ^ 6)
      (fun x => (x.length + 1) ^ 3) ∧
    (cubePad [true, false]).length = 32 ∧
    unframe (cubePad [true, false]) = [true, false] :=
  ⟨computableInO_polynomialPadding (k := 3) (by decide), by decide, by decide⟩

/-- Sufficient padding passes the guard; a bare nonempty frame fails it. The empty word still
has a delimiter and one padding bit. -/
example :
    decide (((unframe (cubePad [true, false])).length + 1) ^ 3 ≤
      (cubePad [true, false]).length) = true ∧
    decide (((unframe (frame [true, false])).length + 1) ^ 3 ≤
      (frame [true, false]).length) = false ∧
    cubePad [] = [false, true] := by decide

/-- The rounded quadratic padding writer has a cubic runtime, and its concrete output still
passes the same quadratic padding guard and recovers the original word. -/
example :
    ComputableInO roundedSquarePad encBits encBits (fun x => (x.length + 1) ^ 3)
      (fun x => (x.length + 1) ^ 2) ∧
    (roundedSquarePad [true, false]).length = 21 ∧
    unframe (roundedSquarePad [true, false]) = [true, false] ∧
    decide (((unframe (roundedSquarePad [true, false])).length + 1) ^ 2 ≤
      (roundedSquarePad [true, false]).length) = true :=
  ⟨computableInO_roundedPolynomialPadding (k := 2) (by decide),
    by decide, by decide, by decide⟩

/-- Binary-to-unary conversion now has a quadratic time bound and retains its linear space
bound, including the zero and nonzero output encodings. -/
theorem binaryToUnary_bound_and_values :
    ComputableInO (fun n : ℕ => n) encNat encUnary (fun n => (n + 1) ^ 2) (fun n => n) ∧
    encUnary 0 = [] ∧ encUnary 4 = [true, true, true, true] :=
  ⟨ComputableInO.natToUnary, rfl, rfl⟩

end ComplexityTests.PolynomialPadding
