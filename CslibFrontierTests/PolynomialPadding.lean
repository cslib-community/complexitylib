/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Computability.Complexity.Classes.Padding.Polynomial
import CslibFrontier.Computability.Complexity.Classes.Padding.Translation
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.PolynomialPadding
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible

/-! Concrete padding, decoding, acceptance/rejection by the padding guard, the linear
binary-to-unary resource bound, and instances of the translation lemma. -/

public section

namespace CslibFrontierTests.PolynomialPadding

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

/-- Binary-to-unary conversion has linear time and space bounds, including the zero and nonzero
output encodings. -/
theorem binaryToUnary_bound_and_values :
    ComputableInO (fun n : ℕ => n) encNat encUnary (fun n => n) (fun n => n) ∧
    encUnary 0 = [] ∧ encUnary 4 = [true, true, true, true] :=
  ⟨ComputableInO.natToUnary, rfl, rfl⟩

open Cslib.Complexity in
/-- The translation lemma along the padding function `2 * n + 1`: a collapse from quadratic to
linear time would transfer to the doubled lengths. -/
example (h : DTIME encBits (fun n => (n + 1) ^ 2) ⊆ DTIME encBits (fun n => n + 1)) :
    DTIME encBits ((fun n => (n + 1) ^ 2) ∘ fun n => 2 * n + 1) ⊆
      DTIME encBits ((fun n => n + 1) ∘ fun n => 2 * n + 1) :=
  DTIME_comp_subset_of_subset (fun _ _ hmn => Nat.pow_le_pow_left (by omega) 2)
    (fun n => by nlinarith) (fun n => by omega) (by fun_prop) (fun n => by omega) h

open Cslib.Complexity in
/-- Polynomial padding transfers collapses whose smaller degree is linear. -/
example (h : DTIME encBits (fun n => (n + 1) ^ 2) ⊆ DTIME encBits (fun n => (n + 1) ^ 1)) :
    DTIME encBits (fun n => (n + 1) ^ (2 * 3)) ⊆ DTIME encBits (fun n => (n + 1) ^ (1 * 3)) :=
  DTIME_pow_mul_subset_of_subset le_rfl (by omega) (by omega) h

end CslibFrontierTests.PolynomialPadding
