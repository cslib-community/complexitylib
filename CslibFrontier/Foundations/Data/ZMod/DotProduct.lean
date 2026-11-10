/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.List.DotProduct
public import Mathlib.Data.ZMod.Basic

/-!
# Integer list dot products and residue matrices

The integer-cast matrix bridge formerly used inside Lyubashevsky's verifier is available
independently of cryptography and native certificates. The operation is Mathlib's public
padded list dot product; no new arithmetic definition is introduced.

## Main results

* `intCast_dotProduct_matrix_ofFn`: reduction of the integer product is matrix-vector
  multiplication over `ZMod q`, including modulus zero.
-/

public section

open scoped Matrix

namespace Mathlib.Tactic.Matrix.ListMatrix

/-- A canonical integer lift of a residue-matrix row gives its residue dot product. -/
theorem intCast_dotProduct_matrix_ofFn {n m q : ℕ}
    (A : _root_.Matrix (Fin n) (Fin m) (ZMod q)) (z : Fin m → ℤ) (i : Fin n) :
    ((dotProduct m
      ((List.ofFn fun r : Fin n => List.ofFn fun c : Fin m => ZMod.cast (A r c)).getD i.val [])
      (List.ofFn z) : ℤ) : ZMod q) =
      (A *ᵥ (Int.cast ∘ z)) i := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.isLt, ↓reduceDIte, Option.getD_some]
  rw [dotProduct_ofFn, Int.cast_sum]
  simp only [Int.cast_mul, ZMod.intCast_zmod_cast]
  rfl

end Mathlib.Tactic.Matrix.ListMatrix
