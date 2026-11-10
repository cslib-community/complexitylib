/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib.FieldTheory.Finite.Basic)

public import CslibFrontier.Init
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Finite fields and groups with zero

Basic results about powers and inverses in finite groups with zero and finite fields.

## Main results

* `FiniteField.pow_card_sub_two_eq_inv`: in a finite group with zero `K`, `a ^ (q - 2) = a⁻¹`
  for `a ≠ 0`.
* `ZMod.pow_card_sub_two_eq_inv`: Fermat's inverse identity `a ^ (p - 2) = a⁻¹` in `ZMod p`.
-/

@[expose] public section

namespace FiniteField

section GroupWithZero

variable {K : Type*} [GroupWithZero K] [Fintype K]

local notation "q" => Fintype.card K

/-- In a finite group with zero, the `q - 2`-nd power of a nonzero element is its inverse. -/
theorem pow_card_sub_two_eq_inv (a : K) (ha : a ≠ 0) : a ^ (q - 2) = a⁻¹ := by
  have : 2 ≤ q := Fintype.one_lt_card
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← pow_succ, show q - 2 + 1 = q - 1 by omega, pow_card_sub_one_eq_one a ha]

end GroupWithZero

/-- In `ZMod p`, the `p - 2`-nd power of a nonzero residue is its inverse. -/
theorem _root_.ZMod.pow_card_sub_two_eq_inv {p : ℕ} [Fact p.Prime] {a : ZMod p} (ha : a ≠ 0) :
    a ^ (p - 2) = a⁻¹ := by
  have := FiniteField.pow_card_sub_two_eq_inv a ha
  rwa [ZMod.card] at this

end FiniteField
