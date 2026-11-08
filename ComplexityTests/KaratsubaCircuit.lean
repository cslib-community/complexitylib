/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import Complexity.Computability.Circuit.Boolean.Karatsuba

/-!
# Tests for Karatsuba multiplication circuits

Exact gate counts, the product on concrete inputs, a direct application of the synthesis bound
with satisfiable hypotheses, and the complexity bound at concrete widths.
-/

namespace ComplexityTests.KaratsubaCircuit

open Cslib Cslib.Circuits Cslib.Circuits.Boolean

/-! ### Gate counts -/

example : Karatsuba.gates 2 = 407 := by decide +kernel
example : Karatsuba.gates 3 = 1823 := by decide +kernel
example : Karatsuba.gates 4 = 1995 := by decide +kernel

/-- At `w = 3` the construction is larger than the schoolbook modular bound `63 (w + 1)²`. -/
example : 63 * (3 + 1) ^ 2 < Karatsuba.gates 3 + 1 := by decide +kernel

/-- At `w = 1024` it is smaller, although it returns twice as many bits. -/
example : Karatsuba.gates 1024 + 1 < 63 * (1024 + 1) ^ 2 := by decide +kernel

/-- The closed bound `419 · 3 ^ ⌈log₂ w⌉` at `w = 4`, where it is `3771`. -/
example : Karatsuba.gates 4 ≤ 3771 := by
  have h := Karatsuba.gates_le_pow_clog 4
  have h4 : Nat.clog 2 4 = 2 := Nat.clog_pow 2 2 one_lt_two
  simp only [h4] at h
  omega

/-! ### The product -/

/-- `3 · 3 = 9`: the halves `11` and `11` give `1001`, least significant bit first. -/
example : mulBits 2 ![true, true, true, true] = ![true, false, false, true] := by decide +kernel

/-- `2 · 3 = 6`. -/
example : mulBits 2 ![false, true, true, true] = ![false, true, true, false] := by decide +kernel

example (x : BitString (3 + 3)) :
    (BitString.equivFin (3 + 3) (mulBits 3 x) : ℕ) =
      (BitString.equivFin 3 (BitString.fstBits x) : ℕ) *
        (BitString.equivFin 3 (BitString.sndBits x) : ℕ) :=
  val_equivFin_mulBits 3 x

/-! ### The synthesis bound applies to the input halves -/

example (w : ℕ) :
    Synthesis interpretation (inputs (w + w) ∪ {fun _ => false})
      (wordWires fun x => (word (BitString.fstBits x)).setWidth (w + w) *
        (word (BitString.sndBits x)).setWidth (w + w))
      (Karatsuba.gates w) :=
  Synthesis.word_mul_karatsuba _ _
    (fun i => Or.inl ⟨Fin.castAdd w i, funext fun x => by simp⟩)
    (fun i => Or.inl ⟨Fin.natAdd w i, funext fun x => by simp⟩)
    (Or.inr rfl)

/-! ### Circuit complexity -/

example : complexity interpretation (mulBits 2) ≤ 408 :=
  (complexity_mulBits_le 2).trans (by decide +kernel)

/-- Width zero: no outputs, and the bound charges only the `false` constant. -/
example : complexity interpretation (mulBits 0) ≤ 1 := by
  simpa using complexity_mulBits_le 0

end ComplexityTests.KaratsubaCircuit
