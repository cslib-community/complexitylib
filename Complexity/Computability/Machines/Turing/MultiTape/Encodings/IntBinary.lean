/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat
public import Mathlib.Data.Nat.Size

/-!
# Binary sign-magnitude integers

`encIntBin` encodes an integer by a sign bit, `true` for negative integers, followed by the binary
digits of its magnitude (`Turing.MultiTapeTM.encNat`), least significant first. The magnitude is
not framed: the sign is a single leading bit, the digits are the rest of the word, and the
magnitude is the tail of the code, so the binary natural arithmetic applies to it directly. A
negative integer has a nonzero magnitude, so zero has the single code `[false]`. An integer `z`
occupies `Nat.size z.natAbs + 1` bits. The unary integers `Turing.MultiTapeTM.encIntUnary` index
tape positions; this encoding carries values whose magnitude is exponential in their length.

## Main definitions

* `Turing.MultiTapeTM.encIntBin`: integers as a sign bit followed by a binary magnitude.

## Main results

* `Turing.MultiTapeTM.length_encIntBin`: the code of `z` has `Nat.size z.natAbs + 1` bits.
* `Turing.MultiTapeTM.encIntBin_natCast`, `Turing.MultiTapeTM.encIntBin_negSucc`: the codes of
  nonnegative and negative integers.
-/

@[expose] public section

namespace Turing.MultiTapeTM

/-- Integers in binary sign-magnitude form: the bit `z < 0` followed by the binary digits of the
magnitude `z.natAbs`, least significant first. Zero is encoded as `[false]` only. -/
def encIntBin : ℤ ↪ List Bool :=
  ⟨fun z => decide (z < 0) :: encNat z.natAbs, fun z w h => by
    simp only [List.cons.injEq, decide_eq_decide] at h
    have := encNat.injective h.2
    lia⟩

@[simp]
theorem encIntBin_apply (z : ℤ) : encIntBin z = decide (z < 0) :: z.natAbs.bits := rfl

/-- The code of an integer has one sign bit and the binary length of its magnitude. -/
theorem length_encIntBin (z : ℤ) : (encIntBin z).length = z.natAbs.size + 1 := by
  simp [Nat.size_eq_bits_len]

theorem encIntBin_natCast (n : ℕ) : encIntBin n = false :: n.bits := by
  simp

theorem encIntBin_zero : encIntBin 0 = [false] := rfl

theorem encIntBin_negSucc (n : ℕ) : encIntBin (Int.negSucc n) = true :: (n + 1).bits := by
  simp only [encIntBin_apply, Int.negSucc_lt_zero, decide_true, Int.natAbs_negSucc]

end Turing.MultiTapeTM
