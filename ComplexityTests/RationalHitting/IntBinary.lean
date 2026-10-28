/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Karn Seth
-/

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary

/-!
# Binary sign-magnitude integers and binary subtraction

Concrete codes of binary sign-magnitude integers and their lengths, the schoolbook subtraction
program on concrete operands, instances of the binary length bounds, and composed clients of the
integer certificates under `fun_prop`.
-/

namespace ComplexityTests.IntBinary

open Turing MultiTapeTM ComputableTidilyInPolyTime

/-! ### Concrete codes, schoolbook subtraction, and binary lengths -/

/-- The borrow fold of `binary_sub` on concrete operands: the final borrow and the digits. -/
def subRun (a b : ℕ) : Bool × List Bool :=
  (BinarySub.digitPairs (a, b)).foldl BinarySub.subStep (false, [])

-- A final borrow marks a negative difference; the digits are then its two's complement.
/-- info: [(false, 7), (true, 121), (false, 0), (false, 1000)] -/
#guard_msgs in
#eval [(13, 6), (6, 13), (6, 6), (1024, 24)].map fun p : ℕ × ℕ =>
  ((subRun p.1 p.2).1, (subRun p.1 p.2).2.foldr Nat.bit 0)

example (z : ℤ) (h : encIntBin z = [false]) :
    (encIntBin 0 = [false] ∧ encIntBin 6 = [false, false, true, true] ∧
      encIntBin (-6) = [true, false, true, true] ∧ encIntBin (-1) = [true, true]) ∧
    ((encIntBin (-6)).headD false = true ∧ (encIntBin (-6)).tail = encNat 6 ∧
      (encIntBin (-6)).length = Nat.size 6 + 1 ∧ (encIntBin (-6)).length = 4) ∧
    z = 0 ∧
    ((13 : ℕ) - 6 = 7 ∧
      ([false, true, true, false, false] : List Bool).foldr Nat.bit 0 = 6) ∧
    ((6 * 7 : ℕ).size ≤ Nat.size 6 + Nat.size 7 ∧
      (-6 + -7 : ℤ).natAbs.size ≤ max (Nat.size 6) (Nat.size 7) + 1 ∧
      ((-3 : ℤ) ^ 4).natAbs.size ≤ 4 * Nat.size 3 + 1 ∧
      ([3, -2, 1] : List ℤ).sum.natAbs.size ≤ 2 + Nat.size 3) :=
  ⟨by decide +kernel,
    ⟨by decide +kernel, by decide +kernel, length_encIntBin (-6), by decide +kernel⟩,
    encIntBin.injective h,
    ⟨by rw [BinarySub.sub_eq (13, 6)]; decide +kernel, by decide +kernel⟩,
    ⟨Nat.size_mul_le 6 7, Int.size_natAbs_add_le (-6) (-7), Int.size_natAbs_pow_le (-3) 4,
      Int.size_natAbs_sum_le (by decide +kernel)⟩⟩

/-! ### Certificates and composed clients -/

example :
    ComputableInPolyTime (fun p : ℤ × ℤ => p.1 * p.2 - p.2)
      (encPair encIntBin encIntBin) encIntBin ∧
    ComputableInPolyTime (fun p : ℤ × ℤ => -(p.1 + p.2) * p.1)
      (encPair encIntBin encIntBin) encIntBin ∧
    ComputableInPolyTime (fun p : ℤ × ℕ => (p.1 ^ p.2).natAbs)
      (encPair encIntBin encUnary) encNat ∧
    ComputableInPolyTime (fun p : ℕ × ℕ => ((p.1 : ℤ) - p.2).natAbs)
      (encPair encNat encNat) encNat ∧
    ComputableInPolyTime
      (fun p : ℤ × ℤ => decide (p.1 * p.1 ≤ p.2) && !decide (p.2 = 0))
      (encPair encIntBin encIntBin) encBool ∧
    ComputableInPolyTime (fun p : List ℤ × ℤ => p.1.sum - p.2)
      (encPair (encList encIntBin) encIntBin) encIntBin ∧
    ComputableInPolyTime (fun p : ℕ × ℕ => (p.1 - p.2) * p.1 ^ 3)
      (encPair encNat encNat) encNat :=
  ⟨.of_tidy (by fun_prop), .of_tidy (by fun_prop), .of_tidy (by fun_prop),
    .of_tidy (by fun_prop), .of_tidy (by fun_prop), .of_tidy (by fun_prop),
    .of_tidy (by fun_prop)⟩

end ComplexityTests.IntBinary
