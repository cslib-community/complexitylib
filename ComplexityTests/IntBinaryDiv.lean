/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.BinaryDiv
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
Signed binary modular reduction: negative wraparound, exact multiples, zero and unit moduli,
and native clients with growing binary operands and a computed signed difference.
-/

open Turing.MultiTapeTM

example : ((-1 : ℤ) % 64).toNat = 63 ∧ ((-65 : ℤ) % 64).toNat = 63 ∧
    ((-64 : ℤ) % 64).toNat = 0 ∧ ((65 : ℤ) % 64).toNat = 1 := by
  decide +kernel

example : ((-7 : ℤ) % 0).toNat = 0 ∧ ((7 : ℤ) % 0).toNat = 7 := by
  decide +kernel

example (z : ℤ) : (z % 1).toNat = 0 := by simp

-- Both operands may grow; the modulus is binary rather than enumerated or supplied in unary.
example : ComputableInPolyTime (fun p : ℤ × ℕ => (p.1 % (p.2 : ℤ)).toNat)
    (encPair encIntBin encNat) encNat := by
  fun_prop

-- The composition rule includes every operand of the signed difference and the modulus.
example : ComputableInPolyTime
    (fun p : (ℤ × ℤ) × ℕ => ((p.1.1 - p.1.2) % (p.2 : ℤ)).toNat)
    (encPair (encPair encIntBin encIntBin) encNat) encNat := by
  fun_prop
