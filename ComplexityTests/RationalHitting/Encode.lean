/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Karn Seth
-/

import Complexity.Computability.Circuit.Rational.Runtime.Encode
import Complexity.Foundations.Data.Rat.Basic

/-!
# Binary division, Euclidean GCD, and canonical rational encodings

Concrete evaluations of binary long division, Euclidean remainder steps, and canonical natural and
rational encodings; and composed clients of `binary_div`, `binary_mod`, `binary_gcd`,
`encodeNat_polytime`, and `encodeDivInt_polytime` under `fun_prop`.
-/

namespace ComplexityTests.RationalHitting.Encode

open Turing MultiTapeTM ComputableTidilyInPolyTime
open Cslib.Circuits.Rational

/-! ### Binary long division, Euclidean GCD, and canonical encodings -/

example :
    (43 : ℕ).bits.reverse.foldl (BinaryDiv.divModStep 6) (0, 0) = (7, 1) ∧
    (43 : ℕ).bits.reverse.foldl (BinaryDiv.divModStep 0) (0, 0) = (0, 43) ∧
    ((43 : ℕ) / 6 = 7 ∧ (43 : ℕ) % 6 = 1) ∧
    2 * (6 * (43 % 6)) ≤ 6 * 43 ∧
    BinaryGcd.gcdStep^[BinaryGcd.gcdCount (42, 30)] (42, 30) = (6, 0) ∧
    BinaryGcd.gcdStep^[BinaryGcd.gcdCount (0, 15)] (0, 15) = (15, 0) ∧
    encodeNat 0 = [false] ∧
    encodeNat 6 = [true, true, true, false, false, true, true] ∧
    (Rat.divInt (-6) 4).num.natAbs = 3 ∧
    (Rat.divInt (-6) 4).den = 2 ∧
    decide ((Rat.divInt (-6) 4).num < 0) = true ∧
    encodeRat (Rat.divInt (-6) 4) =
      [true, true, true, false, true, true, true, true, false, false, true] ∧
    encodeRat (Rat.divInt 5 0) = [false, false, true, false, true] := by
  refine ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel⟩,
    BinaryGcd.gcd_product_halving (by decide) (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [BinaryGcd.iterate_gcdStep_eq]; decide +kernel
  · rw [BinaryGcd.iterate_gcdStep_eq]; decide +kernel
  · rw [encodeNat_eq]; decide +kernel
  · rw [encodeNat_eq]; decide +kernel
  · rw [Rat.natAbs_num_divInt_of_ne_zero (-6) 4 (by decide)]; decide +kernel
  · rw [Rat.den_divInt]; decide +kernel
  · rw [divInt_sign (-6) 4 (by decide)]; decide +kernel
  · rw [encodeRat_divInt]; decide +kernel
  · rw [encodeRat_divInt]; decide +kernel

/-! ### Certificates and composed clients -/

attribute [local fun_prop] ComputableInPolyTime.tidy in
example :
    ComputableInPolyTime (fun p : ℕ × ℕ => (p.1 / p.2, p.1 % p.2))
      (encPair encNat encNat) (encPair encNat encNat) ∧
    ComputableInPolyTime (fun p : ℕ × ℕ => encodeNat (Nat.gcd (p.1 / p.2) (p.1 % p.2)))
      (encPair encNat encNat) encBits ∧
    ComputableInPolyTime
      (fun p : ℤ × ℤ => encodeRat (Rat.divInt (p.1 + p.2) (p.1 * p.2 - 1)))
      (encPair encIntBin encIntBin) encBits ∧
    ComputableInPolyTime
      (fun p : ℤ × ℤ =>
        encodeNat (Nat.gcd p.1.natAbs p.2.natAbs) ++ encodeRat (Rat.divInt p.1 p.2))
      (encPair encIntBin encIntBin) encBits := by
  refine ⟨.of_tidy binary_divMod, .of_tidy (by fun_prop), ?_, ?_⟩
  · apply encodeDivInt_polytime' <;> exact .of_tidy (by fun_prop)
  · apply ComputableInPolyTime.of_tidy
    have hrat := encodeDivInt_polytime.tidy
    have hnat : ComputableTidilyInPolyTime
        (fun p : ℤ × ℤ => encodeNat (Nat.gcd p.1.natAbs p.2.natAbs))
        (encPair encIntBin encIntBin) encBits := by fun_prop
    fun_prop

end ComplexityTests.RationalHitting.Encode
