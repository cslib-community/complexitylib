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

/-! ### Binary long division -/

example : (43 : ℕ).bits.reverse.foldl (BinaryDiv.divModStep 6) (0, 0) = (7, 1) := by
  decide +kernel

example : (43 : ℕ).bits.reverse.foldl (BinaryDiv.divModStep 0) (0, 0) = (0, 43) := by
  decide +kernel

example : (43 : ℕ) / 6 = 7 ∧ (43 : ℕ) % 6 = 1 := by
  have h := BinaryDiv.divMod_eq (43, 6)
  exact ⟨by decide +kernel, by decide +kernel⟩

/-! ### Euclidean GCD -/

example : 2 * (6 * (43 % 6)) ≤ 6 * 43 :=
  BinaryGcd.gcd_product_halving (by decide) (by decide)

example : BinaryGcd.gcdStep^[BinaryGcd.gcdCount (42, 30)] (42, 30) = (6, 0) := by
  rw [BinaryGcd.iterate_gcdStep_eq]
  decide +kernel

example : BinaryGcd.gcdStep^[BinaryGcd.gcdCount (0, 15)] (0, 15) = (15, 0) := by
  rw [BinaryGcd.iterate_gcdStep_eq]
  decide +kernel

/-! ### Canonical natural and rational encodings -/

example : encodeNat 0 = [false] := by
  rw [encodeNat_eq]
  decide +kernel

example : encodeNat 6 = [true, true, true, false, false, true, true] := by
  rw [encodeNat_eq]
  decide +kernel

example : (Rat.divInt (-6) 4).num.natAbs = 3 := by
  rw [Rat.natAbs_num_divInt_of_ne_zero (-6) 4 (by decide)]
  decide +kernel

example : (Rat.divInt (-6) 4).den = 2 := by
  rw [Rat.den_divInt]
  decide +kernel

example : decide ((Rat.divInt (-6) 4).num < 0) = true := by
  rw [Rat.decide_num_divInt_lt_zero_of_ne_zero (-6) 4 (by decide)]
  decide +kernel

example : decide ((Rat.divInt (-6) 0).num < 0) = false := by
  rw [Rat.decide_num_divInt_lt_zero (-6) 0]
  decide +kernel

example : encodeRat (Rat.divInt (-6) 4) =
    [true, true, true, false, true, true, true, true, false, false, true] := by
  rw [encodeRat_divInt]
  decide +kernel

example : encodeRat (Rat.divInt 5 0) = [false, false, true, false, true] := by
  rw [encodeRat_divInt]
  decide +kernel

/-! ### Certificates and composed clients -/

example : ComputableInPolyTime
    (fun p : ℕ × ℕ => encodeNat (Nat.gcd (p.1 / p.2) (p.1 % p.2)))
    (encPair encNat encNat) encBits := by
  fun_prop

example : ComputableInPolyTime
    (fun p : ℕ × ℕ => let qr := (p.1 / p.2, p.1 % p.2); encodeNat (qr.1 + qr.2))
    (encPair encNat encNat) encBits := by
  have hqr : ComputableInPolyTime (fun p : ℕ × ℕ => (p.1 / p.2, p.1 % p.2))
      (encPair encNat encNat) (encPair encNat encNat) := .of_tidy binary_divMod
  have hadd : ComputableInPolyTime (fun qr : ℕ × ℕ => encodeNat (qr.1 + qr.2))
      (encPair encNat encNat) encBits := by fun_prop
  exact hadd.comp hqr

example : ComputableInPolyTime
    (fun p : ℤ × ℤ => encodeRat (Rat.divInt (p.1 + p.2) (p.1 * p.2 - 1)))
    (encPair encIntBin encIntBin) encBits := by
  apply encodeDivInt_polytime' <;> exact .of_tidy (by fun_prop)

example : ComputableInPolyTime
    (fun p : ℤ × ℤ =>
      encodeNat (Nat.gcd p.1.natAbs p.2.natAbs) ++ encodeRat (Rat.divInt p.1 p.2))
    (encPair encIntBin encIntBin) encBits := by
  have hrat := encodeDivInt_polytime
  have hnat : ComputableInPolyTime
      (fun p : ℤ × ℤ => encodeNat (Nat.gcd p.1.natAbs p.2.natAbs))
      (encPair encIntBin encIntBin) encBits := by fun_prop
  fun_prop

end ComplexityTests.RationalHitting.Encode
