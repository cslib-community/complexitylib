/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.GenericRAM.Native.IndexFold
public import Complexity.Foundations.Data.Nat.Radix.Measurement
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeBinaryPower

/-!
# Binary clocks for measurement-value enumeration

The dimension is a runtime unary natural and the radius a runtime binary natural. Count
preparation is polynomial in their full encoding even though the number of visits need not be.
The decoder and streaming native client are separate obligations of runtime M0.4 in #1226.
-/

@[expose] public section
namespace Cslib.GenericRAM.MeasurementFold

open Turing.MultiTapeTM

/-- The actual number of signed measurement tuples in dimension `c` and radius `D`. -/
def count (p : ℕ × ℕ) : ℕ := (2 * p.2 + 1) ^ p.1

private theorem radix_polyTime :
    ComputableInPolyTime (fun D : ℕ => 2 * D + 1) encNat encNat := by
  have hbits : ComputableInPolyTime Nat.bits encNat encBits :=
    ComputableInPolyTime.of_eq fun _ => rfl
  have h := ComputableInPolyTime.bitsCons (ComputableInPolyTime.const true) hbits
  apply h.of_enc_eq
  intro D
  change (2 * D + 1).bits = true :: D.bits
  exact Nat.bit1_bits D

/-- Prepare the visit count in binary, charging the unary dimension and binary radius. -/
theorem count_polyTime : ComputableInPolyTime count (encPair encUnary encNat) encNat := by
  exact ComputableInPolyTime.binary_pow.comp
    ((radix_polyTime.comp (ComputableInPolyTime.snd encUnary encNat)).prod
      (ComputableInPolyTime.fst encUnary encNat))

/-- An actual fixed native count-preparation machine; no unary exponential count is produced. -/
noncomputable def clock : NativeCertificate count (encPair encUnary encNat) encNat :=
  NativeCertificate.ofPolyTime count_polyTime

/-- Both preparation bounds are polynomial in the complete runtime pair encoding. -/
theorem clock_isPolynomial : clock.IsPolynomial :=
  NativeCertificate.ofPolyTime_isPolynomial count_polyTime

/-- The binary count has polynomial bit length, rather than polynomial numeric value. -/
theorem length_count_le (c D : ℕ) :
    (encNat (count (c, D))).length ≤ c * (D.size + 1) + 1 := by
  change ((2 * D + 1) ^ c).bits.length ≤ _
  rw [Nat.size_eq_bits_len]
  have hb := Nat.size_bit (b := true) (n := D) (by simp [Nat.bit])
  simp only [Nat.bit_val, Bool.toNat_true, Nat.succ_eq_add_one] at hb
  simpa only [hb] using Nat.size_pow_le (2 * D + 1) c

end Cslib.GenericRAM.MeasurementFold
