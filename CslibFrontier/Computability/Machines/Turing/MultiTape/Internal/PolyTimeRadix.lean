/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeBinaryDivision
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.IntBinary
public import CslibFrontier.Foundations.Data.Nat.Radix
import CslibFrontier.Foundations.Data.Nat.Bits.Halving

/-!
# Direct signed shifts and runtime radix digits

Named certificates keep natural magnitudes binary and digit positions unary. Quotient iteration
only decreases the magnitude, so its prefix bound follows from the encoded input, not from the
numeric value of the dividend. No global encoding-search rule or raw transport is added.
-/

public section
namespace Turing.MultiTapeTM.ComputableInPolyTime

/-- Shift a natural digit by a natural radius, returning an ordinary sign-magnitude integer.
This is the existing `Int.subNatNat` function, not a second integer representation. -/
theorem intBin_subNatNat : ComputableInPolyTime (fun p : ℕ × ℕ => Int.subNatNat p.1 p.2)
    (encPair encNat encNat) encIntBin := by
  have hr := binary_sub.comp ((snd encNat encNat).prod (fst encNat encNat))
  have hm := binary_add.comp (binary_sub.prod hr)
  have hbits : ComputableInPolyTime Nat.bits encNat encBits := of_eq fun _ => rfl
  have h := bitsCons binary_lt (hbits.comp hm)
  apply h.of_enc_eq
  intro p
  change encIntBin (Int.subNatNat p.1 p.2) =
    decide (p.1 < p.2) :: ((p.1 - p.2) + (p.2 - p.1)).bits
  rw [encIntBin_apply, Int.subNatNat_eq_coe]
  have hs : decide ((p.1 : ℤ) - p.2 < 0) = decide (p.1 < p.2) := by grind
  rw [hs]
  congr 2
  rcases le_total p.1 p.2 with hl | hr
  · have he : (p.1 : ℤ) - p.2 = -((p.2 - p.1 : ℕ) : ℤ) := by omega
    rw [he]
    simp [Nat.sub_eq_zero_of_le hl]
  · have he : (p.1 : ℤ) - p.2 = ((p.1 - p.2 : ℕ) : ℤ) := by omega
    rw [he]
    simp [Nat.sub_eq_zero_of_le hr]

/-- Read the existing radix digit with binary base/value and a unary runtime position.
The certificate is total, including bases zero and one. -/
theorem radix_digit :
    ComputableInPolyTime (fun p : (ℕ × ℕ) × ℕ => Cslib.Radix.digit p.1.1 p.1.2 p.2)
      (encPair (encPair encNat encNat) encUnary) encNat := by
  have hp := fst (encPair encNat encNat) encUnary
  have hb := (fst encNat encNat).comp hp
  have hx := (snd encNat encNat).comp hp
  have hi := snd (encPair encNat encNat) encUnary
  have hstep := binary_div.comp ((snd encNat encNat).prod (fst encNat encNat))
  have hit := iterateWith (par := fun p : (ℕ × ℕ) × ℕ => p.1.1) (count := fun p => p.2)
    (init := fun p => p.1.2) (step := fun B acc => acc / B) hb hi hx hstep
    (bound := fun p => (encPair (encPair encNat encNat) encUnary p).length) .self (by
      intro p i _
      rw [Nat.iterate_div]
      have hq : (encNat (p.1.2 / p.1.1 ^ i)).length ≤ (encNat p.1.2).length := by
        simpa [Nat.size_eq_bits_len] using Nat.size_le_size (Nat.div_le_self p.1.2 (p.1.1 ^ i))
      exact hq.trans ((length_le_encPair_right encNat encNat p.1).trans
        (length_le_encPair_left (encPair encNat encNat) encUnary p)))
  have h := binary_mod.comp (hit.prod hb)
  convert h using 1
  funext p
  simp only [Cslib.Radix.digit_eq_div_pow_mod, Nat.iterate_div, Function.comp_def]

end Turing.MultiTapeTM.ComputableInPolyTime
