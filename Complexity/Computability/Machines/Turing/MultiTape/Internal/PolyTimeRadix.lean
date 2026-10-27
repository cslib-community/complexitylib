/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeBinaryDivision
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.IntBinary
public import Complexity.Foundations.Data.Nat.Radix

/-!
# Direct signed shifts and runtime radix digits

Named certificates keep natural magnitudes binary and digit positions unary. Quotient iteration
only decreases the magnitude, so its prefix bound follows from the encoded input, not from the
numeric value of the dividend. No global encoding-search rule or raw transport is added.
-/

@[expose] public section
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
  have hs : decide ((p.1 : ℤ) - p.2 < 0) = decide (p.1 < p.2) := by
    rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq]
    omega
  rw [hs]
  congr 2
  rcases le_total p.1 p.2 with hl | hr
  · have he : (p.1 : ℤ) - p.2 = -((p.2 - p.1 : ℕ) : ℤ) := by omega
    rw [he]
    simp [Nat.sub_eq_zero_of_le hl]
  · have he : (p.1 : ℤ) - p.2 = ((p.1 - p.2 : ℕ) : ℤ) := by omega
    rw [he]
    simp [Nat.sub_eq_zero_of_le hr]

private theorem quotientFold (B x k : ℕ) :
    (List.replicate k true).foldl (fun acc _ => acc / B) x = x / B ^ k := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ, List.foldl_cons, ih, Nat.div_div_eq_div_mul, Nat.pow_succ']

/-- Read the existing radix digit with binary base/value and a unary runtime position.
The certificate is total, including bases zero and one. -/
theorem radix_digit :
    ComputableInPolyTime (fun p : (ℕ × ℕ) × ℕ => Cslib.Radix.digit p.1.1 p.1.2 p.2)
      (encPair (encPair encNat encNat) encUnary) encNat := by
  have hp := fst (encPair encNat encNat) encUnary
  have hb := (fst encNat encNat).comp hp
  have hx := (snd encNat encNat).comp hp
  have hi := snd (encPair encNat encNat) encUnary
  have hlist := (of_eq (encIn := encUnary) (encOut := encBits) fun _ => rfl).comp hi
  have hs := fst (encPair encNat encNat) encBool
  have hstep := binary_div.comp (hs.snd'.prod hs.fst')
  have hfold := foldlWith (encP := encNat) (encA := encBool) (encL := encBits) (encB := encNat)
    (par := fun p : (ℕ × ℕ) × ℕ => p.1.1) (list := fun p => List.replicate p.2 true)
    (init := fun p => p.1.2) (step := fun B acc _ => acc / B) hb hlist hx hstep
    (B := fun p => (encPair (encPair encNat encNat) encUnary p).length) .self (by
      intro p i _
      rw [List.take_replicate, quotientFold]
      have hq : (encNat (p.1.2 / p.1.1 ^ min i p.2)).length ≤ (encNat p.1.2).length := by
        simpa [Nat.size_eq_bits_len] using
          Nat.size_le_size (Nat.div_le_self p.1.2 (p.1.1 ^ min i p.2))
      exact hq.trans ((length_le_encPair_right encNat encNat p.1).trans
        (length_le_encPair_left (encPair encNat encNat) encUnary p)))
  have h := binary_mod.comp (hfold.prod hb)
  convert h using 1
  funext p
  simp only [Cslib.Radix.digit_eq_div_pow_mod, quotientFold, Function.comp_def]

end Turing.MultiTapeTM.ComputableInPolyTime
