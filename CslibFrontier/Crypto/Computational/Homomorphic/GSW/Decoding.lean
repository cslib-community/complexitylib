/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.IntervalCases

/-!
# Scalar decoding for GSW ciphertexts

For modulus `2 ^ w`, a bit is represented by zero or `2 ^ (w - 1)`, with an integer error.
The decoder selects the half-open middle half of the canonical residue interval. Thus the
lower quarter boundary decodes to `true` and the upper quarter boundary to `false`.
Correctness uses a strict error bound, which excludes both ties and handles negative errors
by modular wraparound.

## Main definitions

* `Cslib.Crypto.Homomorphic.GSW.decode`: the scalar bit decoder.

## Main results

* `Cslib.Crypto.Homomorphic.GSW.decode_eq_of_error`: errors of magnitude strictly below
  one quarter of the modulus preserve the encoded bit.
* `Cslib.Crypto.Homomorphic.GSW.decode_eq_xor_highBits`: for width at least two, decoding
  is exclusive-or of the two highest bits of the canonical residue, on every input.

## References

* [C. Gentry, A. Sahai, B. Waters, *Homomorphic Encryption from Learning with Errors:
  Conceptually-Simpler, Asymptotically-Faster, Attribute-Based*][GentrySahaiWaters2013],
  Section 3.1.
-/

@[expose] public section

namespace Cslib.Crypto.Homomorphic.GSW

/-- Decode the half-open middle half of the canonical residue interval as `true`. -/
def decode (w : ℕ) (x : ZMod (2 ^ w)) : Bool :=
  decide (2 ^ w ≤ 4 * x.val ∧ 4 * x.val < 3 * 2 ^ w)

@[simp] theorem decode_eq_true_iff (w : ℕ) (x : ZMod (2 ^ w)) :
    decode w x = true ↔ 2 ^ w ≤ 4 * x.val ∧ 4 * x.val < 3 * 2 ^ w := by
  simp [decode]

/-- Width zero has only the zero residue, which decodes to `false`. -/
@[simp] theorem decode_zero (x : ZMod (2 ^ 0)) : decode 0 x = false := by
  have hx : x.val = 0 := by
    have h : x.val < 1 := ZMod.val_lt x
    omega
  simp [decode, hx]

/-- At width one, the single bit is already the decoded message. -/
theorem decode_one (x : ZMod (2 ^ 1)) : decode 1 x = x.val.testBit 0 := by
  have hx : x.val < 2 := ZMod.val_lt x
  simp only [decode, pow_one, Nat.testBit_eq_decide_div_mod_eq, pow_zero, Nat.div_one,
    Nat.mod_eq_of_lt hx]
  congr 1
  apply propext
  omega

/-- The half-open middle interval is exactly the set where the two highest bits differ.
This identity holds on every residue, including both quarter-boundary ties. -/
theorem decode_eq_xor_highBits {w : ℕ} (hw : 2 ≤ w) (x : ZMod (2 ^ w)) :
    decode w x = (x.val.testBit (w - 1) ^^ x.val.testBit (w - 2)) := by
  obtain ⟨k, rfl⟩ : ∃ k, w = k + 2 := ⟨w - 2, by omega⟩
  have hp : 0 < 2 ^ k := Nat.two_pow_pos k
  have hq : 2 ^ (k + 2) = 4 * 2 ^ k := by simp [pow_add, Nat.mul_comm]
  have hh : 2 ^ (k + 2 - 1) = 2 ^ k * 2 := by
    rw [show k + 2 - 1 = k + 1 by omega, pow_succ]
  have hx : x.val / 2 ^ k < 4 := (Nat.div_lt_iff_lt_mul hp).mpr (by
    have := ZMod.val_lt x
    omega)
  have hlo : 1 ≤ x.val / 2 ^ k ↔ 2 ^ k ≤ x.val := by
    simpa only [one_mul] using (Nat.le_div_iff_mul_le hp :
      1 ≤ x.val / 2 ^ k ↔ 1 * 2 ^ k ≤ x.val)
  have hhi : x.val / 2 ^ k < 3 ↔ x.val < 3 * 2 ^ k := Nat.div_lt_iff_lt_mul hp
  have hdecode : decode (k + 2) x = decide (1 ≤ x.val / 2 ^ k ∧ x.val / 2 ^ k < 3) := by
    simp only [decode, hq, hlo, hhi]
    congr 1
    apply propext
    omega
  rw [hdecode, Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq,
    hh, Nat.add_sub_cancel, ← Nat.div_div_eq_div_mul]
  interval_cases h : x.val / 2 ^ k <;> simp

/-- Decoding recovers a bit whenever its integer error has magnitude strictly below one
quarter of the modulus. The strict inequality excludes the decoder's asymmetric ties. -/
theorem decode_eq_of_error {w : ℕ} (hw : 0 < w) (μ : Bool) (error : ℤ)
    (herror : 4 * error.natAbs < 2 ^ w) :
    decode w (((μ.toNat : ℤ) * 2 ^ (w - 1) + error : ℤ) : ZMod (2 ^ w)) = μ := by
  have hhalf : 2 ^ w = 2 * 2 ^ (w - 1) := by
    calc
      2 ^ w = 2 ^ ((w - 1) + 1) := by rw [Nat.sub_add_cancel hw]
      _ = 2 * 2 ^ (w - 1) := by rw [pow_succ, Nat.mul_comm]
  have hhalfInt : (2 ^ w : ℕ) = (2 : ℤ) * 2 ^ (w - 1) := by
    exact_mod_cast hhalf
  have hbound : 4 * (error.natAbs : ℤ) < (2 ^ w : ℕ) := by
    exact_mod_cast herror
  have hupper : error ≤ (error.natAbs : ℤ) := Int.le_natAbs
  have hlower : -(error.natAbs : ℤ) ≤ error := by
    have := Int.le_natAbs (a := -error)
    simpa only [Int.natAbs_neg, neg_neg] using neg_le_neg this
  have hmod : ∀ x : ℤ, 0 ≤ x → x < (2 ^ w : ℕ) →
      (((x : ZMod (2 ^ w)).val : ℕ) : ℤ) = x := by
    intro x hx hx'
    rw [ZMod.val_intCast, Int.emod_eq_of_lt hx hx']
  cases μ
  · simp only [Bool.toNat_false, Nat.cast_zero, zero_mul, zero_add]
    by_cases he : 0 ≤ error
    · have hval := hmod error he (by omega)
      simp only [decode, decide_eq_false_iff_not]
      omega
    · have hval := hmod (error + (2 ^ w : ℕ)) (by omega) (by omega)
      rw [ZMod.val_intCast, Int.add_emod_right, ← ZMod.val_intCast] at hval
      simp only [decode, decide_eq_false_iff_not]
      omega
  · simp only [Bool.toNat_true, Nat.cast_one, one_mul]
    have hval := hmod (2 ^ (w - 1) + error) (by omega) (by omega)
    rw [decode_eq_true_iff]
    omega

end Cslib.Crypto.Homomorphic.GSW
