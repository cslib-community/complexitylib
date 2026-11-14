/-
Copyright (c) 2026 Karn Seth, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.ZMod.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.IntervalCases

/-!
# Scalar bit encoding, decoding, and binary noise bounds modulo `2 ^ w`

For modulus `2 ^ w`, a bit `μ` is encoded as `μ * 2 ^ (w - 1)` (`encodeBit`) and decoded by
selecting the half-open middle half `[2 ^ w / 4, 3 * 2 ^ w / 4)` of the canonical residue
interval (`decodeResidue`, `decode`). Correctness holds whenever the additive integer error has
magnitude strictly below one quarter of `2 ^ w` (`decode_eq_of_error`). This module also hosts the
common magnitude bound `natAbs_binarySum_le` for integer subset sums over Boolean coefficients.

## Main definitions

* `Cslib.Crypto.LWE.encodeBit`: half-modulus encoding `false ↦ 0`, `true ↦ 2 ^ (w - 1)`.
* `Cslib.Crypto.LWE.decodeResidue`: scalar bit decoder on natural residue representatives.
* `Cslib.Crypto.LWE.decode`: scalar bit decoder over `ZMod (2 ^ w)`.

## Main results

* `Cslib.Crypto.LWE.computableInPolyTime_decodeResidue`: polynomial-time rounding of binary residue
  representatives for unary width `w`.
* `Cslib.Crypto.LWE.decode_eq_of_error`: errors of magnitude strictly below one quarter of the
  modulus preserve the encoded bit.
* `Cslib.Crypto.LWE.decode_eq_xor_highBits`: for width at least two, decoding is exclusive-or of
  the two highest bits of the canonical residue, on every input.
* `Cslib.Crypto.LWE.natAbs_binarySum_le_sum`, `Cslib.Crypto.LWE.natAbs_binarySum_le`: integer
  noise bounds for binary subset sums shared across GSW and Regev encryption.

## References

* [O. Regev, *On lattices, learning with errors, random linear codes, and cryptography*]
  [Regev2009], Section 5.
* [C. Gentry, A. Sahai and B. Waters, *Homomorphic Encryption from Learning with Errors:
  Conceptually-Simpler, Asymptotically-Faster, Attribute-Based*][GentrySahaiWaters2013],
  Section 3.1.
-/

@[expose] public section

namespace Cslib.Crypto.LWE

open Turing.MultiTapeTM

/-- Half-modulus encoding: `false ↦ 0` and `true ↦ 2 ^ (w - 1)`. -/
def encodeBit (w : ℕ) (μ : Bool) : ZMod (2 ^ w) :=
  (μ.toNat : ZMod (2 ^ w)) * 2 ^ (w - 1)

/-- Decode a natural residue representative modulo `2 ^ w` by selecting the half-open middle half
`[2 ^ w / 4, 3 * 2 ^ w / 4)` of `[0, 2 ^ w)`. -/
def decodeResidue (w value : ℕ) : Bool :=
  decide (2 ^ w ≤ 4 * value ∧ 4 * value < 3 * 2 ^ w)

/-- Characterization of `decodeResidue` as the middle half of `[0, 2 ^ w)`. -/
@[simp] theorem decodeResidue_eq_true_iff (w value : ℕ) :
    decodeResidue w value = true ↔ 2 ^ w ≤ 4 * value ∧ 4 * value < 3 * 2 ^ w := by
  simp [decodeResidue]

/-- At width zero, residue zero decodes to `false`. -/
@[simp] theorem decodeResidue_zero_zero : decodeResidue 0 0 = false := rfl

/-- Rounding a natural residue representative `value` modulo `2 ^ w` via `decodeResidue` is
computable in polynomial time for unary `w` and binary `value`. -/
@[fun_prop]
theorem computableInPolyTime_decodeResidue {α : Type} {input : α ↪ List Bool}
    {w value : α → ℕ}
    (hw : ComputableInPolyTime w input encUnary)
    (hvalue : ComputableInPolyTime value input encNat) :
    ComputableInPolyTime (fun a => decodeResidue (w a) (value a)) input encBool := by
  have hq := ComputableInPolyTime.binary_pow' (ComputableInPolyTime.const 2) hw
  have hfour := ComputableInPolyTime.binary_mul' (ComputableInPolyTime.const 4) hvalue
  exact ComputableInPolyTime.decide_and
    (ComputableInPolyTime.binary_le' hq hfour)
    (ComputableInPolyTime.binary_lt' hfour
      (ComputableInPolyTime.binary_mul' (ComputableInPolyTime.const 3) hq))

/-- Decode the half-open middle half of the canonical residue interval as `true`. -/
def decode (w : ℕ) (x : ZMod (2 ^ w)) : Bool :=
  decodeResidue w x.val

/-- Characterization of decoding to `true` as the middle half of the canonical residue interval. -/
@[simp] theorem decode_eq_true_iff (w : ℕ) (x : ZMod (2 ^ w)) :
    decode w x = true ↔ 2 ^ w ≤ 4 * x.val ∧ 4 * x.val < 3 * 2 ^ w := by
  simp [decode, decodeResidue]

/-- Width zero has only the zero residue, which decodes to `false`. -/
@[simp] theorem decode_zero (x : ZMod (2 ^ 0)) : decode 0 x = false := by
  have hx : x.val = 0 := by
    have h : x.val < 1 := ZMod.val_lt x
    omega
  simp [decode, decodeResidue, hx]

/-- At width one, the single bit is already the decoded message. -/
theorem decode_one (x : ZMod (2 ^ 1)) : decode 1 x = x.val.testBit 0 := by
  have hx : x.val < 2 := ZMod.val_lt x
  simp only [decode, decodeResidue, pow_one, Nat.testBit_eq_decide_div_mod_eq, pow_zero,
    Nat.div_one, Nat.mod_eq_of_lt hx]
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
    simp only [decode, decodeResidue, hq, hlo, hhi]
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
      simp only [decode, decodeResidue, decide_eq_false_iff_not]
      omega
    · have hval := hmod (error + (2 ^ w : ℕ)) (by omega) (by omega)
      rw [ZMod.val_intCast, Int.add_emod_right, ← ZMod.val_intCast] at hval
      simp only [decode, decodeResidue, decide_eq_false_iff_not]
      omega
  · simp only [Bool.toNat_true, Nat.cast_one, one_mul]
    have hval := hmod (2 ^ (w - 1) + error) (by omega) (by omega)
    rw [decode_eq_true_iff]
    omega

/-- The magnitude of a binary-selected integer sum is at most the sum of term magnitudes. -/
theorem natAbs_binarySum_le_sum {κ : Type*} [Fintype κ] (bits : κ → Bool) (error : κ → ℤ) :
    (∑ j, ((bits j).toNat : ℤ) * error j).natAbs ≤ ∑ j, (error j).natAbs := by
  refine (Int.natAbs_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  cases bits j <;> simp

/-- Errors bounded uniformly by `bound` yield a binary-selected sum of magnitude at most
`|κ| * bound`. -/
theorem natAbs_binarySum_le {κ : Type*} [Fintype κ] (bits : κ → Bool) (error : κ → ℤ)
    {bound : ℕ} (herror : ∀ j, (error j).natAbs ≤ bound) :
    (∑ j, ((bits j).toNat : ℤ) * error j).natAbs ≤ Fintype.card κ * bound := by
  refine (natAbs_binarySum_le_sum bits error).trans ?_
  simpa using Finset.sum_le_sum (s := Finset.univ) (fun j _ => herror j)

end Cslib.Crypto.LWE
