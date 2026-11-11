/-
Copyright (c) 2026 Samuel Schlesinger, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Nat.Bits
public import Batteries.Data.Nat.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Fixed-width packed words

A fixed tuple of bounded words stores an initial segment of a bit stream. Reading a field
constrains its entire value, including all bits outside the specified width.

## Main definitions

* `Cslib.BitString.packRadix`: bounded fields in a common radix.
* `Cslib.BitString.packWords`: split a bit stream into a fixed tuple of words.
* `Cslib.BitString.readPackedBit`: read one bit of a fixed tuple of words by its address.
* `Cslib.BitString.readPackedField`: read a bounded-width field across word boundaries.

## Main results

* `Cslib.BitString.packRadix_field`: exact radix-field decoding.
* `Cslib.BitString.readPackedField_packWords`: exact field decoding.
* `Cslib.BitString.readPackedField_fields`: decoding fixed-width consecutive fields.
-/

@[expose] public section

namespace Cslib.BitString

open scoped BigOperators

/-- Pack a bit stream into `B` words of `h` bits each. -/
def packWords (f : ℕ → Bool) (h B : ℕ) (r : Fin B) : ℕ :=
  Nat.ofBits (fun b : Fin h => f (r.val * h + b.val))

/-- Each packed word is below `2 ^ h`. -/
theorem packWords_lt (f : ℕ → Bool) (h B : ℕ) (r : Fin B) :
    packWords f h B r < 2 ^ h := Nat.ofBits_lt_two_pow _

/-- Read one bit of a fixed tuple; unused addresses are false. -/
def readPackedBit {B : ℕ} (h : ℕ) (w : Fin B → ℕ) (a : ℕ) : Bool :=
  decide (∃ r : Fin B, ∃ b : Fin h, r.val * h + b.val = a ∧ (w r).testBit b.val = true)

/-- Decode exactly `s` bits starting at address `a`, with every higher bit zero. -/
def readPackedField {B : ℕ} (h : ℕ) (w : Fin B → ℕ) (a s : ℕ) : ℕ :=
  Nat.ofBits (fun b : Fin s => readPackedBit h w (a + b.val))

/-- A field of width `s` is below `2 ^ s`. -/
theorem readPackedField_lt {B : ℕ} (h : ℕ) (w : Fin B → ℕ) (a s : ℕ) :
    readPackedField h w a s < 2 ^ s := Nat.ofBits_lt_two_pow _

/-- Bit `b` of the field of width `s` at address `a` is set exactly when `b < s` and the packed
bit at address `a + b`, bit `t` of word `r` with `r * h + t = a + b`, is set. -/
theorem readPackedField_testBit {B : ℕ} (h : ℕ) (w : Fin B → ℕ) (a s b : ℕ) :
    (readPackedField h w a s).testBit b = true ↔
      b < s ∧ ∃ r : Fin B, ∃ t : Fin h, r.val * h + t.val = a + b ∧
        (w r).testBit t.val = true := by
  by_cases hb : b < s <;> simp [readPackedField, Nat.testBit_ofBits, hb, readPackedBit]

/-- Every bit below the total capacity is recovered from the packed tuple. -/
theorem readPackedBit_packWords (f : ℕ → Bool) {h B a : ℕ} (ha : a < B * h) :
    readPackedBit h (packWords f h B) a = f a := by
  apply Bool.eq_iff_iff.mpr
  simp only [readPackedBit, decide_eq_true_eq]
  constructor
  · rintro ⟨r, b, he, hb⟩
    simpa only [packWords, Nat.testBit_ofBits_lt _ _ b.isLt, he] using hb
  · intro hf
    have hh : 0 < h := by nlinarith
    refine ⟨⟨a / h, (Nat.div_lt_iff_lt_mul hh).mpr ha⟩,
      ⟨a % h, Nat.mod_lt _ hh⟩, ?_, ?_⟩
    · simpa only [Nat.mul_comm] using Nat.div_add_mod a h
    · simpa only [packWords, Nat.testBit_ofBits_lt _ _ (Nat.mod_lt a hh),
        Nat.mul_comm (a / h), Nat.div_add_mod] using hf

/-- A fitting field is recovered exactly, including high zero bits. -/
theorem readPackedField_packWords (f : ℕ → Bool) {h B a s z : ℕ}
    (ha : a + s ≤ B * h) (hz : z < 2 ^ s) (hf : ∀ b < s, f (a + b) = z.testBit b) :
    readPackedField h (packWords f h B) a s = z := by
  apply Nat.eq_of_testBit_eq
  intro b
  by_cases hb : b < s
  · rw [readPackedField, Nat.testBit_ofBits_lt _ _ hb, readPackedBit_packWords f (by lia)]
    exact hf b hb
  · rw [readPackedField, Nat.testBit_ofBits_ge _ _ (by lia)]
    exact (Nat.testBit_lt_two_pow (lt_of_lt_of_le hz
      (Nat.pow_le_pow_right (by decide) (show s ≤ b by lia)))).symm

/-- Consecutive fixed-width fields can be packed and decoded without overlap. -/
theorem readPackedField_fields (v : ℕ → ℕ) {h B q s : ℕ} (hs : 0 < s)
    (ha : q * s + s ≤ B * h) (hv : v q < 2 ^ s) :
    readPackedField h (packWords (fun a => (v (a / s)).testBit (a % s)) h B)
      (q * s) s = v q := by
  apply readPackedField_packWords _ ha hv
  intro b hb
  rw [Nat.mul_comm q s, Nat.mul_add_div hs, Nat.div_eq_of_lt hb, Nat.add_zero,
    Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hb]

/-- Pack `n` radix-`base` fields, least significant field first. -/
def packRadix (base n : ℕ) (f : ℕ → ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, f i * base ^ i

private theorem packRadix_succ (base n : ℕ) (f : ℕ → ℕ) :
    packRadix base (n + 1) f = f 0 + base * packRadix base n (fun i => f (i + 1)) := by
  simp only [packRadix, Finset.sum_range_succ', pow_succ, pow_zero, mul_one,
    Finset.mul_sum]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Bounded fields fit the total radix capacity, including the empty tuple. -/
theorem packRadix_lt {base n : ℕ} (f : ℕ → ℕ)
    (hf : ∀ i < n, f i < base) : packRadix base n f < base ^ n := by
  induction n with
  | zero => simp [packRadix]
  | succ n ih =>
    rw [packRadix, Finset.sum_range_succ]
    have hp := ih (fun i hi => hf i (by omega))
    have hn := hf n (by omega)
    rw [pow_succ]
    change packRadix base n f + f n * base ^ n < base ^ n * base
    nlinarith

/-- Reading a radix field recovers its entire value, with no contributions from other fields. -/
theorem packRadix_field {base n i : ℕ} (hb : 0 < base) (f : ℕ → ℕ)
    (hf : ∀ j < n, f j < base) (hi : i < n) :
    packRadix base n f / base ^ i % base = f i := by
  induction n generalizing i f with
  | zero => omega
  | succ n ih =>
    rw [packRadix_succ]
    have h0 := hf 0 (by omega)
    cases i with
    | zero => simp [Nat.add_mod, Nat.mod_eq_of_lt h0]
    | succ i =>
      rw [pow_succ, Nat.mul_comm (base ^ i) base, ← Nat.div_div_eq_div_mul,
        Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt h0, zero_add]
      exact ih _ (fun j hj => hf (j + 1) (by omega)) (by omega)

end Cslib.BitString
