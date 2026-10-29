/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Karn Seth
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Data/Nat/Bits.lean`)

public import Complexity.Init
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Nat.Bits
public import Mathlib.Data.Nat.Size
import Mathlib.Data.List.OfFn

/-!
# Recovering a natural number from its binary digits

The digits returned by `Nat.bits` are least significant first. Folding `Nat.bit` from the right
with initial value zero reconstructs the original number.

## Main results

* `Nat.bits_eq_nil_iff`: a natural has no binary digits exactly when it is zero.
* `Nat.foldr_bit_bits`: folding `Nat.bit` over the binary representation of `n` gives `n`.
* `Nat.foldr_bit_lt`, `Nat.foldr_bit_testBit`: fixed-width little-endian reconstruction.
* `Nat.foldr_bit_one_ne_zero`, `Nat.bits_foldr_bit_one`, `Nat.foldr_bit_one_lt`: reconstruction
  with base value `1`, producing a positive number whose binary digits end in `true`.
* `Nat.foldr_bit_ofFn`: reconstruction is the sum of the digits' binary place values.
* `Nat.size_div_two_add_one`: halving a positive number removes one binary digit.
-/

@[expose] public section

open scoped BigOperators

/-- The binary digit list of `n` is empty if and only if `n = 0`. -/
theorem Nat.bits_eq_nil_iff {n : ℕ} : n.bits = [] ↔ n = 0 := by
  rw [← List.length_eq_zero_iff, Nat.size_eq_bits_len, Nat.size_eq_zero]

/-- Reconstructing a finite little-endian word sums the digits' binary place values. -/
theorem Nat.foldr_bit_ofFn {w : ℕ} (bits : Fin w → Bool) :
    (List.ofFn bits).foldr Nat.bit 0 = ∑ k : Fin w, (bits k).toNat * 2 ^ k.val := by
  induction w with
  | zero => simp
  | succ w ih =>
    rw [List.ofFn_succ, List.foldr_cons, ih]
    simp only [Fin.sum_univ_succ, Fin.val_zero, pow_zero, mul_one, Fin.val_succ,
      pow_succ, Nat.bit_val, ← Nat.mul_assoc, ← Finset.sum_mul]
    omega

/-- Folding `Nat.bit` over the binary representation of `n` gives back `n`. -/
@[simp]
theorem Nat.foldr_bit_bits (n : ℕ) : n.bits.foldr Nat.bit 0 = n := by
  induction n using Nat.binaryRec' with
  | zero => simp
  | bit b n h ih => rw [Nat.bits_append_bit n b h, List.foldr_cons, ih]

/-- A little-endian word represents a natural below the power of two given by its length. -/
theorem Nat.foldr_bit_lt (l : List Bool) : l.foldr Nat.bit 0 < 2 ^ l.length := by
  induction l with
  | nil => simp
  | cons b l ih =>
    simp only [List.foldr_cons, Nat.bit_val, List.length_cons, Nat.pow_succ]
    cases b <;> simp only [Bool.toNat_true, Bool.toNat_false] <;> lia

/-- Folding `Nat.bit` with base `1` over any word gives a positive number. -/
theorem Nat.foldr_bit_one_ne_zero (w : List Bool) : w.foldr Nat.bit 1 ≠ 0 := by
  induction w with
  | nil => simp
  | cons b w ih => exact Nat.bit_ne_zero b ih

/-- Folding `Nat.bit` with base `1` appends `true` to the binary representation. -/
theorem Nat.bits_foldr_bit_one (w : List Bool) : (w.foldr Nat.bit 1).bits = w ++ [true] := by
  induction w with
  | nil => simp
  | cons b w ih =>
    rw [List.foldr_cons,
      Nat.bits_append_bit _ _ fun h => absurd h (Nat.foldr_bit_one_ne_zero w), ih,
      List.cons_append]

/-- Folding `Nat.bit` with base `1` produces a number strictly below `2 ^ (|w| + 1)`. -/
theorem Nat.foldr_bit_one_lt (w : List Bool) : w.foldr Nat.bit 1 < 2 ^ (w.length + 1) := by
  induction w with
  | nil => simp
  | cons b w ih =>
    rw [List.foldr_cons, Nat.bit_val, List.length_cons, pow_succ]
    cases b <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega

/-- Reading enough low-order digits recovers the natural, including its leading zero digits. -/
theorem Nat.foldr_bit_testBit {n K : ℕ} (h : n.size ≤ K) :
    ((List.range K).map n.testBit).foldr Nat.bit 0 = n := by
  induction K generalizing n with
  | zero =>
    simp only [List.range_zero, List.map_nil, List.foldr_nil]
    exact (Nat.size_eq_zero.1 (Nat.le_zero.1 h)).symm
  | succ K ih =>
    have hn : (n / 2).size ≤ K := by
      have := Nat.size_le.1 h
      rw [Nat.pow_succ] at this
      exact Nat.size_le.2 (by lia)
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, List.foldr_cons]
    have hmap : n.testBit ∘ Nat.succ = (n / 2).testBit := funext fun i => Nat.testBit_succ n i
    rw [hmap, ih hn, ← Nat.shiftRight_one, Nat.bit_testBit_zero_shiftRight_one]

/-- Halving a positive number removes one binary digit. -/
theorem Nat.size_div_two_add_one {n : ℕ} (hn : n ≠ 0) : Nat.size (n / 2) + 1 = Nat.size n := by
  have hpos := Nat.size_pos.2 (Nat.pos_of_ne_zero hn)
  rw [← Nat.size_eq_bits_len, ← Nat.size_eq_bits_len, ← Nat.div2_val, Nat.div2_bits_eq_tail,
    List.length_tail]
  rw [← Nat.size_eq_bits_len] at hpos
  omega
