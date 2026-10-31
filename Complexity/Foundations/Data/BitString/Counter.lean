/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Bits

/-!
# A binary counter

A word of fixed length is a counter, read least significant bit first (`Cslib.BitString.lsbValue`).
Increment (`Cslib.BitString.increment`) flips the trailing ones of the least significant end and
the first zero, discarding the final carry, so it keeps the length and wraps around from the word
of ones to the word of zeros. Counting from the word of `m` zeros enumerates the words of length
`m` in order of value (`Cslib.BitString.iterate_increment`), each reached at its value
(`Cslib.BitString.iterate_increment_lsbValue`). Exhaustive searches in polynomial space enumerate
their candidates in this way, storing only the current one.

## Main definitions

* `Cslib.BitString.increment`: binary increment, least significant bit first.
* `Cslib.BitString.lsbValue`: the value of a word, least significant bit first.

## Main results

* `Cslib.BitString.lsbValue_increment`: increment adds one below the largest value.
* `Cslib.BitString.lsbValue_injective`: words of the same length are determined by their values.
* `Cslib.BitString.iterate_increment`, `Cslib.BitString.iterate_increment_lsbValue`: counting from
  zero enumerates the words of a length.
* `Cslib.BitString.lsbValue_eq_foldr_bit`: `lsbValue` is a right fold of `Nat.bit`.
* `Cslib.BitString.testBit_lsbValue`: binary digit `i` of `lsbValue w` is the bit `w[i]`.
-/

@[expose] public section

namespace Cslib.BitString

/-- Binary increment, least significant bit first, discarding the final carry. -/
def increment : List Bool → List Bool
  | [] => []
  | false :: w => true :: w
  | true :: w => false :: increment w

/-- The value of a word in binary, least significant bit first. -/
def lsbValue : List Bool → ℕ
  | [] => 0
  | b :: w => b.toNat + 2 * lsbValue w

/-- Increment keeps the length. -/
@[simp] theorem length_increment : ∀ w, (increment w).length = w.length
  | [] => rfl
  | false :: _ => rfl
  | true :: w => by simp [increment, length_increment w]

/-- Iterated increment keeps the length. -/
@[simp] theorem length_iterate_increment (j : ℕ) (w : List Bool) :
    (increment^[j] w).length = w.length := by
  induction j generalizing w with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply, ih, length_increment]

/-- A word of length `m` has value below `2 ^ m`. -/
theorem lsbValue_lt : ∀ w, lsbValue w < 2 ^ w.length
  | [] => by simp [lsbValue]
  | b :: w => by
    have := lsbValue_lt w
    have := Bool.toNat_le b
    simp only [lsbValue, List.length_cons]
    lia

/-- Below the largest value, increment adds one. -/
theorem lsbValue_increment : ∀ w, lsbValue w + 1 < 2 ^ w.length →
    lsbValue (increment w) = lsbValue w + 1
  | [] => by simp [lsbValue]
  | false :: w => fun _ => by
    simp only [increment, lsbValue, Bool.toNat_true, Bool.toNat_false]
    lia
  | true :: w => fun h => by
    simp only [lsbValue, List.length_cons, Bool.toNat_true, increment, Bool.toNat_false] at h ⊢
    rw [lsbValue_increment w (by lia)]
    lia

/-- Words of the same length are determined by their values. -/
theorem lsbValue_injective : ∀ {w w' : List Bool}, w.length = w'.length →
    lsbValue w = lsbValue w' → w = w'
  | [], [], _, _ => rfl
  | b :: w, b' :: w', hl, hv => by
    simp only [lsbValue] at hv
    have hb : b = b' := by
      cases b <;> cases b' <;>
        first | rfl | (simp only [Bool.toNat_false, Bool.toNat_true] at hv; lia)
    subst hb
    exact congrArg _ (lsbValue_injective (by simpa using hl) (by lia))

/-- The word of zeros has value `0`. -/
@[simp] theorem lsbValue_replicate_false : ∀ m, lsbValue (List.replicate m false) = 0
  | 0 => rfl
  | m + 1 => by simp [List.replicate_succ, lsbValue, lsbValue_replicate_false m]

/-- The word of ones has the largest value. -/
theorem lsbValue_replicate_true : ∀ m, lsbValue (List.replicate m true) + 1 = 2 ^ m
  | 0 => rfl
  | m + 1 => by
    have := lsbValue_replicate_true m
    simp only [List.replicate_succ, lsbValue, Bool.toNat_true]
    lia

/-- A word with a `true` has a positive value. -/
theorem lsbValue_pos_of_true_mem : ∀ {u : List Bool}, true ∈ u → 0 < lsbValue u
  | b :: u, h => by
    rcases List.mem_cons.mp h with rfl | h
    · simp only [lsbValue, Bool.toNat_true]
      lia
    · have := lsbValue_pos_of_true_mem h
      simp only [lsbValue]
      lia

/-- A word without `true` has value `0`. -/
theorem lsbValue_eq_zero_of_true_not_mem : ∀ {u : List Bool}, true ∉ u → lsbValue u = 0
  | [], _ => rfl
  | b :: u, h => by
    simp only [List.mem_cons, not_or] at h
    have hb : b = false := by simpa using h.1
    subst hb
    simp [lsbValue, lsbValue_eq_zero_of_true_not_mem h.2]

/-- **The counter counts**: the `j`-th iterate from the word of `m` zeros has value `j`, for
`j < 2 ^ m`. -/
theorem iterate_increment (m : ℕ) : ∀ j < 2 ^ m,
    lsbValue (increment^[j] (List.replicate m false)) = j ∧
      (increment^[j] (List.replicate m false)).length = m
  | 0, _ => ⟨lsbValue_replicate_false m, List.length_replicate⟩
  | j + 1, hj => by
    obtain ⟨hv, hl⟩ := iterate_increment m j (by lia)
    rw [Function.iterate_succ_apply', length_increment,
      lsbValue_increment _ (by rw [hv, hl]; lia), hv]
    exact ⟨rfl, hl⟩

/-- **Every word is reached by counting up to its value.** -/
theorem iterate_increment_lsbValue (u : List Bool) :
    increment^[lsbValue u] (List.replicate u.length false) = u :=
  let h := iterate_increment u.length (lsbValue u) (lsbValue_lt u)
  lsbValue_injective h.2 h.1

/-- `lsbValue` is a right fold of `Nat.bit`. -/
theorem lsbValue_eq_foldr_bit (w : List Bool) : lsbValue w = w.foldr Nat.bit 0 := by
  induction w with
  | nil => rfl
  | cons b w ih => rw [lsbValue, List.foldr_cons, ← ih, Nat.bit_val, Nat.add_comm]

/-- Binary digit `i` of the value of a word is its bit `i`, or `false` past its end. -/
@[simp] theorem testBit_lsbValue : ∀ (w : List Bool) (i : ℕ),
    (lsbValue w).testBit i = w.getD i false
  | [], _ => by simp [lsbValue]
  | b :: w, i => by
    rw [lsbValue_eq_foldr_bit, List.foldr_cons, ← lsbValue_eq_foldr_bit]
    cases i with
    | zero => simp
    | succ i => simp [Nat.testBit_bit_succ, testBit_lsbValue w i]

end Cslib.BitString
