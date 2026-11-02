/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.Nat.Bitwise

/-!
# Bits of successors, predecessors and packed fields

Incrementing a number flips bit `q` exactly when all lower bits are one, and decrementing a
positive number flips it exactly when all lower bits are zero. A number packed from fields of
fixed widths has, in each window of bits, the bits of the corresponding field.

## Main results

* `Nat.testBit_add_one_eq_xor`, `Nat.testBit_sub_one_eq_xor`: the bits of `c + 1` and `c - 1`.
* `Nat.testBit_add_four_mul`: the bits of a two-bit tag followed by a payload.
* `Nat.testBit_add_two_pow_mul_add_two_pow_mul`: the bits of three packed fields.
-/

@[expose] public section

namespace Nat

/-- Bit `q` of `c - 1`, for `1 ≤ c`: bit `q` of `c`, flipped when the lower bits of `c` are
zero. -/
theorem testBit_sub_one_eq_xor {c : ℕ} (hc : 1 ≤ c) (q : ℕ) :
    (c - 1).testBit q = (c.testBit q ^^ decide (c % 2 ^ q = 0)) := by
  induction q generalizing c with
  | zero =>
    simp only [Nat.testBit_zero, pow_zero, Nat.mod_one, decide_true, Bool.xor_true]
    rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not,
      Nat.mod_two_not_eq_one]
    omega
  | succ q ih =>
    rw [Nat.testBit_succ, Nat.testBit_succ, Nat.pow_succ', Nat.mod_mul]
    rcases Nat.even_or_odd c with ⟨d, rfl⟩ | ⟨d, rfl⟩
    · have hd : 1 ≤ d := by omega
      have h₁ : (d + d - 1) / 2 = d - 1 := by omega
      have h₂ : (d + d) / 2 = d := by omega
      have h₃ : (d + d) % 2 = 0 := by omega
      rw [h₁, h₂, ih hd, h₃]
      congr 2
      rw [Nat.zero_add, Nat.mul_eq_zero]
      simp
    · have h₁ : (2 * d + 1 - 1) / 2 = d := by omega
      have h₂ : (2 * d + 1) / 2 = d := by omega
      have h₃ : (2 * d + 1) % 2 = 1 := by omega
      rw [h₁, h₂, h₃]
      simp

/-- Bit `q` of `c + 1`: bit `q` of `c`, flipped when the lower bits of `c` are all one. -/
theorem testBit_add_one_eq_xor (c q : ℕ) :
    (c + 1).testBit q = (c.testBit q ^^ decide (c % 2 ^ q = 2 ^ q - 1)) := by
  induction q generalizing c with
  | zero =>
    simp only [Nat.testBit_zero, pow_zero, Nat.mod_one, Nat.sub_self, decide_true, Bool.xor_true]
    rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not,
      Nat.mod_two_not_eq_one]
    omega
  | succ q ih =>
    rw [Nat.testBit_succ, Nat.testBit_succ, Nat.pow_succ', Nat.mod_mul]
    have hq := Nat.one_le_two_pow (n := q)
    rcases Nat.even_or_odd c with ⟨d, rfl⟩ | ⟨d, rfl⟩
    · have h₁ : (d + d + 1) / 2 = d := by omega
      have h₂ : (d + d) / 2 = d := by omega
      have h₃ : (d + d) % 2 = 0 := by omega
      rw [h₁, h₂, h₃]
      have : ¬ (2 * (d % 2 ^ q) = 2 * 2 ^ q - 1) := by omega
      simp [this]
    · have h₁ : (2 * d + 1 + 1) / 2 = d + 1 := by omega
      have h₂ : (2 * d + 1) / 2 = d := by omega
      have h₃ : (2 * d + 1) % 2 = 1 := by omega
      rw [h₁, h₂, h₃, ih d]
      congr 2
      exact propext ⟨fun h => by omega, fun h => by omega⟩

/-- The bits of a tag and a payload. -/
theorem testBit_add_four_mul {tag : ℕ} (htag : tag < 4) (pay i : ℕ) :
    (tag + 4 * pay).testBit i = if i < 2 then tag.testBit i else pay.testBit (i - 2) := by
  rw [Nat.add_comm, show 4 = 2 ^ 2 from rfl, Nat.testBit_two_pow_mul_add _ htag]

/-- The bits of three fields of widths `s` and `cb` and a high field. -/
theorem testBit_add_two_pow_mul_add_two_pow_mul {s cb sl C Tm : ℕ} (hsl : sl < 2 ^ s)
    (hC : C < 2 ^ cb) (q : ℕ) :
    (sl + 2 ^ s * (C + 2 ^ cb * Tm)).testBit q =
      if q < s then sl.testBit q else if q < s + cb then C.testBit (q - s)
      else Tm.testBit (q - s - cb) := by
  rw [Nat.add_comm, Nat.testBit_two_pow_mul_add _ hsl, Nat.add_comm C,
    Nat.testBit_two_pow_mul_add _ hC]
  split_ifs <;> first | rfl | omega

end Nat
