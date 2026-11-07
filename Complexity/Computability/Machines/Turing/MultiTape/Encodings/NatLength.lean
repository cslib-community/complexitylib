/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Binary lengths of natural numbers

The binary encoding `encNat` of a number has `Nat.size` digits, so numbers below `2 ^ p` have at
most `p` digits. Numbers at most `N` have at most `log₂ N + 1` digits, and numbers at most
`(N + 1) ^ d` at most `(d + 1) * (log₂ N + 1)`: counters bounded by a polynomial in the length of
the input are stored in logarithmic space.

## Main results

* `Turing.MultiTapeTM.length_encNat_le_of_lt_two_pow`: numbers below `2 ^ p` have at most `p`
  digits.
* `Turing.MultiTapeTM.length_encNat_le_log2`: numbers at most `N` have at most `log₂ N + 1`
  digits.
* `Turing.MultiTapeTM.length_encNat_le_log2_add_two`: numbers at most `N + 1` have at most
  `log₂ N + 2` digits.
* `Turing.MultiTapeTM.length_encNat_le_of_le_pow`: numbers at most `(N + 1) ^ d` have at most
  `(d + 1) * (log₂ N + 1)` digits.

* `Turing.MultiTapeTM.length_encNat_le_of_le_mul_pow`: the corresponding bound with a
  constant coefficient.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Section 8.4][Sipser2013]
-/

@[expose] public section

namespace Turing.MultiTapeTM

/-- A number below `2 ^ p` has at most `p` binary digits. -/
theorem length_encNat_le_of_lt_two_pow {a p : ℕ} (h : a < 2 ^ p) : (encNat a).length ≤ p := by
  rw [encNat_apply, Nat.size_eq_bits_len]
  exact Nat.size_le.mpr h

/-- The binary length of a number at most `N` is at most `log₂ N + 1`. -/
theorem length_encNat_le_log2 {j N : ℕ} (h : j ≤ N) : (encNat j).length ≤ Nat.log2 N + 1 := by
  rw [encNat_apply, Nat.size_eq_bits_len, Nat.size_le]
  exact lt_of_le_of_lt h Nat.lt_log2_self

/-- The binary length of a number at most `N + 1` is at most `log₂ N + 2`. -/
theorem length_encNat_le_log2_add_two {j N : ℕ} (h : j ≤ N + 1) :
    (encNat j).length ≤ Nat.log2 N + 2 := by
  rw [encNat_apply, Nat.size_eq_bits_len, Nat.size_le]
  have := Nat.lt_log2_self (n := N)
  rw [pow_succ]
  omega

/-- A number at most `(N + 1) ^ d` has at most `(d + 1) * (log₂ N + 1)` binary digits. -/
theorem length_encNat_le_of_le_pow {r N d : ℕ} (h : r ≤ (N + 1) ^ d) :
    (encNat r).length ≤ (d + 1) * (Nat.log2 N + 1) := by
  rw [encNat_apply, Nat.size_eq_bits_len, Nat.size_le]
  have h₁ : N + 1 ≤ 2 ^ (Nat.log2 N + 1) := Nat.lt_log2_self
  calc r ≤ (N + 1) ^ d := h
    _ ≤ (2 ^ (Nat.log2 N + 1)) ^ d := Nat.pow_le_pow_left h₁ d
    _ = 2 ^ (d * (Nat.log2 N + 1)) := by rw [← pow_mul, Nat.mul_comm]
    _ < 2 ^ ((d + 1) * (Nat.log2 N + 1)) :=
      Nat.pow_lt_pow_right (by norm_num) (by nlinarith)

/-- A number bounded by a constant times a fixed power has logarithmic binary length. -/
theorem length_encNat_le_of_le_mul_pow {M A D L : ℕ} (h : M ≤ A * (L + 1) ^ D) :
    (encNat M).length ≤ (Nat.size A + 2 * D + 1) * (Nat.log2 L + 1) := by
  have hp := length_encNat_le_of_le_pow (r := (L + 1) ^ D) (N := L) (d := D) le_rfl
  rw [encNat_apply, Nat.size_eq_bits_len] at hp ⊢
  have hM : M < 2 ^ (Nat.size A + (D + 1) * (Nat.log2 L + 1)) := by
    calc
      M ≤ A * (L + 1) ^ D := h
      _ < 2 ^ Nat.size A * 2 ^ ((D + 1) * (Nat.log2 L + 1)) :=
        Nat.mul_lt_mul'' (Nat.lt_size_self A) (Nat.size_le.mp hp)
      _ = _ := (pow_add ..).symm
  exact (Nat.size_le.mpr hM).trans (by nlinarith)

end Turing.MultiTapeTM
