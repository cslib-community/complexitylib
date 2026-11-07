/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.FastContractionSchedule

/-!
# Polynomially many residues in the contraction modulus

The modulus already used by the contraction machine has degree
`2 * 3 ^ ⌊log₂ (4 ⌊log₂ m⌋ + 2)⌋`. For every fixed `d`, its residue field eventually has at least
`(m + 1) ^ d` elements. The explicit sufficient threshold `2 ^ (2 ^ d)` is intentionally coarse:
it is used only to bound a finite fallback branch by a constant depending on `d`.

This observation lets the same contraction machine interpolate every fixed polynomial
truncation order. It does not change the modulus or require a larger extension field.

## Main results

* `FastContraction.mul_log_add_one_le_length_modulus`: eventually the degree exceeds any fixed
  multiple of `⌊log₂ m⌋ + 1`.
* `FastContraction.pow_le_card_modulus`: eventually every fixed power of `m + 1` fits in the
  residue field.
-/

public section

namespace Cslib.Circuits.Frontier.FastContraction

private theorem mul_two_pow_le_two_mul_three_pow (t : ℕ) :
    (t + 2) * 2 ^ t ≤ 2 * 3 ^ t := by
  induction t with
  | zero => norm_num
  | succ t ih =>
    have h : 2 * (t + 3) ≤ 3 * (t + 2) := by omega
    calc (t + 1 + 2) * 2 ^ (t + 1)
        = (2 * (t + 3)) * 2 ^ t := by rw [pow_succ]; ring
      _ ≤ (3 * (t + 2)) * 2 ^ t := Nat.mul_le_mul_right _ h
      _ = 3 * ((t + 2) * 2 ^ t) := by ring
      _ ≤ 3 * (2 * 3 ^ t) := Nat.mul_le_mul_left _ ih
      _ = 2 * 3 ^ (t + 1) := by rw [pow_succ]; ring

/-- The existing modulus eventually has degree at least any fixed multiple of
`⌊log₂ m⌋ + 1`. The threshold depends only on that multiple. -/
theorem mul_log_add_one_le_length_modulus {d m : ℕ} (hm : 2 ^ (2 ^ d) ≤ m) :
    d * (Nat.log 2 m + 1) ≤ (modulus m).length := by
  have hd : 2 ^ d ≤ Nat.log 2 m := Nat.le_log_of_pow_le (by norm_num) hm
  have ht : d ≤ modulusExp m :=
    Nat.le_log_of_pow_le (by norm_num) (show 2 ^ d ≤ 4 * Nat.log 2 m + 2 by omega)
  have hlog := Nat.lt_pow_succ_log_self one_lt_two (4 * Nat.log 2 m + 2)
  change 4 * Nat.log 2 m + 2 < 2 ^ (modulusExp m + 1) at hlog
  rw [pow_succ] at hlog
  have hpow : Nat.log 2 m + 1 ≤ 2 ^ modulusExp m := by omega
  rw [length_modulus]
  exact (Nat.mul_le_mul (by omega : d ≤ modulusExp m + 2) hpow).trans
    (mul_two_pow_le_two_mul_three_pow (modulusExp m))

/-- For every fixed power, the residue field of the existing modulus eventually contains at
least that many points. -/
theorem pow_le_card_modulus {d m : ℕ} (hm : 2 ^ (2 ^ d) ≤ m) :
    (m + 1) ^ d ≤ 2 ^ (modulus m).length := by
  have hm' : m + 1 ≤ 2 ^ (Nat.log 2 m + 1) :=
    Nat.lt_pow_succ_log_self one_lt_two m
  calc (m + 1) ^ d ≤ (2 ^ (Nat.log 2 m + 1)) ^ d := Nat.pow_le_pow_left hm' d
    _ = 2 ^ (d * (Nat.log 2 m + 1)) := by rw [← pow_mul, Nat.mul_comm]
    _ ≤ 2 ^ (modulus m).length :=
      Nat.pow_le_pow_right (by norm_num) (mul_log_add_one_le_length_modulus hm)

end Cslib.Circuits.Frontier.FastContraction
