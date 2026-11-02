/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.Nat.BinarySize
public import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Precision and truncation bounds for binary weights

If the number of vertices is linear in `s` and local weights have a fixed polynomial number of
bits, binary-digit contraction needs precision `O(s log s)` and a fixed polynomial truncation
order. These elementary estimates keep the constants before the instance parameters.

## Main results

* `binaryWeight_size_le`: a polynomially bounded bit-length has logarithmic binary length.
* `binaryWeight_parameters_le`: the precision and truncation fit the strengthened contraction
  interface with explicit constants.
-/

public section

namespace Cslib.Circuits.Frontier

/-- The binary length of a number bounded by `D (s + 1)^d` is at most a fixed multiple of
`⌊log₂ s⌋ + 1`. -/
theorem binaryWeight_size_le {B D d s : ℕ} (hB : B ≤ D * (s + 1) ^ d) :
    B.size ≤ (D.size + 2 * d + 1) * (Nat.log 2 s + 1) := by
  have hs : s + 1 ≤ 2 ^ (Nat.log 2 s + 1) := Nat.lt_pow_succ_log_self one_lt_two s
  have hsize : (s + 1).size ≤ Nat.log 2 s + 2 := by
    simpa only [Nat.size_pow, Nat.add_assoc] using Nat.size_le_size hs
  have h1 := Nat.size_mul_le D ((s + 1) ^ d)
  have h2 := Nat.size_pow_le (s + 1) d
  have h3 := Nat.size_le_size hB
  have h4 := Nat.mul_le_mul_left d hsize
  nlinarith

/-- For at most `C s` vertices, a polynomial bound on local bit-length gives logarithmic-linear
precision and polynomial truncation. The displayed constant depends only on `C`, `D` and `d`. -/
theorem binaryWeight_parameters_le {B C D d s v : ℕ} (hs : 1 ≤ s)
    (hv : v ≤ C * s) (hB : B ≤ D * (s + 1) ^ d) :
    s + v * B.size + 1 ≤ (C * (D.size + 2 * d + 1) + 2) * s * (Nat.log 2 s + 1) ∧
      (B - 1) * v + 1 ≤ (C * D + 1) * (s + 1) ^ (d + 1) := by
  constructor
  · set E := D.size + 2 * d + 1
    set L := Nat.log 2 s + 1
    have hL : 1 ≤ L := by omega
    have h1 : v * B.size ≤ C * s * (E * L) :=
      Nat.mul_le_mul hv (binaryWeight_size_le hB)
    have h2 : s ≤ s * L := Nat.le_mul_of_pos_right _ hL
    have h3 : 1 ≤ s * L := hs.trans h2
    calc s + v * B.size + 1 ≤ s * L + C * s * (E * L) + s * L := by omega
      _ = (C * E + 2) * s * L := by ring
  · have h1 : (B - 1) * v ≤ C * D * (s + 1) ^ (d + 1) := by
      calc (B - 1) * v ≤ (D * (s + 1) ^ d) * (C * (s + 1)) :=
            Nat.mul_le_mul (by omega) (hv.trans (Nat.mul_le_mul_left C (Nat.le_succ s)))
        _ = C * D * (s + 1) ^ (d + 1) := by rw [pow_succ]; ring
    have h2 : 1 ≤ (s + 1) ^ (d + 1) := Nat.one_le_pow _ _ (by omega)
    nlinarith

end Cslib.Circuits.Frontier
