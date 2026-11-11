/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (next to `Cslib/Computability/Circuit/Boolean/Counting.lean`)

public import CslibFrontier.Init
public import Cslib.Computability.Circuit.Boolean.Counting
public import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Ring

/-!
# A power-of-two bound on the number of small De Morgan circuits

At most `2 ^ M` functions on `n` inputs have De Morgan circuit complexity at most `s`, where
`M = computableFunctionsLogBound n s = (s + 1) (2 ⌈log₂ (n + s + 1)⌉ + 3)`. This is the factorial
bound `Cslib.Circuits.Boolean.card_computableFunctions_mul_factorial_le` with the factorial dropped
and every factor rounded up to a power of two. The resulting exponent is `O(s log (n + s))`, which
union bounds over small circuits need.

## Main definitions

* `Cslib.Circuits.Boolean.computableFunctionsLogBound`: the exponent
  `(s + 1) * (2 * Nat.clog 2 (n + s + 1) + 3)`.

## Main results

* `Cslib.Circuits.Boolean.card_computableFunctions_le_two_pow`:
  `(computableFunctions n s).card ≤ 2 ^ computableFunctionsLogBound n s`.
* `Cslib.Circuits.Boolean.computableFunctionsLogBound_le_poly`: the exponent is at most
  `(s + 1) (2 (n + s + 1) + 3)`.
-/

public section

namespace Cslib.Circuits.Boolean

/-- An explicit `s log(n + s)` upper bound on `log₂ (computableFunctions n s).card`, derived from
`card_computableFunctions_mul_factorial_le`. -/
@[expose] def computableFunctionsLogBound (n s : ℕ) : ℕ :=
  (s + 1) * (2 * Nat.clog 2 (n + s + 1) + 3)

/-- The number of `n`-input Boolean functions of De Morgan circuit complexity at most `s` is at most
`2 ^ computableFunctionsLogBound n s`. -/
theorem card_computableFunctions_le_two_pow (n s : ℕ) :
    (computableFunctions n s).card ≤ 2 ^ computableFunctionsLogBound n s := by
  set L := Nat.clog 2 (n + s + 1)
  have hns : n + s + 1 ≤ 2 ^ L := Nat.le_pow_clog (by decide) (n + s + 1)
  have hs1 : s + 1 ≤ 2 ^ L := (by omega : s + 1 ≤ n + s + 1).trans hns
  have hns0 : n + s ≤ 2 ^ L := (by omega : n + s ≤ n + s + 1).trans hns
  have hbase : 5 * (n + s + 1) ^ 2 ≤ 2 ^ (2 * L + 3) := by
    calc 5 * (n + s + 1) ^ 2
        ≤ 8 * (2 ^ L) ^ 2 := Nat.mul_le_mul (by decide) (Nat.pow_le_pow_left hns 2)
      _ = 2 ^ (2 * L + 3) := by
        rw [← pow_mul, pow_add]
        ring
  have hpow : (5 * (n + s + 1) ^ 2) ^ s ≤ 2 ^ (s * (2 * L + 3)) := by
    calc (5 * (n + s + 1) ^ 2) ^ s
        ≤ (2 ^ (2 * L + 3)) ^ s := Nat.pow_le_pow_left hbase s
      _ = 2 ^ (s * (2 * L + 3)) := by rw [← pow_mul, mul_comm]
  have hends : (s + 1) * (n + s) ≤ 2 ^ (2 * L + 3) := by
    calc (s + 1) * (n + s)
        ≤ 2 ^ L * 2 ^ L := Nat.mul_le_mul hs1 hns0
      _ = 2 ^ (2 * L) := by rw [← pow_add, two_mul]
      _ ≤ 2 ^ (2 * L + 3) := Nat.pow_le_pow_right (by decide) (by omega)
  calc (computableFunctions n s).card
      ≤ (computableFunctions n s).card * s.factorial :=
        Nat.le_mul_of_pos_right _ (Nat.factorial_pos s)
    _ ≤ (s + 1) * (5 * (n + s + 1) ^ 2) ^ s * (n + s) :=
        card_computableFunctions_mul_factorial_le n s
    _ = ((s + 1) * (n + s)) * (5 * (n + s + 1) ^ 2) ^ s := by ring
    _ ≤ 2 ^ (2 * L + 3) * 2 ^ (s * (2 * L + 3)) := Nat.mul_le_mul hends hpow
    _ = 2 ^ computableFunctionsLogBound n s := by
        rw [← pow_add, computableFunctionsLogBound]
        congr 1
        ring

/-- Elementary polynomial upper bound on `computableFunctionsLogBound n s`: since
`Nat.clog 2 (n + s + 1) ≤ n + s + 1`, we have
`computableFunctionsLogBound n s ≤ (s + 1) * (2 * (n + s + 1) + 3)`. -/
theorem computableFunctionsLogBound_le_poly (n s : ℕ) :
    computableFunctionsLogBound n s ≤ (s + 1) * (2 * (n + s + 1) + 3) := by
  have hclog : Nat.clog 2 (n + s + 1) ≤ n + s + 1 :=
    (Nat.clog_le_iff_le_pow (by decide)).mpr (Nat.lt_two_pow_self).le
  dsimp only [computableFunctionsLogBound]
  exact Nat.mul_le_mul_left (s + 1)
    (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hclog) 3)

end Cslib.Circuits.Boolean
