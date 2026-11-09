/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Nat.CeilQuarter
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.Ring

/-!
# Computing the ceiling fourth root by integer square roots

The search definition has an explicit square-root implementation, including at zero.

## Main results

* `Nat.ceilQuarter_eq_sqrt`: compute the ceiling fourth root by two integer square roots.
-/

public section

namespace Nat

/-- Two integer square roots compute the search-defined ceiling fourth root, including zero. -/
theorem ceilQuarter_eq_sqrt (n : ℕ) :
    ceilQuarter n = if n = 0 then 0 else (n - 1).sqrt.sqrt + 1 := by
  by_cases hn : n = 0
  · subst n
    have h := ceilQuarter_le_self 0
    simp only [ite_true]
    omega
  rw [ite_eq_right hn]
  let q := (n - 1).sqrt.sqrt
  have hlow : q ^ 4 ≤ n - 1 := by
    have h1 := Nat.sqrt_le' ((n - 1).sqrt)
    have h2 := Nat.sqrt_le' (n - 1)
    calc q ^ 4 = (q ^ 2) ^ 2 := by ring
      _ ≤ ((n - 1).sqrt) ^ 2 := Nat.pow_le_pow_left h1 _
      _ ≤ n - 1 := h2
  have hhigh : n - 1 < (q + 1) ^ 4 := by
    have h1 := Nat.lt_succ_sqrt' ((n - 1).sqrt)
    have h2 := Nat.lt_succ_sqrt' (n - 1)
    change (n - 1).sqrt < (q + 1) ^ 2 at h1
    calc n - 1 < ((n - 1).sqrt + 1) ^ 2 := h2
      _ ≤ ((q + 1) ^ 2) ^ 2 := Nat.pow_le_pow_left (by omega) _
      _ = (q + 1) ^ 4 := by ring
  have hupper : ceilQuarter n ≤ q + 1 := Nat.find_min' _ (by omega)
  have h := le_ceilQuarter_pow n
  have hlower : q + 1 ≤ ceilQuarter n := by
    by_contra hle
    have hq : ceilQuarter n ≤ q := by omega
    have hpow := Nat.pow_le_pow_left hq 4
    omega
  exact Nat.le_antisymm hupper hlower

end Nat
