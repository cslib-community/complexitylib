/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.TraversalTime

/-!
# Polylogarithmic traversal overhead on charged native instructions

The full ternary transition budget includes skipped calls. At the existing Chan–He recursion
fuel it is polylogarithmic, just as the emitted-node bound is. Combining it with the actual
native visit cost gives a cubic candidate-bound term and a linear-times-candidate input term.
This is a charged instruction estimate, not the finite reduction's candidate/element pair count.

## Main results

* `work_fuel_le`: polylogarithmically many charged transitions, including zero-fuel leaves.
* `visitTime_square_le`: the actual visit bound is controlled by `n*m + m³` up to constants.
* `rootTime_fuel_square_le`: the complete native root bound has polylogarithmic tree overhead.

These native resource estimates are original. Substituting the actual parameter bound and
composing all frontend roots remain obligations of initialized-input preprocessing.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Traversal

open Cslib.Algorithms.ThreeSum.ChanHe (fuel three_pow_fuel_le)

/-- Full-tree work counts all native pops, not just emitted mathematical instances. -/
theorem work_fuel_le (n : ℕ) : Math.work (fuel n) ≤ 3 * (2 * Nat.log 2 n + 2) ^ 5 := by
  have he := Math.work_eq (fuel n)
  rw [pow_succ] at he
  have hb := Nat.mul_le_mul_right 3 (three_pow_fuel_le n)
  omega

/-- The concrete `N=2m²` visit cost has the desired input-times-candidate and cubic terms. -/
theorem visitTime_square_le (n m : ℕ) :
    visitTime n m (2 * m ^ 2) ≤ 1024 * ((n + 1) * (m + 1) + (m + 1) ^ 3) := by
  dsimp only [visitTime]
  nlinarith

/-- The complete native root cost, including setup, all skipped calls and all stack/loop work,
has only a polylogarithmic factor beyond `card*m + m³`. -/
theorem rootTime_fuel_square_le (n card m : ℕ) :
    rootTime (fuel n) card m (2 * m ^ 2) ≤
      70 + 6144 * (2 * Nat.log 2 n + 2) ^ 5 *
        ((card + 1) * (m + 1) + (m + 1) ^ 3) := by
  let S := (card + 1) * (m + 1) + (m + 1) ^ 3
  have hpos : 1 ≤ S := by
    have hp : 0 < S := by dsimp only [S]; positivity
    omega
  have hvisit := visitTime_square_le card m
  have hcost : visitTime card m (2 * m ^ 2) + 316 ≤ 2048 * S := by
    change visitTime card m (2 * m ^ 2) ≤ 1024 * S at hvisit
    omega
  have hm := Nat.mul_le_mul (work_fuel_le n) hcost
  calc rootTime (fuel n) card m (2 * m ^ 2)
      ≤ 70 + (3 * (2 * Nat.log 2 n + 2) ^ 5) * (2048 * S) :=
        Nat.add_le_add_left hm 70
    _ = 70 + 6144 * (2 * Nat.log 2 n + 2) ^ 5 *
        ((card + 1) * (m + 1) + (m + 1) ^ 3) := by dsimp only [S]; ring

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Traversal
