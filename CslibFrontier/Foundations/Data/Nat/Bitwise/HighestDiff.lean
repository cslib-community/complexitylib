/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Nat.Bitwise.Projection
import Batteries.Data.Nat.Bitwise.Lemmas

/-!
# Highest differing bits through exclusive or

## Main results

* `highestDiff_eq_log2_xor`: the highest differing bit is the highest set bit of exclusive or.
* `highestDiff_le_of_xor_le`: comparing exclusive-or values suffices to compare divergences.

## References

See [FredmanWillard1993] for longest-prefix selection in fusion nodes.
-/

@[expose] public section

namespace Cslib.BitString

/-- The most significant set bit of exclusive or is the highest differing bit. Distinct
inputs ensure that this index identifies an actual set bit. -/
theorem highestDiff_eq_log2_xor {w x y : ℕ} (hx : x < 2 ^ w) (hy : y < 2 ^ w)
    (hne : x ≠ y) : highestDiff w x y = (x ^^^ y).log2 := by
  have hz : x ^^^ y ≠ 0 := fun h => hne (Nat.xor_eq_zero_iff.mp h)
  apply highestDiff_eq_of_testBit ((Nat.log2_lt hz).mpr (Nat.xor_lt_two_pow hx hy))
  · have h := Nat.testBit_log2 hz
    rw [Nat.testBit_xor] at h
    cases hxb : x.testBit (x ^^^ y).log2 <;>
      cases hyb : y.testBit (x ^^^ y).log2 <;> simp_all
  · intro i hi
    have he := Nat.testBit_eq_false_of_lt
      (Nat.lt_log2_self.trans_le (Nat.pow_le_pow_right (by decide) (by omega :
        (x ^^^ y).log2 + 1 ≤ i)))
    rw [Nat.testBit_xor] at he
    cases hxb : x.testBit i <;> cases hyb : y.testBit i <;> simp_all

/-- Smaller exclusive-or values have no higher differing position. This includes ties in the
highest differing position while retaining a concrete one-comparison selection rule. -/
theorem highestDiff_le_of_xor_le {w q x y : ℕ} (hq : q < 2 ^ w)
    (hx : x < 2 ^ w) (hy : y < 2 ^ w) (hqx : q ≠ x) (hqy : q ≠ y)
    (h : q ^^^ x ≤ q ^^^ y) : highestDiff w q x ≤ highestDiff w q y := by
  rw [highestDiff_eq_log2_xor hq hx hqx, highestDiff_eq_log2_xor hq hy hqy]
  have hz : q ^^^ x ≠ 0 := fun h => hqx (Nat.xor_eq_zero_iff.mp h)
  have hl := (Nat.log2_lt hz).mpr (h.trans_lt Nat.lt_log2_self)
  omega

end Cslib.BitString
