/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.ZMod.ValMinAbs

/-!
# Bounds for centered modular representatives

The centered representative `ZMod.valMinAbs` minimizes absolute value among the integer
representatives of a residue. This module records the comparison with an arbitrary chosen
integer representative.

## Main results

* `ZMod.abs_valMinAbs_intCast_le`: the centered representative of an integer modulo `q` has no
  greater magnitude than that integer.

## References

The result is derived from Mathlib's minimality and range API for `ZMod.valMinAbs`.
-/

public section

namespace ZMod

/-- The centered representative of an integer modulo `q` has no greater magnitude than the
chosen integer representative. -/
theorem abs_valMinAbs_intCast_le {q : ℕ} [NeZero q] (z : ℤ) :
    |((z : ZMod q).valMinAbs)| ≤ |z| := by
  rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs]
  norm_cast
  exact natAbs_min_of_le_div_two q ((z : ZMod q).valMinAbs) z
    (by rw [coe_valMinAbs]) (natAbs_valMinAbs_le (z : ZMod q))

end ZMod
