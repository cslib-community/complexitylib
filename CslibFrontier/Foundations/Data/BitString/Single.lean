/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Ring.BooleanRing

/-!
# Unit vectors in Boolean vectors

For a Boolean vector `t : ι → Bool` with exclusive or as addition, the two vectors obtained by
adding the unit vector `e_i = Pi.single i b` with `b = false` and `b = true` add up to `e_i`: the
shared mask `t` cancels. This is the reconstruction step of the two-server and subcube private
information retrieval schemes of Chor, Goldreich, Kushilevitz and Sudan.

## Main results

* `Cslib.BitString.add_single_false_add_add_single_true`: `(t + e_i·0) + (t + e_i·1) = e_i`.
-/

public section

namespace Cslib.BitString

/-- Adding the two choices of the `i`-th unit vector to a shared mask `t` and summing leaves the
unit vector: `(t + e_i·0) + (t + e_i·1) = e_i`. -/
theorem add_single_false_add_add_single_true {ι : Type*} [DecidableEq ι] (t : ι → Bool) (i : ι) :
    (t + Pi.single i false) + (t + Pi.single i true) = Pi.single i true := by
  rw [show (Pi.single i false : ι → Bool) = 0 from Pi.single_zero i, add_zero]
  ext j
  rw [Pi.add_apply, Pi.add_apply, ← add_assoc, BooleanRing.add_self, zero_add]

end Cslib.BitString
