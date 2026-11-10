/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Space.Reachability
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Substituting width and depth bounds in Savitch's stack invariant

`length_encState_le_of_bounds` separates the stack accounting from the application-specific
choice of vertex width. When depth and width are each bounded by a multiple of a common scale,
the actual encoded state has a quadratic bound in that scale. The invariant still has to hold
for the concrete state; a linear-space transition alone supplies no such guarantee.
-/

public section

namespace Cslib.Reachability.Savitch

/-- Depth times frame size gives a quadratic state bound when both are linear in `L`. -/
theorem length_encState_le_of_bounds {w d L D W : ℕ} {s : State}
    (h : Invariant w d s) (hd : d ≤ D * L) (hw : w ≤ W * L) (hL : 1 ≤ L) :
    (encState s).length ≤ 24 * (D + 1) * (D + W + 1) * L ^ 2 := by
  have hdepth : d + 1 ≤ (D + 1) * L := by nlinarith
  have hframe : d + w + 1 ≤ (D + W + 1) * L := by nlinarith
  calc
    (encState s).length ≤ 24 * (d + 1) * (d + w + 1) := length_encState_le h
    _ ≤ 24 * ((D + 1) * L) * ((D + W + 1) * L) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 24 hdepth) hframe
    _ = 24 * (D + 1) * (D + W + 1) * L ^ 2 := by ring

end Cslib.Reachability.Savitch
