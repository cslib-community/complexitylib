/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.P
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership

/-!
# Finite problems are in `P`

A finite problem is decided in polynomial time by comparing the encoded instance with the
encodings of its finitely many members (`Set.Finite.mem_P`).

## Main results

* `Set.Finite.mem_P`: finite problems are in `P`.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-- **Finite problems are in `P`**, decided by comparing the encoded instance with the encodings
of the finitely many members. -/
theorem _root_.Set.Finite.mem_P {β : Type} {enc : β ↪ List Bool} {F : Set β} (hF : F.Finite) :
    F ∈ P enc := by
  classical
  refine ⟨fun b => decide (enc b ∈ hF.toFinset.toList.map enc), ?_, fun b => ?_⟩
  · have : ComputableInPolyTime (fun b : β => enc b) enc encBits := .of_eq fun _ => rfl
    fun_prop
  · simp

end Cslib.Complexity
