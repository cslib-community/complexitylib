/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

-- upstream: candidate

import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.ArgumentPermutation

/-! Ordinary occurrence-only import, repeated names, nullary rows and distinct row positions. -/

namespace CslibFrontierTests.CSPArgumentPermutation

open Cslib.Logic.PL Cslib.Complexity.CSP

private abbrev F : CSP Unit ℕ := [⟨(), [7, 7]⟩, ⟨(), []⟩, ⟨(), [7]⟩]
private def first : F.Occurrence := ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩
private def second : F.Occurrence := ⟨⟨0, by decide⟩, ⟨1, by decide⟩⟩
private def last : F.Occurrence := ⟨⟨2, by decide⟩, ⟨0, by decide⟩⟩

example : argumentPermutation F first = second := by decide
example : argumentPermutation F second = first := by decide
example : argumentPermutation F last = last := by decide

example : (argumentPermutation F).SameCycle first second :=
  (sameCycle_argumentPermutation first second).mpr rfl

example : ¬ (argumentPermutation F).SameCycle first last := by
  rw [sameCycle_argumentPermutation]
  decide

/-- info: Unknown identifier `Cslib.Complexity.CSP.polygonGraph` -/
#guard_msgs in
#check_failure Cslib.Complexity.CSP.polygonGraph

end CslibFrontierTests.CSPArgumentPermutation
