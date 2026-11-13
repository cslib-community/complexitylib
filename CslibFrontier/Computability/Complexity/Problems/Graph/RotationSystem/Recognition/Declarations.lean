/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Declarations
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.Input

/-!
# Fresh-hub declaration cleanup

Contracting a fresh split hub to an old vertex repeats that vertex in the declaration list.
The exact dense-range relabeling below retains that duplicate explicitly. General rotation
transport across duplicate declarations lives in `Graph.RotationSystem.Declarations`.
-/

public section

namespace Cslib.Complexity.Graph.RotationRecognition

/-- Contracting fresh name `n` to old name `v` relabels the dense declarations to `range n ++ [v]`.
The duplicate old declaration is explicit and can then use the numerical transport theorem. -/
theorem map_range_update_fresh (n v : ℕ) :
    (List.range (n + 1)).map (Function.update id n v) = List.range n ++ [v] := by
  rw [List.range_succ, List.map_append, List.map_singleton, Function.update_self]
  congr 1
  have hm : (List.range n).map (Function.update id n v) = (List.range n).map id := by
    apply List.map_congr_left
    intro i hi
    have hin : i ≠ n := by have := List.mem_range.mp hi; omega
    exact Function.update_of_ne hin _ _
  simpa using hm

end Cslib.Complexity.Graph.RotationRecognition
