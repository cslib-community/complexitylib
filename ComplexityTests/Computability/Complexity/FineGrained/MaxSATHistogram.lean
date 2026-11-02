/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import Complexity.Computability.Complexity.FineGrained.MaxSAT.Histogram

/-!
# Exact MAX-SAT histogram edge cases

The finite examples distinguish the canonical declared assignment count, clause multiplicities,
empty clauses, and the total convention for undeclared references.
-/

open Cslib.Complexity.MaxSAT

example : histogram (0, []) = [1] := by decide
example : optimum (0, []) = 0 := by decide

/-- Three unused variables still give eight assignments of score zero. -/
example : histogram (3, []) = [8] := by decide
example : thresholdCounts (3, []) = [8, 0] := by decide

/-- Repeated clauses retain their multiplicity: score one is impossible here. -/
example : histogram (1, [[(0, true)], [(0, true)]]) = [1, 0, 1] := by decide
example : optimum (1, [[(0, true)], [(0, true)]]) = 2 := by decide

/-- Opposite literals and an empty clause force score one; the second declared variable is free. -/
example : histogram (2, [[(0, true)], [(0, false)], []]) = [0, 4, 0, 0] := by decide
example : optimum (2, [[(0, true)], [(0, false)], []]) = 1 := by decide

/-- With no declared variables, the undeclared variable reads false. -/
example : histogram (0, [[(0, true)], [(0, false)]]) = [0, 1, 0] := by decide

/-- The runtime postprocessors agree with the exact semantics on a nontrivial example. -/
example : histogramFromCounts (thresholdCounts (2, [[(0, true)], [(0, false)], []])) =
    [0, 4, 0, 0] := by decide
example : optimumFromCounts (thresholdCounts (2, [[(0, true)], [(0, false)], []])) = 1 := by decide

/-- Width and density permit the empty instance even at zero parameters. -/
example : SparseInstance 0 0 := ⟨(0, []), by simp⟩
