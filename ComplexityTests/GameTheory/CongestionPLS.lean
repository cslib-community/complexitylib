/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.GameTheory.Congestion.PLS

/-!
# Pure Nash equilibria of explicit congestion games

Two players choose between resource `0`, with costs `1, 2` at loads `1, 2`, and resource `1`,
with costs `3, 6`. Both players on resource `0` is a pure Nash equilibrium; both on resource `1`
is not, and neither is the split profile. The local-search neighbor moves away from a
non-equilibrium and fixes the equilibrium. A player with no listed strategy gets the empty one,
resource indices out of range are ignored, and strings of the wrong length are never solutions.
-/

namespace ComplexityTests.GameTheory.CongestionPLS

open Cslib.GameTheory Cslib.GameTheory.CongestionCode

/-- Two players, two resources: `[[0], [1]]` for each player, cost tables `[1, 2]` and
`[3, 6]`. -/
def twoLinks : CongestionCode := ([[[0], [1]], [[0], [1]]], [[1, 2], [3, 6]])

example : twoLinks.vertexLength = 10 := by decide

-- Profiles are encoded in blocks of `width = 5` bits with a thermometer code.
example : twoLinks.encode [0, 1] =
    [false, false, false, false, false, true, false, false, false, false] := by decide

-- Rosenthal's potential: `1 + 2` at `(0, 0)`, `1 + 3` at `(0, 1)`, `3 + 6` at `(1, 1)`.
example : twoLinks.potential [0, 0] = 3 := by decide
example : twoLinks.potential [0, 1] = 4 := by decide
example : twoLinks.potential [1, 1] = 9 := by decide

-- Both players on resource `0` is a pure Nash equilibrium.
example : twoLinks.PureNash (twoLinks.encode [0, 0]) := by
  rw [pureNash_iff]; decide

-- Both players on resource `1` is not, nor is the split profile.
example : ¬ twoLinks.PureNash (twoLinks.encode [1, 1]) := by
  rw [pureNash_iff]; decide

example : ¬ twoLinks.PureNash (twoLinks.encode [0, 1]) := by
  rw [pureNash_iff]; decide

-- The same facts for the congestion game `twoLinks.toGame` itself.
example : twoLinks.toGame.toCostGame.IsPureNash (twoLinks.decode (twoLinks.encode [0, 0])) :=
  ((pureNash_iff _ _).2 (by decide)).2

-- The local-search neighbor improves `(1, 1)` and fixes `(0, 0)`.
example : twoLinks.step (twoLinks.encode [1, 1]) = twoLinks.encode [0, 1] := by decide
example : twoLinks.step (twoLinks.encode [0, 0]) = twoLinks.encode [0, 0] := by decide

-- Every string of the right length decodes to a profile: excess ones clamp to strategy `0`.
example : twoLinks.decodeList (List.replicate 10 true) = [0, 0] := by decide

-- Strings of the wrong length are never solutions.
example : ¬ twoLinks.PureNash [] := by
  rw [pureNash_iff]; decide

/-- Player `0` lists no strategy and gets the empty one; player `1` lists a strategy that uses an
out-of-range resource `7` and resource `0`, whose cost table is empty. -/
def degenerate : CongestionCode := ([[], [[7, 0]]], [[]])

example : degenerate.numStrategies 0 = 1 := by decide
example : degenerate.strategy 0 0 = [] := by decide
example : degenerate.potential [0, 0] = 0 := by decide
example : degenerate.PureNash (List.replicate degenerate.vertexLength false) := by
  rw [pureNash_iff]; decide

-- Every code has a solution.
example (c : CongestionCode) : ∃ u, c.PureNash u := pureNash_mem_TFNP.2 c

end ComplexityTests.GameTheory.CongestionPLS
