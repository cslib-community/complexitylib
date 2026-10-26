/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Foundations.Geometry.Orthogonal.Macrocell

/-! Concrete contacts and noncontacts in the real 240-by-240 tiling. -/

namespace ComplexityTests.OrthogonalMacrocell

open Cslib.Orthogonal

-- Translation includes isolated route vertices and preserves wire length.
example : translate (-240, 480) [(0, 0), (120, 0), (120, 120)] =
    [(-240, 480), (-120, 480), (-120, 600)] := by decide

example : wireLength (translate (-240, 480) [(0, 0), (120, 0), (120, 120)]) = 240 := by
  rw [wireLength_translate]
  decide

example : IsOrthogonal (translate (-240, 480) [(0, 0), (120, 0), (120, 120)]) := by
  rw [isOrthogonal_translate_iff]
  simp [IsOrthogonal, List.consecutivePairs, AxisAligned]

example : IsSimple (translate (-240, 480) [(0, 0), (120, 0)]) := by
  rw [isSimple_translate_iff]
  simp [IsSimple, List.consecutivePairs]

example : ((-239.5 : ℝ), (480 : ℝ)) ∈
    support (translate (-240, 480) [(0, 0), (120, 0)]) := by
  have h : ((0.5 : ℝ), (0 : ℝ)) ∈ support [(0, 0), (120, 0)] := by
    rw [support_cons_cons]
    apply Or.inl
    norm_num [Cslib.Orthogonal.segment, realPoint, mem_horizontal, Set.mem_uIcc]
  convert (mem_support_translate_iff (-240, 480) _ _).2 h using 1
  norm_num [realPoint]

-- Adjacent closed cells share their midpoint port, but their open interiors never meet.
example : cellPort 120 (0, 0) 1 = cellPort 120 (1, 0) 0 := by decide
example : realPoint (cellPort 120 (0, 0) 1) ∈ closedCell 120 (0, 0) ∩
    closedCell 120 (1, 0) := by
  norm_num [cellPort, cellOrigin, realPoint, closedCell]

example : Disjoint (openCell 120 (0, 0)) (closedCell 120 (1, 0)) :=
  disjoint_openCell_closedCell (by decide) (by decide)

-- Negative cell indices obey the same separation and port convention.
example : cellPort 120 (-1, -2) 3 = cellPort 120 (-1, -1) 2 := by decide
example : Disjoint (openCell 120 (-1, -2)) (openCell 120 (-1, -1)) :=
  disjoint_openCell (by decide) (by decide)

-- Fractional points are included in both the positive and the forbidden-contact checks.
example : ((0.5 : ℝ), (239.5 : ℝ)) ∈ openCell 120 (0, 0) := by
  norm_num [openCell]
example : ((240 : ℝ), (120 : ℝ)) ∉ openCell 120 (0, 0) := by
  norm_num [openCell]
example : cellPort 120 (0, 0) 1 ≠ cellPort 120 (2, 0) 0 := by decide

-- Zero radius is deliberately excluded from the separation theorem.
example : cellPort 0 (0, 0) 0 = cellPort 0 (20, -30) 3 := by decide

end ComplexityTests.OrthogonalMacrocell
