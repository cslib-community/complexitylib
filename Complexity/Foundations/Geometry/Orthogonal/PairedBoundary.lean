/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Foundations.Geometry.Orthogonal.PairedPorts
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Matching paired boundaries of grid cells

## Main results

* `boundary_eq_cases`: equal boundary points in distinct cells determine adjacent opposite
  sides and the same lane.
* `boundary_not_mem_openCell`: a paired boundary belongs to no open grid cell.

## References

These are original integer-coordinate facts about the fixed paired-port interface.
-/

@[expose] public section

namespace Cslib.Orthogonal.PairedPorts

/-- Equal boundary points in distinct cells identify the lane and opposite adjacent sides. -/
theorem boundary_eq_cases {c d : Point} {s t : Fin 4} {l k : Fin 2}
    (hcd : c ≠ d)
    (h : cellOrigin 120 c + boundaryPort s l = cellOrigin 120 d + boundaryPort t k) :
    l = k ∧ d = c + neighbor s ∧ t = oppositeSide s := by
  rcases c with ⟨cx, cy⟩
  rcases d with ⟨dx, dy⟩
  have hcd' : ¬ (cx = dx ∧ cy = dy) := fun h => hcd (Prod.ext h.1 h.2)
  fin_cases s <;> fin_cases t <;> fin_cases l <;> fin_cases k <;>
    norm_num [cellOrigin, boundaryPort, offset, neighbor, oppositeSide, Prod.ext_iff] at h ⊢ <;>
    omega

/-- Each translated paired boundary belongs to its own closed cell. -/
theorem boundary_mem_closedCell (c : Point) (s : Fin 4) (l : Fin 2) :
    realPoint (cellOrigin 120 c + boundaryPort s l) ∈ closedCell 120 c := by
  rw [realPoint_add, add_comm, mem_closedCell_add_origin_iff]
  fin_cases s <;> fin_cases l <;> norm_num [boundaryPort, offset, realPoint]

/-- A translated paired boundary lies outside every open grid cell. -/
theorem boundary_not_mem_openCell (c d : Point) (s : Fin 4) (l : Fin 2) :
    realPoint (cellOrigin 120 c + boundaryPort s l) ∉ openCell 120 d := by
  intro hp
  have hdc := cell_eq_of_mem_open_closed (by decide) hp (boundary_mem_closedCell c s l)
  subst d
  rw [realPoint_add, add_comm, mem_openCell_add_origin_iff] at hp
  fin_cases s <;> fin_cases l <;> norm_num [boundaryPort, offset, realPoint] at hp

end Cslib.Orthogonal.PairedPorts
