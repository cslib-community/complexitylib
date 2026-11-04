/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.DataStructure.Memory.Alloc

/-!
# The cells a framed method or an allocation writes

A method run of a framed refinement changes an allocated cell only in its footprint, and it
advances the frontier by at most the room it gives up, so the cells it allocates lie in the room
reserved above the old frontier. An admissible run changes no cell at or above its final
frontier. So a method run writes only the footprint and the reserved room, the region of the
structure (`Framed.region`, `Framed.mem_eq_of_not_mem_region`). An allocation changes no
allocated cell, and allocates only within the room it takes, so it writes only that room
(`Allocates.mem_eq_of_not_mem`). These are the memory side of the native frame theorems of
`Realization.Backend`.

The argument is the block frame of `Realization.product_exec` in #2273 (Codex), stated here once
for every framed refinement.

## Main definitions

* `Memory.Framed.region`: the footprint and the room reserved above the frontier.

## Main results

* `Memory.Framed.mem_eq_of_not_mem_region`: a method run writes only the region.
* `Memory.Framed.region_eq_footprint`: without room, the region is the footprint.
* `Memory.Allocates.mem_eq_of_not_mem`: an allocation writes only the room it takes.
-/

@[expose] public section

namespace Cslib.DataStructure.Memory

open Cslib.WordRAM

variable {w : ℕ} {D : StateTransitionSpec.{0, 0, 0}}

/-- The cells that a method run of `M` from `s` may write: the footprint, and the room reserved
above the frontier. -/
def Framed.region (M : Framed D w) (s : State) : Finset ℕ :=
  M.footprint s ∪ Finset.Ico s.frontier (s.frontier + M.room s)

/-- Without room, the region is the footprint. -/
theorem Framed.region_eq_footprint (M : Framed D w) {s : State} (h : M.room s = 0) :
    M.region s = M.footprint s := by
  simp [Framed.region, h]

/-- **A method run writes only the region**: an allocated cell outside the footprint is kept
by `Framed.modifies`, and a cell beyond the reserved room lies at or above the final frontier. -/
theorem Framed.mem_eq_of_not_mem_region (M : Framed D w) {s : State} (o : D.Op)
    {a : D.Result o} {s' : State} {tr : (spec w).Transcript} (hs : M.inv s)
    (hv : D.valid (M.abs s) o) (hrun : (spec w).ClientRun s (M.methods o) a s' tr) {b : ℕ}
    (hb : b ∉ M.region s) : s'.mem b = s.mem b := by
  obtain ⟨hmod, -, hroom⟩ := M.modifies o hs hv hrun
  simp only [Framed.region, Finset.mem_union, Finset.mem_Ico, not_or, not_and, not_lt] at hb
  obtain ⟨hfp, hico⟩ := hb
  by_cases hlt : b < s.frontier
  · exact hmod b hlt hfp
  · obtain ⟨hvh, -, rfl, -⟩ := ((spec w).clientRun_iff_runClient _ _ _ _ _).mp hrun
    have := hico (Nat.le_of_not_lt hlt)
    exact mem_clientState_of_frontier_le s _ hvh (by omega)

/-- **An allocation writes only the room it takes**: it keeps every allocated cell, and every
cell beyond its room lies at or above its final frontier. -/
theorem Allocates.mem_eq_of_not_mem {H : Type} {alloc : Prog H} {methods : H → Methods D (spec w)}
    {init : D.State} {owned : Finset ℕ} {room cost : ℕ} {s : State} {M : Framed D w}
    (h : Allocates alloc methods init owned room cost s M) {b : ℕ}
    (hb : b ∉ Finset.Ico s.frontier (s.frontier + room)) :
    ((spec w).clientState s alloc).mem b = s.mem b := by
  rw [Finset.mem_Ico, not_and, not_lt] at hb
  by_cases hlt : b < s.frontier
  · exact h.mem_eq b hlt
  · have := h.room_le
    have := hb (Nat.le_of_not_lt hlt)
    exact mem_clientState_of_frontier_le s alloc h.validHistory (by omega)

end Cslib.DataStructure.Memory
