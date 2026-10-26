/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SAT.Planar.PathData
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Linarith

/-!
# Bounds for shared incidence-path data

Canonical path budgets, crossing counts, retained-gap counts, and 240-macrocell grid
sides are independent of the emitted clause template. No output formula is defined here.

## Main definitions

* `Cslib.Complexity.SAT.PlanarCompile.linkCount`: retained path gaps.
* `Cslib.Complexity.SAT.PlanarCompile.gridWidth`, `.gridHeight`: shared macrocell grid sides.

## Main results

* `Cslib.Complexity.SAT.PlanarCompile.crossingSites_length_le`.
* `Cslib.Complexity.SAT.PlanarCompile.paths_length`.
* `Cslib.Complexity.SAT.PlanarCompile.path_length_le`.
* `Cslib.Complexity.SAT.PlanarCompile.linkCount_le`.
* `Cslib.Complexity.SAT.PlanarCompile.gridWidth_le`.
* `Cslib.Complexity.SAT.PlanarCompile.gridHeight_le`.

## References

These are the shared canonical incidence-path constructions and certificates.
-/

@[expose] public section

namespace Cslib.Complexity.SAT.PlanarCompile

open Cslib.Logic.PL Cslib.Logic.PL.CNF Orthogonal

/-- Number of retained path gaps before the final step into each source clause. -/
def linkCount (φ : CNF ℕ) : ℕ :=
  ((Cslib.Logic.PL.occurrences φ).map fun o => (occurrencePath φ o).length - 2).sum

/-- Selected crossing sites form a sublist of the quadratic canonical cover after deduplication.
The bound counts all source literal incidences, including repetitions. -/
theorem crossingSites_length_le (φ : CNF ℕ) :
    (crossingSites φ).length ≤ 2 * φ.vars.length ^ 2 := by
  unfold crossingSites
  rw [length_selectDistinct_replicate]
  exact (List.toFinset_card_le _).trans ((List.length_filter_le _ _).trans (by
    simp [Graph.crossingCandidates_length, SAT.length_edges_incidenceGraph]))

/-- There is one unit path per original literal incidence. -/
theorem paths_length (φ : CNF ℕ) : (paths φ).length = φ.vars.length := by
  simp [paths, SAT.length_edges_incidenceGraph]

/-- The bounded enumerator emits at most five segment budgets plus the final endpoint.
This unconditional bound also applies to inputs that fail the degree-three restriction. -/
theorem path_length_le {φ : CNF ℕ} {r : Route} (hr : r ∈ paths φ) :
    r.length ≤ 5 * budget φ + 1 := by
  change r ∈ ((SAT.incidenceGraph φ).orthogonalRoutes
    (SAT.incidenceGraph φ).canonicalPorts).map (subdivideWithin (budget φ)) at hr
  obtain ⟨base, hbase, rfl⟩ := List.mem_map.mp hr
  have hs : base.consecutivePairs.length = 5 := by
    obtain ⟨⟨e, i⟩, _, rfl⟩ := List.mem_map.mp hbase
    rfl
  simpa only [hs, Nat.mul_comm] using subdivideWithin_length_le (budget φ) base

/-- Indexed access to a path obeys the same bound, including the empty fallback. -/
theorem occurrencePath_length_le (φ : CNF ℕ) (o : Occurrence ℕ) :
    (occurrencePath φ o).length ≤ 5 * budget φ + 1 := by
  unfold occurrencePath
  by_cases h : (Cslib.Logic.PL.occurrences φ).idxOf o < (paths φ).length
  · rw [List.getD_eq_getElem _ _ h]
    exact path_length_le (List.getElem_mem h)
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact Nat.zero_le _

/-- There are quadratically many links, even before checking the source restrictions. -/
theorem linkCount_le (φ : CNF ℕ) :
    linkCount φ ≤ φ.vars.length * (5 * budget φ + 1) := by
  calc
    _ ≤ ((Cslib.Logic.PL.occurrences φ).map fun _ => 5 * budget φ + 1).sum :=
      List.sum_le_sum fun o _ => (Nat.sub_le _ _).trans (occurrencePath_length_le φ o)
    _ = _ := by simp [Cslib.Logic.PL.length_occurrences, Nat.mul_comm]

/-- Horizontal side of the actual tiled drawing, including its last square. -/
def gridWidth (φ : CNF ℕ) : ℕ := 240 * (8 * (SAT.incidenceGraph φ).1.length + 1)
/-- Vertical side of the actual tiled drawing, including its last square. -/
def gridHeight (φ : CNF ℕ) : ℕ :=
  240 * (8 * (SAT.incidenceGraph φ).1.length + 2 * (SAT.incidenceGraph φ).2.length + 1)

/-- The horizontal grid side is at most 1920 times the source incidence size plus one. -/
theorem gridWidth_le (φ : CNF ℕ) :
    gridWidth φ ≤ 1920 * (φ.numVars + φ.length + φ.vars.length + 1) := by
  unfold gridWidth
  rw [SAT.length_vertices_incidenceGraph]
  nlinarith

/-- The vertical grid side is at most 1920 times the source incidence size plus one. -/
theorem gridHeight_le (φ : CNF ℕ) :
    gridHeight φ ≤ 1920 * (φ.numVars + φ.length + φ.vars.length + 1) := by
  unfold gridHeight
  rw [SAT.length_vertices_incidenceGraph, SAT.length_edges_incidenceGraph]
  nlinarith

end Cslib.Complexity.SAT.PlanarCompile
