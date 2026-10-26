/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SAT.Planar.Paths
public import Complexity.Computability.Complexity.Problems.Graph.OrthogonalPath
public import Complexity.Computability.Complexity.Problems.SAT.Incidence.Degree
import Complexity.Foundations.Data.List.Filter
import Mathlib.Data.List.GetD

/-!
# Ordinary-cell occupancy in the actual planarization paths

This module depends only on the executable compiler and canonical source layout. Both the
continuous drawing proof and the literal-count proof can use it without importing each other.

## Main results

* `Cslib.Complexity.SAT.PlanarCompile.paths_filter_length_le_one`: outside source centers and
  selected crossing cells, at most one actual path contains a given integer point.

## References

This is an original consequence of the canonical path contact classification.
-/

@[expose] public section

namespace Cslib.Complexity.SAT.PlanarCompile

open Cslib.Logic.PL Orthogonal

/-- Away from source centers, an unselected ordinary cell belongs to at most one path. -/
theorem paths_filter_length_le_one {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3) {p : Point}
    (hp : p ∉ crossingSites φ) (hc : p ∉ (SAT.incidenceGraph φ).orthogonalPositions) :
    ((paths φ).filter fun r => r.contains p).length ≤ 1 := by
  by_contra h
  have ht : 2 ≤ ((paths φ).filter fun r => r.contains p).length := by omega
  obtain ⟨i, j, hi, hj, hij, hpi, hpj⟩ :=
    (List.two_le_filter_contains_iff (paths φ) p).1 ht
  have hi' : i < (SAT.incidenceGraph φ).2.length := by
    simpa only [paths_eq_unitPaths, Graph.unitPaths_length] using hi
  have hj' : j < (SAT.incidenceGraph φ).2.length := by
    simpa only [paths_eq_unitPaths, Graph.unitPaths_length] using hj
  have hpi' : p ∈ (SAT.incidenceGraph φ).unitPath i := by
    change p ∈ (paths φ).getD i []
    rwa [List.getD_eq_getElem _ _ hi]
  have hpj' : p ∈ (SAT.incidenceGraph φ).unitPath j := by
    change p ∈ (paths φ).getD j []
    rwa [List.getD_eq_getElem _ _ hj]
  have hcand := Graph.unitPath_shared_mem_crossingCandidates (SAT.incidenceGraph φ)
    (fun _ => SAT.incidenceGraph_endpoints) (fun _ => SAT.incidenceGraph_loopless)
    (SAT.incidenceGraph_degree_le hw hv) hi' hj' hij hc hpi' hpj'
  exact hp ((mem_crossingSites φ p).mpr ⟨hcand, hc, ht⟩)

end Cslib.Complexity.SAT.PlanarCompile
