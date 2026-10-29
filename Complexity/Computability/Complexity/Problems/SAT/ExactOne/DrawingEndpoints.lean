/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SAT.ExactOne.Drawing
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Abel

/-!
# Matching actual local and exterior clause-box endpoints

The selected local source slot ends at precisely the same integer point as the normalized,
scaled, trimmed original incidence. The far endpoint is the common actual source-variable
vertex, including when different source literal positions use the same variable.

## Main results

* `clauseGeometry_source_point`: actual local source-placeholder position.
* `positiveExterior_endpoints`: exact collar and shared-variable endpoints.

## References

These finite-coordinate matching and indexing proofs are original.
-/

@[expose] public section

namespace Cslib.Complexity.SAT.ExactOne

open Cslib.Logic.PL Orthogonal

/-- A valid local variable index resolves to its moved source port or its affine core point. -/
theorem collared_variablePoint (g : LocalGeometry) (s : PortAssignment)
    {v : ℕ} (hv : v < g.variablePositions.length) :
    (collaredPrefixGeometry g s).variablePosition v =
      if v ∈ g.terminalVariables then collarOuterPort (s.side (terminalIndex g v))
      else collarPoint (collarReflected s) (g.variablePosition v) := by
  unfold LocalGeometry.variablePosition collaredPrefixGeometry
  rw [List.getD_eq_getElem _ _ (by simpa using hv), List.getElem_map, List.getElem_zipIdx]
  simp only [Nat.zero_add]
  rw [List.getD_eq_getElem _ _ hv]

/-- An exposed local variable resolves to its prescribed outer collar midpoint. -/
theorem collared_variablePoint_terminal (g : LocalGeometry) (s : PortAssignment)
    {v : ℕ} (hv : v < g.variablePositions.length) (ht : v ∈ g.terminalVariables) :
    (collaredPrefixGeometry g s).variablePosition v =
      collarOuterPort (s.side (terminalIndex g v)) := by
  unfold LocalGeometry.variablePosition collaredPrefixGeometry
  rw [List.getD_eq_getElem _ _ (by simpa using hv), List.getElem_map, List.getElem_zipIdx]
  simp only [Nat.zero_add, ht, ↓reduceIte]

/-- Every actual local clause position receives the common affine core placement. -/
theorem collared_clausePoint (g : LocalGeometry) (s : PortAssignment)
    {i : ℕ} (hi : i < g.clausePositions.length) :
    (collaredPrefixGeometry g s).clausePosition i =
      collarPoint (collarReflected s) (g.clausePosition i) := by
  unfold LocalGeometry.clausePosition collaredPrefixGeometry
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map,
    List.getD_eq_getElem _ _ hi]

/-- The local source-slot position is the selected outer collar midpoint. -/
theorem clauseGeometry_source_point (φ : CNF ℕ) (d : Graph.OrthogonalDrawing)
    (i : ℕ) (c : Clause ℕ) (j : Fin 3) (hj : j.val < (profileSource (clauseProfile c)).length) :
    (clauseGeometry φ d i c).variablePosition
      ((profileVariables (clauseProfile c)).idxOf (Sum.inl (Sum.inl j.val))) =
        collarOuterPort ((clausePorts φ d i).side j) := by
  have hv := profileSource_terminal_index (clauseProfile c) j hj
  dsimp only at hv
  have hlen : (profilePrefixGeometry (clauseProfile c)).variablePositions.length =
      (profileGeometry (clauseProfile c)).variablePositions.length := by
    simp only [profilePrefixGeometry, LocalGeometry.toPrefix, List.length_map, List.length_zipIdx]
  have ht : (profileVariables (clauseProfile c)).idxOf (Sum.inl (Sum.inl j.val)) ∈
      (profilePrefixGeometry (clauseProfile c)).terminalVariables := hv.2.1
  rw [clauseGeometry, collared_variablePoint_terminal _ _ (by omega) ht]
  congr 2
  apply Fin.ext
  change ((profileGeometry (clauseProfile c)).terminalVariables.idxOf
    ((profileVariables (clauseProfile c)).idxOf (Sum.inl (Sum.inl j.val)))) % 3 = j.val
  rw [hv.2.2, Nat.mod_eq_of_lt j.isLt]

/-- The exterior source incidence begins at the actual selected collar midpoint. -/
theorem positiveExterior_head {φ : CNF ℕ} {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph φ) d) {i : ℕ}
    (hi : i < φ.length) (j : Fin 3) (hj : j.val < φ[i].length) :
    (positiveExterior φ d i j).head? =
      some (positiveBoxOrigin φ d i + collarOuterPort ((clausePorts φ d i).side j)) := by
  have he := (exteriorRoute_endpoints hd (sourceEdgeIndex_lt φ hi hj)
    positiveScale positiveRadius).1
  unfold positiveExterior translate
  rw [List.head?_map, he, Option.map_some]
  congr 1
  have hs : sourceStart (SAT.incidenceGraph φ) d (sourceEdgeIndex φ i j) =
      Graph.drawingPosition (SAT.incidenceGraph φ) d (φ.distinctVars.length + i) := by
    rw [sourceStart, sourceEdgeIndex_edge φ hi hj]
  rw [collarOuterPort_eq_center_add, clausePorts_side hd hi j hj]
  unfold literalSide
  rw [sideDirection_directionSide (sourceDirection_unit _ _ _)]
  rw [exteriorPort, hs]
  unfold positiveBoxOrigin positiveTranslation positiveRadius
  abel

/-- The exterior route ends at the actual shared source-variable vertex. -/
theorem positiveExterior_last {φ : CNF ℕ} {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph φ) d) {i j : ℕ}
    (hi : i < φ.length) (hj : j < φ[i].length) :
    (positiveExterior φ d i j).getLast? =
      some (positiveVariablePoint φ d (Sum.inl (Sum.inl φ[i][j].1))) := by
  have he := (exteriorRoute_endpoints hd (sourceEdgeIndex_lt φ hi hj)
    positiveScale positiveRadius).2
  have hv : φ[i][j].1 ∈ φ.vars := CNF.mem_vars.mpr
    ⟨φ[i], List.getElem_mem hi, φ[i][j].2, List.getElem_mem hj⟩
  unfold positiveExterior translate
  rw [List.getLast?_map, he, Option.map_some, positiveVariablePoint_source φ d hv]
  congr 1
  rw [sourceFinish, sourceEdgeIndex_edge φ hi hj]

/-- Actual inherited exterior routes have exactly the local port and common variable endpoints. -/
theorem positiveExterior_endpoints {φ : CNF ℕ} {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph φ) d) {i : ℕ}
    (hi : i < φ.length) (j : Fin 3) (hj : j.val < φ[i].length) :
    (positiveExterior φ d i j).head? =
        some (positiveBoxOrigin φ d i + collarOuterPort ((clausePorts φ d i).side j)) ∧
      (positiveExterior φ d i j).getLast? =
        some (positiveVariablePoint φ d (Sum.inl (Sum.inl φ[i][j].1))) :=
  ⟨positiveExterior_head hd hi j hj, positiveExterior_last hd hi hj⟩

end Cslib.Complexity.SAT.ExactOne
