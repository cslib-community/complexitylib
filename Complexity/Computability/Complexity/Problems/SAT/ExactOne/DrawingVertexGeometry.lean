/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SAT.ExactOne.DrawingPositions
public import Complexity.Computability.Complexity.Problems.SAT.ExactOne.DrawingEndpoints
public import Complexity.Computability.Complexity.Problems.SAT.ExactOne.GeometryProfilesCollar
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup

/-!
# Actual vertex geometry inside clause boxes

Private variables and clauses receive the common injective affine placement of their inner
profile. Source placeholders instead occupy outer boundary ports and are omitted from the
actual global vertex list.

## Main results

* `profileVariableIndex_lt`, `profileAuxiliaryIndex_not_terminal`: actual local index scopes.
* `clauseGeometry_auxiliary_point`: affine placement of every private variable.
* `prefix_variablePoint_injective`, `prefix_clausePoint_injective`,
  `prefix_variablePoint_ne_clausePoint`: distinct inner vertices remain distinct.

## References

These finite support and geometric indexing arguments are original.
-/

@[expose] public section

namespace Cslib.Complexity.SAT.ExactOne

open Cslib.Logic.PL Orthogonal

/-- The logical first-occurrence index is a valid geometric variable index. -/
theorem profileVariableIndex_lt (p : ClauseProfile)
    {v : CNF.PositiveExactOneCompile.Variable ℕ} (hv : v ∈ profileVariables p) :
    (profileVariables p).idxOf v < (profilePrefixGeometry p).variablePositions.length := by
  have hlen : (profilePrefixGeometry p).variablePositions.length = (profileVariables p).length := by
    simpa only [profilePrefixGeometry, LocalGeometry.toPrefix, List.length_map,
      List.length_zipIdx] using profileGeometry_variable_length p
  rw [hlen]
  exact List.idxOf_lt_length_of_mem hv

/-- A private logical variable cannot be one of the exposed source placeholders. -/
theorem profileAuxiliaryIndex_not_terminal (p : ClauseProfile)
    {v : CNF.PositiveExactOneCompile.Variable ℕ} (hv : v ∈ profileVariables p)
    (ha : ∀ n, v ≠ Sum.inl (Sum.inl n)) :
    (profileVariables p).idxOf v ∉ (profilePrefixGeometry p).terminalVariables := by
  intro ht
  change (profileVariables p).idxOf v ∈ (profileGeometry p).terminalVariables at ht
  have hm : v ∈ (profileGeometry p).terminalVariables.map
      (fun i => (profileVariables p).getD i (.inl (.inl 0))) := by
    refine List.mem_map.mpr ⟨(profileVariables p).idxOf v, ht, ?_⟩
    rw [List.getD_eq_getElem _ _ (List.idxOf_lt_length_of_mem hv), List.getElem_idxOf]
  rw [profileGeometry_terminals] at hm
  obtain ⟨n, _, he⟩ := List.mem_map.mp hm
  exact ha n he.symm

/-- Private variables receive the common affine placement of their actual inner points. -/
theorem clauseGeometry_auxiliary_point (φ : CNF ℕ) (d : Graph.OrthogonalDrawing)
    (i : ℕ) (c : Clause ℕ) {v : CNF.PositiveExactOneCompile.Variable ℕ}
    (hv : v ∈ profileVariables (clauseProfile c)) (ha : ∀ n, v ≠ Sum.inl (Sum.inl n)) :
    (clauseGeometry φ d i c).variablePosition ((profileVariables (clauseProfile c)).idxOf v) =
      collarPoint (collarReflected (clausePorts φ d i))
        ((profilePrefixGeometry (clauseProfile c)).variablePosition
          ((profileVariables (clauseProfile c)).idxOf v)) := by
  rw [clauseGeometry, collared_variablePoint _ _ (profileVariableIndex_lt _ hv),
    ite_eq_right (profileAuxiliaryIndex_not_terminal _ hv ha)]

/-- The coordinate lookup of an actual inner variable is injective. -/
theorem prefix_variablePoint_injective {g : LocalGeometry} (h : LocalGeometry.PrefixCheck g)
    {i j : ℕ} (hi : i < g.variablePositions.length) (hj : j < g.variablePositions.length)
    (he : g.variablePosition i = g.variablePosition j) : i = j := by
  have hn := (List.nodup_append.mp h.1).1
  simp only [LocalGeometry.variablePosition, List.getD_eq_getElem _ _ hi,
    List.getD_eq_getElem _ _ hj] at he
  exact hn.getElem_inj_iff.mp he

/-- The coordinate lookup of an actual inner clause is injective. -/
theorem prefix_clausePoint_injective {g : LocalGeometry} (h : LocalGeometry.PrefixCheck g)
    {i j : ℕ} (hi : i < g.clausePositions.length) (hj : j < g.clausePositions.length)
    (he : g.clausePosition i = g.clausePosition j) : i = j := by
  have hn := (List.nodup_append.mp h.1).2.1
  simp only [LocalGeometry.clausePosition, List.getD_eq_getElem _ _ hi,
    List.getD_eq_getElem _ _ hj] at he
  exact hn.getElem_inj_iff.mp he

/-- An actual inner variable and clause cannot occupy the same point. -/
theorem prefix_variablePoint_ne_clausePoint {g : LocalGeometry}
    (h : LocalGeometry.PrefixCheck g) {i j : ℕ}
    (hi : i < g.variablePositions.length) (hj : j < g.clausePositions.length) :
    g.variablePosition i ≠ g.clausePosition j := by
  have hn := (List.nodup_append.mp h.1).2.2
  have hvi : g.variablePosition i ∈ g.variablePositions := by
    simp only [LocalGeometry.variablePosition, List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi
  have hcj : g.clausePosition j ∈ g.clausePositions := by
    simp only [LocalGeometry.clausePosition, List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem hj
  exact hn _ hvi _ hcj

end Cslib.Complexity.SAT.ExactOne
