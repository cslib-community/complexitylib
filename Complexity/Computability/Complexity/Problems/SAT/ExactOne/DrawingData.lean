/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.Graph.OrthogonalDrawing
public import Complexity.Computability.Complexity.Problems.SAT.Incidence.Compact
public import Complexity.Logics.Propositional.CNF.Occurrence
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup

/-!
# Incidence-order assembly of clause-replacement drawings

The drawing lists follow the actual formula: variables use first-occurrence order, clauses use
list order, and routes use literal-occurrence order. This interface bridges local replacement
geometry to `Graph.IsPlanarOrthogonalDrawing` without changing the output incidence graph.

## Main definitions

* `FormulaDrawing`: variable positions, clause positions, and occurrence-indexed routes.
* `FormulaDrawing.drawing`: the finite lists of the actual incidence drawing.
* `FormulaDrawing.Valid`: continuous geometric conditions on those data.

## Main results

* `FormulaDrawing.isPlanarOrthogonalDrawing`: the assembled drawing has the actual incidence graph.
* `FormulaDrawing.isPlanarOrthogonalDrawing_compact`: compact numbering preserves that graph.

## References

The finite assembly and its indexing proofs are original.
-/

@[expose] public section

namespace Cslib.Complexity.SAT.ExactOne

open Cslib.Logic.PL Orthogonal

variable {V : Type} [DecidableEq V]

/-- Geometric data indexed by the variables, clauses, and literal positions of a fixed formula. -/
structure FormulaDrawing (φ : CNF V) where
  /-- The displayed position of each occurring variable. Values outside the support are ignored. -/
  variablePoint : V → Point
  /-- Clause positions, in formula-list order. -/
  clausePoints : List Point
  /-- A clause-to-variable route for every actual literal occurrence. -/
  incidenceRoute : Occurrence V → Route

namespace FormulaDrawing

/-- Variable vertices precede clause vertices in the actual incidence graph. -/
def positions {φ : CNF V} (a : FormulaDrawing φ) : List Point :=
  φ.distinctVars.map a.variablePoint ++ a.clausePoints

/-- Routes retain the actual formula's literal-occurrence order. -/
def routes {φ : CNF V} (a : FormulaDrawing φ) : List Route :=
  (Cslib.Logic.PL.occurrences φ).map a.incidenceRoute

/-- Finite drawing data for the actual listed incidence graph. -/
def drawing {φ : CNF V} (a : FormulaDrawing φ) : Graph.OrthogonalDrawing :=
  (a.positions, a.routes)

/-- Geometric replacement certificates are stated on actual literal occurrences, including
repeated literals and repeated clause records. All intersections concern full real supports. -/
structure Valid {φ : CNF V} (a : FormulaDrawing φ) : Prop where
  /-- There is exactly one displayed clause vertex per clause position. -/
  clauseCount : a.clausePoints.length = φ.length
  /-- No distinct formula vertices share their displayed positions. -/
  positionsNodup : a.positions.Nodup
  /-- Every route has the actual clause and variable endpoints. -/
  endpoints : ∀ o ∈ Cslib.Logic.PL.occurrences φ,
    (a.incidenceRoute o).head? = some (a.clausePoints.getD o.1 (0, 0)) ∧
      (a.incidenceRoute o).getLast? = some (a.variablePoint o.2.2.1)
  /-- Routes are proper and orthogonal. -/
  orthogonal : ∀ o ∈ Cslib.Logic.PL.occurrences φ, IsOrthogonal (a.incidenceRoute o)
  /-- Routes have no self-crossings or retracing. -/
  simple : ∀ o ∈ Cslib.Logic.PL.occurrences φ, IsSimple (a.incidenceRoute o)
  /-- Only the incident variable vertex can lie on a route. -/
  avoidsVariables : ∀ o ∈ Cslib.Logic.PL.occurrences φ, ∀ v ∈ φ.vars,
    realPoint (a.variablePoint v) ∈ support (a.incidenceRoute o) → v = o.2.2.1
  /-- Only the incident clause vertex can lie on a route. -/
  avoidsClauses : ∀ o ∈ Cslib.Logic.PL.occurrences φ, ∀ i < φ.length,
    realPoint (a.clausePoints.getD i (0, 0)) ∈ support (a.incidenceRoute o) → i = o.1
  /-- Different occurrence routes meet only at their shared actual variable or clause vertex. -/
  contacts : ∀ o ∈ Cslib.Logic.PL.occurrences φ,
    ∀ t ∈ Cslib.Logic.PL.occurrences φ, o ≠ t →
      ∀ p ∈ support (a.incidenceRoute o), p ∈ support (a.incidenceRoute t) →
        (o.2.2.1 = t.2.2.1 ∧ p = realPoint (a.variablePoint o.2.2.1)) ∨
          (o.1 = t.1 ∧ p = realPoint (a.clausePoints.getD o.1 (0, 0)))

private theorem idxOf_range_eq {i n : ℕ} (hi : i < n) : (List.range n).idxOf i = i := by
  have h := (List.nodup_range : (List.range n).Nodup).idxOf_getElem i
    (by simpa only [List.length_range] using hi)
  rw [List.getElem_range] at h
  exact h

/-- An occurring variable resolves to its supplied position in the actual graph. -/
theorem drawingPosition_variable {φ : CNF V} (a : FormulaDrawing φ) {v : V}
    (hv : v ∈ φ.vars) :
    Graph.drawingPosition (SAT.incidenceGraph φ) a.drawing (φ.distinctVars.idxOf v) =
      a.variablePoint v := by
  have hi := List.idxOf_lt_length_of_mem (CNF.mem_distinctVars.mpr hv)
  change a.positions.getD ((List.range _).idxOf (φ.distinctVars.idxOf v)) (0, 0) = _
  rw [idxOf_range_eq (by omega), positions]
  rw [List.getD_append _ _ _ _ (by simpa only [List.length_map] using hi)]
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using hi), List.getElem_map]
  congr 1
  exact List.getElem_idxOf hi

/-- A clause index resolves to its supplied position in the actual graph. -/
theorem drawingPosition_clause {φ : CNF V} (a : FormulaDrawing φ) (_ha : a.Valid)
    {i : ℕ} (hi : i < φ.length) :
    Graph.drawingPosition (SAT.incidenceGraph φ) a.drawing (φ.distinctVars.length + i) =
      a.clausePoints.getD i (0, 0) := by
  change a.positions.getD ((List.range _).idxOf (φ.distinctVars.length + i)) (0, 0) = _
  rw [idxOf_range_eq (by omega), positions]
  rw [List.getD_append_right _ _ _ _ (by simp only [List.length_map]; omega)]
  simp only [List.length_map, Nat.add_sub_cancel_left]

/-- The occurrence at an edge-list index is the same occurrence used to build its route. -/
theorem indexed_route {φ : CNF V} (a : FormulaDrawing φ) {i : ℕ}
    (hi : i < (SAT.incidenceGraph φ).2.length) :
    a.routes.getD i [] = a.incidenceRoute
      ((Cslib.Logic.PL.occurrences φ)[i]'(by simpa [SAT.incidenceGraph] using hi)) := by
  have hi' : i < (Cslib.Logic.PL.occurrences φ).length := by
    simpa [SAT.incidenceGraph] using hi
  rw [routes, List.getD_eq_getElem _ _ (by simpa using hi'), List.getElem_map]

/-- Local occurrence-indexed certificates give a drawing of the actual formula incidence graph. -/
theorem isPlanarOrthogonalDrawing {φ : CNF V} (a : FormulaDrawing φ) (ha : a.Valid) :
    Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph φ) a.drawing := by
  have hov (o : Occurrence V) (ho : o ∈ Cslib.Logic.PL.occurrences φ) : o.2.2.1 ∈ φ.vars := by
    rw [← Cslib.Logic.PL.map_occurrences]
    exact List.mem_map_of_mem ho
  have hei (i : ℕ) (hi : i < (SAT.incidenceGraph φ).2.length) :
      (SAT.incidenceGraph φ).2[i] =
        (φ.distinctVars.idxOf ((Cslib.Logic.PL.occurrences φ)[i]'(by
          simpa [SAT.incidenceGraph] using hi)).2.2.1,
        φ.distinctVars.length + ((Cslib.Logic.PL.occurrences φ)[i]'(by
          simpa [SAT.incidenceGraph] using hi)).1) := by
    simp only [SAT.incidenceGraph, List.getElem_map]
  refine ⟨?_, ?_, List.nodup_range, ha.positionsNodup,
    (fun _ => SAT.incidenceGraph_endpoints), (fun _ => SAT.incidenceGraph_loopless),
    ?_, ?_, ?_, ?_, ?_⟩
  · simp [drawing, positions, SAT.incidenceGraph, ha.clauseCount]
  · simp [drawing, routes, SAT.incidenceGraph]
  · intro i hi
    have hi' : i < (Cslib.Logic.PL.occurrences φ).length := by
      simpa [SAT.incidenceGraph] using hi
    let o := (Cslib.Logic.PL.occurrences φ)[i]
    have ho : o ∈ Cslib.Logic.PL.occurrences φ := List.getElem_mem hi'
    have hci : o.1 < φ.length := (Cslib.Logic.PL.mem_occurrences.mp ho).choose
    rw [hei i hi]
    change (_ = _ ∧ _ = _) ∨ (_ = _ ∧ _ = _)
    rw [drawingPosition_variable a (hov o ho), drawingPosition_clause a ha hci]
    exact Or.inr (by simpa only [drawing, indexed_route a hi] using ha.endpoints o ho)
  · intro i hi
    rw [show a.drawing.2 = a.routes from rfl, indexed_route a hi]
    exact ha.orthogonal _ (List.getElem_mem _)
  · intro i hi
    rw [show a.drawing.2 = a.routes from rfl, indexed_route a hi]
    exact ha.simple _ (List.getElem_mem _)
  · intro i hi v hv hp
    have hi' : i < (Cslib.Logic.PL.occurrences φ).length := by
      simpa [SAT.incidenceGraph] using hi
    let o := (Cslib.Logic.PL.occurrences φ)[i]
    have ho : o ∈ Cslib.Logic.PL.occurrences φ := List.getElem_mem hi'
    rw [show a.drawing.2 = a.routes from rfl, indexed_route a hi] at hp
    rw [hei i hi]
    have hv' : v < φ.distinctVars.length + φ.length := by simpa [SAT.incidenceGraph] using hv
    by_cases hvar : v < φ.distinctVars.length
    · let w := φ.distinctVars[v]
      have hw : w ∈ φ.vars := CNF.mem_distinctVars.mp (List.getElem_mem hvar)
      have hidx : φ.distinctVars.idxOf w = v := (CNF.nodup_distinctVars φ).idxOf_getElem v hvar
      rw [← hidx, drawingPosition_variable a hw] at hp
      have he := ha.avoidsVariables o ho w hw hp
      exact Or.inl (hidx.symm.trans (congrArg φ.distinctVars.idxOf he))
    · have hci : v - φ.distinctVars.length < φ.length := by omega
      have hvci : v = φ.distinctVars.length + (v - φ.distinctVars.length) := by omega
      rw [hvci, drawingPosition_clause a ha hci] at hp
      have he := ha.avoidsClauses o ho _ hci hp
      exact Or.inr (by change v = φ.distinctVars.length + o.1; omega)
  · intro i hi j hj hij p hp hq
    have hi' : i < (Cslib.Logic.PL.occurrences φ).length := by
      simpa [SAT.incidenceGraph] using hi
    have hj' : j < (Cslib.Logic.PL.occurrences φ).length := by
      simpa [SAT.incidenceGraph] using hj
    let o := (Cslib.Logic.PL.occurrences φ)[i]
    let t := (Cslib.Logic.PL.occurrences φ)[j]
    have ho : o ∈ Cslib.Logic.PL.occurrences φ := List.getElem_mem hi'
    have ht : t ∈ Cslib.Logic.PL.occurrences φ := List.getElem_mem hj'
    have hot : o ≠ t := fun h => hij ((Cslib.Logic.PL.occurrences_nodup φ).getElem_inj_iff.mp h)
    rw [show a.drawing.2 = a.routes from rfl, indexed_route a hi] at hp
    rw [show a.drawing.2 = a.routes from rfl, indexed_route a hj] at hq
    rw [hei i hi, hei j hj]
    rcases ha.contacts o ho t ht hot p hp hq with ⟨he, hp⟩ | ⟨he, hp⟩
    · refine ⟨φ.distinctVars.idxOf o.2.2.1, ?_, Or.inl rfl, Or.inl ?_, ?_⟩
      · have hidx := List.idxOf_lt_length_of_mem (CNF.mem_distinctVars.mpr (hov o ho))
        simp only [SAT.incidenceGraph, List.mem_range]
        omega
      · exact congrArg φ.distinctVars.idxOf he
      · rw [drawingPosition_variable a (hov o ho)]
        exact hp
    · refine ⟨φ.distinctVars.length + o.1, ?_, Or.inr rfl, Or.inr ?_, ?_⟩
      · have hci := (Cslib.Logic.PL.mem_occurrences.mp ho).choose
        simp only [SAT.incidenceGraph, List.mem_range]
        omega
      · exact congrArg (φ.distinctVars.length + ·) he
      · rw [drawingPosition_clause a ha (Cslib.Logic.PL.mem_occurrences.mp ho).choose]
        exact hp

/-- The same actual drawing certifies compact output labels, with no change in any graph record. -/
theorem isPlanarOrthogonalDrawing_compact {φ : CNF V} (a : FormulaDrawing φ) (ha : a.Valid) :
    Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph φ.compact) a.drawing := by
  rw [SAT.incidenceGraph_compact]
  exact a.isPlanarOrthogonalDrawing ha

end FormulaDrawing

end Cslib.Complexity.SAT.ExactOne
