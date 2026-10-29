/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SAT.ExactOne.DrawingData
public import Complexity.Computability.Complexity.Problems.SAT.ExactOne.DrawingPorts
public import Complexity.Computability.Complexity.Problems.SAT.ExactOne.DrawingProfiles
public import Complexity.Computability.Complexity.Problems.SAT.ExactOne.GeometryProfilesPrefixData
public import Complexity.Computability.Complexity.Problems.SAT.ExactOne.GeometryCollarGlue
import Mathlib.Data.List.GetD

/-!
# The actual positive exact-one drawing compiler

Every source clause is replaced by its positive exact-one profile with a collar matching the
source exit directions. Source variable vertices remain shared at scaled positions. Private
source placeholders are removed, and their incidences join the trimmed source routes.

## Main definitions

* `positiveDrawing`: finite drawing data for the actual positive exact-one output formula.
* `positivePlacedClauses`: clause records in the actual compiler's list order.

## Main results

* `positivePlacedClauses_formula`: exact agreement with the actual logical formula.

## References

The finite-profile assembly and its explicit placement are original.
-/

@[expose] public section

namespace Cslib.Complexity.SAT.ExactOne

open Cslib.Logic.PL Orthogonal

/-- The common radius of all collared positive clause replacements. -/
def positiveRadius : ℕ := 270000

/-- Dilation separates all closed clause boxes. -/
def positiveScale : ℕ := 1080000

/-- Translate away from the source coordinate axes. -/
def positiveTranslation : Point := (positiveRadius, positiveRadius)

/-- The collared local geometry selected for one original clause. -/
def clauseGeometry (φ : CNF ℕ) (d : Graph.OrthogonalDrawing) (i : ℕ) (c : Clause ℕ) :
    LocalGeometry :=
  collaredPrefixGeometry (profilePrefixGeometry (clauseProfile c)) (clausePorts φ d i)

/-- The lower-left corner of one replacement box. -/
def positiveBoxOrigin (φ : CNF ℕ) (d : Graph.OrthogonalDrawing) (i : ℕ) : Point :=
  positiveScale • Graph.drawingPosition (SAT.incidenceGraph φ) d (φ.distinctVars.length + i)

/-- The inherited route outside its own local replacement box. -/
def positiveExterior (φ : CNF ℕ) (d : Graph.OrthogonalDrawing) (i j : ℕ) : Route :=
  translate positiveTranslation
    (exteriorRoute positiveScale positiveRadius (SAT.incidenceGraph φ) d (sourceEdgeIndex φ i j))

/-- A source prefix joins its inherited route; an auxiliary prefix already ends at its variable. -/
def positiveIncidenceRoute (φ : CNF ℕ) (d : Graph.OrthogonalDrawing) (i : ℕ)
    (c : Clause ℕ) (e : LocalIncidence) : Route :=
  let stem := translate (positiveBoxOrigin φ d i) e.2.2
  match (profileVariables (clauseProfile c)).getD e.2.1 (.inl (.inl 0)) with
  | .inl (.inl j) => stem ++ (positiveExterior φ d i j).tail
  | _ => stem

/-- An actual clause, its position, and its literal routes in literal order. -/
abbrev PositivePlacedClause := Clause (CNF.PositiveExactOneCompile.Variable ℕ) × Point × List Route

/-- One original clause's output, using its actual global auxiliary offsets. -/
def positiveClauseBlock (φ : CNF ℕ) (d : Graph.OrthogonalDrawing) (i : ℕ) (c : Clause ℕ) :
    List PositivePlacedClause :=
  (profileFormula (clauseProfile c)).zipIdx.map fun a =>
    (a.1.relabel (profileVariableMap i (CNF.PositiveExactOneCompile.signedOffset φ i) c),
      positiveBoxOrigin φ d i + (clauseGeometry φ d i c).clausePosition a.2,
      ((clauseGeometry φ d i c).incidenceRoutes.filter fun e => e.1 == a.2).map
        (positiveIncidenceRoute φ d i c))

/-- Actual output clause records in source-block and local-clause order. -/
def positivePlacedClauses (φ : CNF ℕ) (d : Graph.OrthogonalDrawing) :
    List PositivePlacedClause :=
  φ.zipIdx.flatMap fun c => positiveClauseBlock φ d c.2 c.1

/-- Fresh-variable positions in one clause box; source placeholders are omitted. -/
def positiveAuxiliaryBlock (φ : CNF ℕ) (d : Graph.OrthogonalDrawing) (i : ℕ) (c : Clause ℕ) :
    List (CNF.PositiveExactOneCompile.Variable ℕ × Point) :=
  (profileVariables (clauseProfile c)).zipIdx.filterMap fun v =>
    match v.1 with
    | .inl (.inl _) => none
    | _ => some
        (profileVariableMap i (CNF.PositiveExactOneCompile.signedOffset φ i) c v.1,
          positiveBoxOrigin φ d i + (clauseGeometry φ d i c).variablePosition v.2)

/-- The finite position table for actual output auxiliaries. -/
def positiveAuxiliaryPositions (φ : CNF ℕ) (d : Graph.OrthogonalDrawing) :
    List (CNF.PositiveExactOneCompile.Variable ℕ × Point) :=
  φ.zipIdx.flatMap fun c => positiveAuxiliaryBlock φ d c.2 c.1

/-- Shared original-variable vertices are listed before the fresh-variable position records. -/
def positiveSourcePositions (φ : CNF ℕ) (d : Graph.OrthogonalDrawing) :
    List (CNF.PositiveExactOneCompile.Variable ℕ × Point) :=
  φ.distinctVars.map fun v => (.inl (.inl v), positiveScale •
    Graph.drawingPosition (SAT.incidenceGraph φ) d (φ.distinctVars.idxOf v) + positiveTranslation)

/-- The position table keeps both shared source vertices and fresh clause-box vertices. -/
def positivePositionTable (φ : CNF ℕ) (d : Graph.OrthogonalDrawing) :
    List (CNF.PositiveExactOneCompile.Variable ℕ × Point) :=
  positiveSourcePositions φ d ++ positiveAuxiliaryPositions φ d

/-- Read the position of an actual output variable from the finite position table. -/
def positiveVariablePoint (φ : CNF ℕ) (d : Graph.OrthogonalDrawing)
    (v : CNF.PositiveExactOneCompile.Variable ℕ) : Point :=
  ((positivePositionTable φ d).map Prod.snd).getD
    (((positivePositionTable φ d).map Prod.fst).idxOf v) (0, 0)

/-- The actual compact output drawing omits all private source-placeholder vertices. -/
def positiveDrawing (φ : CNF ℕ) (d : Graph.OrthogonalDrawing) : Graph.OrthogonalDrawing :=
  (((CNF.PositiveExactOneCompile.rawFormula φ).distinctVars.map (positiveVariablePoint φ d)) ++
    ((positivePlacedClauses φ d).map fun c => c.2.1),
    (positivePlacedClauses φ d).flatMap fun c => c.2.2)

private theorem source_table_lookup (vs : List ℕ)
    (tail : List (CNF.PositiveExactOneCompile.Variable ℕ × Point))
    (point : ℕ → Point) {v : ℕ} (hv : v ∈ vs) :
    (((vs.map fun w => (Sum.inl (Sum.inl w), point w)) ++ tail).map Prod.snd).getD
      ((((vs.map fun w => (Sum.inl (Sum.inl w), point w)) ++ tail).map Prod.fst).idxOf
        (Sum.inl (Sum.inl v))) (0, 0) = point v := by
  induction vs with
  | nil => simp at hv
  | cons w vs ih =>
    by_cases he : w = v
    · subst w
      simp [List.getD]
    · have hk : (Sum.inl (Sum.inl w) : CNF.PositiveExactOneCompile.Variable ℕ) ≠
          Sum.inl (Sum.inl v) := by simpa using he
      simp only [List.map_cons, List.cons_append, List.idxOf_cons_ne _ hk]
      simpa only [List.getD_cons_succ] using ih (List.mem_of_ne_of_mem (Ne.symm he) hv)

/-- A used source variable resolves to its common original scaled vertex. -/
theorem positiveVariablePoint_source (φ : CNF ℕ) (d : Graph.OrthogonalDrawing) {v : ℕ}
    (hv : v ∈ φ.vars) :
    positiveVariablePoint φ d (.inl (.inl v)) = positiveScale •
      Graph.drawingPosition (SAT.incidenceGraph φ) d (φ.distinctVars.idxOf v) +
        positiveTranslation := by
  unfold positiveVariablePoint positivePositionTable positiveSourcePositions
  exact source_table_lookup _ _ _ (CNF.mem_distinctVars.mpr hv)

private theorem table_lookup_of_mem
    (table : List (CNF.PositiveExactOneCompile.Variable ℕ × Point))
    (hnd : (table.map Prod.fst).Nodup) {v : CNF.PositiveExactOneCompile.Variable ℕ} {p : Point}
    (hm : (v, p) ∈ table) :
    (table.map Prod.snd).getD ((table.map Prod.fst).idxOf v) (0, 0) = p := by
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hm
  have hi' : i < (table.map Prod.fst).length := by simpa only [List.length_map] using hi
  have hidx := hnd.idxOf_getElem i hi'
  rw [List.getElem_map, he] at hidx
  rw [hidx, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, he]

/-- Any uniquely indexed position-table entry resolves to its prescribed actual point. -/
theorem positiveVariablePoint_of_mem (φ : CNF ℕ) (d : Graph.OrthogonalDrawing)
    (hnd : ((positivePositionTable φ d).map Prod.fst).Nodup)
    {v : CNF.PositiveExactOneCompile.Variable ℕ} {p : Point}
    (hm : (v, p) ∈ positivePositionTable φ d) : positiveVariablePoint φ d v = p :=
  table_lookup_of_mem _ hnd hm

/-- Geometric clause records retain the actual formula, variable names, and clause order. -/
theorem positivePlacedClauses_formula (φ : CNF ℕ) (d : Graph.OrthogonalDrawing) :
    (positivePlacedClauses φ d).map Prod.fst = CNF.PositiveExactOneCompile.rawFormula φ := by
  rw [rawFormula_eq_profiles]
  simp only [positivePlacedClauses, List.map_flatMap]
  simp only [List.flatMap_def]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro c _
  simp only [positiveClauseBlock, List.map_map, Function.comp_def, CNF.relabel]
  have he := congrArg (List.map (Clause.relabel
    (profileVariableMap c.2 (CNF.PositiveExactOneCompile.signedOffset φ c.2) c.1)))
      (List.zipIdx_map_fst 0 (profileFormula (clauseProfile c.1)))
  simpa only [List.map_map, Function.comp_def] using he

end Cslib.Complexity.SAT.ExactOne
