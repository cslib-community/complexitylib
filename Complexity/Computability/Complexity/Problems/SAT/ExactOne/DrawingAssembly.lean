/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SAT.ExactOne.DrawingData
public import Complexity.Computability.Complexity.Problems.SAT.ExactOne.DrawingCounts
public import Complexity.Computability.Complexity.Problems.SAT.ExactOne.DrawingClauseVertices
import Complexity.Foundations.Data.List.Lookup
import Mathlib.Data.List.GetD

/-!
# Actual occurrence indices of the positive drawing

The local clause records are assembled in the output formula's order. The occurrence-indexed
view in this module retains precisely the emitted position and route lists.

## Main definitions

* `positiveFormulaDrawing`: the actual compiler indexed by actual output occurrences.

## Main results

* `positiveFormulaDrawing_drawing`: the indexed view equals the emitted drawing.

## References

The assembly and indexing proofs are original.
-/

@[expose] public section

namespace Cslib.Complexity.SAT.ExactOne

open Cslib.Logic.PL Orthogonal

/-- Index the emitted route lists by actual output clause and literal positions. -/
def positiveFormulaDrawing (φ : CNF ℕ) (d : Graph.OrthogonalDrawing) :
    FormulaDrawing (CNF.PositiveExactOneCompile.rawFormula φ) where
  variablePoint := positiveVariablePoint φ d
  clausePoints := (positivePlacedClauses φ d).map fun pc => pc.2.1
  incidenceRoute := fun o =>
    ((positivePlacedClauses φ d).getD o.1 ([], (0, 0), [])).2.2.getD o.2.1 []

private theorem placed_occurrence_routes (pcs : List PositivePlacedClause)
    (hc : ∀ pc ∈ pcs, pc.2.2.length = pc.1.length) :
    ((Cslib.Logic.PL.occurrences (pcs.map Prod.fst)).map fun o =>
      (pcs.getD o.1 ([], (0, 0), [])).2.2.getD o.2.1 []) = pcs.flatMap fun pc => pc.2.2 := by
  rw [Cslib.Logic.PL.occurrences, List.zipIdx_map]
  simp only [List.flatMap_map, List.map_flatMap, List.map_map, Function.comp_def]
  have he : pcs.flatMap (fun pc => pc.2.2) =
      pcs.zipIdx.flatMap (fun pc => pc.1.2.2) := by
    have h := congrArg (List.flatMap (fun pc : PositivePlacedClause => pc.2.2))
      (List.zipIdx_map_fst (l := pcs) (i := 0))
    simpa only [List.flatMap_map, Function.comp_def] using h.symm
  rw [he]
  simp only [List.flatMap_def]
  apply congrArg List.flatten
  apply List.map_congr_left
  rintro ⟨pc, i⟩ hi
  have hi' := List.mem_zipIdx_iff_getElem?.mp hi
  have hg : pcs.getD i ([], (0, 0), []) = pc := by
    rw [List.getD_eq_getElem?_getD, hi']
    rfl
  change pc.1.zipIdx.map (fun x => (pcs.getD i ([], (0, 0), [])).2.2.getD x.2 []) = _
  rw [hg]
  exact List.map_getD_zipIdx pc.1 pc.2.2 [] (hc pc (List.mem_of_getElem? hi'))

/-- The occurrence-indexed view has exactly the compiler's actual position and route lists. -/
theorem positiveFormulaDrawing_drawing (φ : CNF ℕ) (d : Graph.OrthogonalDrawing) :
    (positiveFormulaDrawing φ d).drawing = positiveDrawing φ d := by
  apply Prod.ext
  · rfl
  · change ((Cslib.Logic.PL.occurrences (CNF.PositiveExactOneCompile.rawFormula φ)).map
      fun o => ((positivePlacedClauses φ d).getD o.1 ([], (0, 0), [])).2.2.getD o.2.1 []) = _
    rw [← positivePlacedClauses_formula φ d]
    exact placed_occurrence_routes _ (fun pc hpc => positivePlacedClauses_route_count φ d hpc)

/-- Each actual output occurrence selects its literal and route in the same placed clause. -/
theorem positiveFormulaDrawing_occurrence (φ : CNF ℕ) (d : Graph.OrthogonalDrawing)
    {o : Occurrence (CNF.PositiveExactOneCompile.Variable ℕ)}
    (ho : o ∈ Cslib.Logic.PL.occurrences (CNF.PositiveExactOneCompile.rawFormula φ)) :
    ∃ pc ∈ positivePlacedClauses φ d,
      pc.2.1 = (positiveFormulaDrawing φ d).clausePoints.getD o.1 (0, 0) ∧
        (o.2.2, (positiveFormulaDrawing φ d).incidenceRoute o) ∈ pc.1.zip pc.2.2 := by
  obtain ⟨hi, hj, hl⟩ := Cslib.Logic.PL.mem_occurrences.mp ho
  have hip : o.1 < (positivePlacedClauses φ d).length := by
    have h := congrArg List.length (positivePlacedClauses_formula φ d)
    simp only [List.length_map] at h
    omega
  let pc := (positivePlacedClauses φ d)[o.1]
  have hpc : pc ∈ positivePlacedClauses φ d := List.getElem_mem hip
  have hec : pc.1 = (CNF.PositiveExactOneCompile.rawFormula φ)[o.1] := by
    have h := congrArg (fun cs => cs.getD o.1 []) (positivePlacedClauses_formula φ d)
    simpa only [List.getD_eq_getElem _ _ (show o.1 <
      ((positivePlacedClauses φ d).map Prod.fst).length by simpa using hip), List.getElem_map,
      List.getD_eq_getElem _ _ hi] using h
  have hjp : o.2.1 < pc.1.length := by simpa only [hec] using hj
  have hjr : o.2.1 < pc.2.2.length := by rw [positivePlacedClauses_route_count φ d hpc]; exact hjp
  refine ⟨pc, hpc, ?_, ?_⟩
  · change pc.2.1 = ((positivePlacedClauses φ d).map (fun pc => pc.2.1)).getD o.1 (0, 0)
    rw [List.getD_eq_getElem _ _ (by simpa using hip), List.getElem_map]
  · have hr : (positiveFormulaDrawing φ d).incidenceRoute o = pc.2.2[o.2.1] := by
      change ((positivePlacedClauses φ d).getD o.1 ([], (0, 0), [])).2.2.getD o.2.1 [] = _
      rw [List.getD_eq_getElem _ _ hip, List.getD_eq_getElem _ _ hjr]
    have hli : o.2.2 = pc.1[o.2.1] := by
      have h := congrArg (fun cs => cs.getD o.2.1 (.inl (.inl 0), true)) hec
      simpa only [List.getD_eq_getElem _ _ hjp, List.getD_eq_getElem _ _ hj, hl] using h.symm
    rw [hr, hli]
    have hz := List.getElem_mem (l := pc.1.zip pc.2.2) (n := o.2.1)
      (by simp only [List.length_zip]; omega)
    rw [List.getElem_zip] at hz
    exact hz

/-- Geometry transformations retain the literal-to-variable index of every profile incidence. -/
theorem clauseGeometry_literal_indices (φ : CNF ℕ) (d : Graph.OrthogonalDrawing)
    (i : ℕ) (c : Clause ℕ) (j : Fin 22)
    {l : Literal (CNF.PositiveExactOneCompile.Variable ℕ)} {e : LocalIncidence}
    (he : (l, e) ∈ ((profileFormula (clauseProfile c)).getD j.val []).zip
      ((clauseGeometry φ d i c).incidenceRoutes.filter fun e => e.1 == j.val)) :
    e.2.1 = (profileVariables (clauseProfile c)).idxOf l.1 := by
  simp only [clauseGeometry, collaredPrefixGeometry, profilePrefixGeometry,
    LocalGeometry.toPrefix, List.filter_map, List.map_map, Function.comp_def,
    List.zip_map_right] at he
  obtain ⟨⟨lit, old⟩, hold, hle⟩ := List.mem_map.mp he
  have hidx := profileGeometry_literal_indices (clauseProfile c) j hold
  have hli : lit = l := congrArg Prod.fst hle
  have hei : old.2.1 = e.2.1 := congrArg (fun a => a.2.2.1) hle
  exact hei.symm.trans (hli ▸ hidx)

/-- A paired actual literal and route comes from its certified local incidence record. -/
theorem positiveClauseBlock_incidence (φ : CNF ℕ) (d : Graph.OrthogonalDrawing)
    (i : ℕ) (c : Clause ℕ) {pc : PositivePlacedClause}
    (hpc : pc ∈ positiveClauseBlock φ d i c)
    {l : Literal (CNF.PositiveExactOneCompile.Variable ℕ)} {r : Route}
    (hlr : (l, r) ∈ pc.1.zip pc.2.2) :
    ∃ e ∈ (clauseGeometry φ d i c).incidenceRoutes,
      r = positiveIncidenceRoute φ d i c e ∧
        pc.2.1 = positiveBoxOrigin φ d i + (clauseGeometry φ d i c).clausePosition e.1 ∧
        l.1 = profileVariableMap i (CNF.PositiveExactOneCompile.signedOffset φ i) c
          ((profileVariables (clauseProfile c)).getD e.2.1 (.inl (.inl 0))) := by
  obtain ⟨⟨cl, j⟩, hj, rfl⟩ := List.mem_map.mp hpc
  change (l, r) ∈ (cl.relabel _).zip (List.map _ _) at hlr
  simp only [Clause.relabel, List.zip_map_left, List.zip_map_right, List.map_map,
    Function.comp_def] at hlr
  obtain ⟨⟨lit, e⟩, hle, hnames⟩ := List.mem_map.mp hlr
  have hparts := List.of_mem_zip hle
  have he := List.mem_filter.mp hparts.2
  have hei : e.1 = j := beq_iff_eq.mp he.2
  have hl : l.1 = profileVariableMap i (CNF.PositiveExactOneCompile.signedOffset φ i) c lit.1 :=
    (congrArg (fun a => a.1.1) hnames).symm
  have hr : r = positiveIncidenceRoute φ d i c e := (congrArg Prod.snd hnames).symm
  have hget := List.mem_zipIdx_iff_getElem?.mp hj
  have hjlt := (List.getElem?_eq_some_iff.mp hget).choose
  have hbound := profileFormula_length_le (clauseProfile c)
  have hecl : (profileFormula (clauseProfile c)).getD j [] = cl := by
    rw [List.getD_eq_getElem?_getD, hget]
    rfl
  have hidx := clauseGeometry_literal_indices φ d i c ⟨j, by omega⟩
    (hecl ▸ hle)
  have hlvar : lit.1 ∈ profileVariables (clauseProfile c) := by
    apply CNF.mem_distinctVars.mpr
    exact CNF.mem_vars.mpr ⟨cl, List.mem_of_getElem? hget, lit.2, hparts.1⟩
  refine ⟨e, he.1, hr, ?_, ?_⟩
  · simp only [hei]
  · rw [hidx, List.getD_eq_getElem _ _ (List.idxOf_lt_length_of_mem hlvar),
      List.getElem_idxOf (List.idxOf_lt_length_of_mem hlvar), hl]

/-- Every actual output occurrence has a source-clause owner and a certified local route. -/
theorem positiveFormulaDrawing_incidence (φ : CNF ℕ) (d : Graph.OrthogonalDrawing)
    {o : Occurrence (CNF.PositiveExactOneCompile.Variable ℕ)}
    (ho : o ∈ Cslib.Logic.PL.occurrences (CNF.PositiveExactOneCompile.rawFormula φ)) :
    ∃ (i : ℕ) (hi : i < φ.length) (e : LocalIncidence),
      e ∈ (clauseGeometry φ d i φ[i]).incidenceRoutes ∧
        (positiveFormulaDrawing φ d).incidenceRoute o = positiveIncidenceRoute φ d i φ[i] e ∧
        (positiveFormulaDrawing φ d).clausePoints.getD o.1 (0, 0) =
          positiveBoxOrigin φ d i + (clauseGeometry φ d i φ[i]).clausePosition e.1 ∧
        o.2.2.1 = profileVariableMap i (CNF.PositiveExactOneCompile.signedOffset φ i) φ[i]
          ((profileVariables (clauseProfile φ[i])).getD e.2.1 (.inl (.inl 0))) := by
  obtain ⟨pc, hpc, hp, hlr⟩ := positiveFormulaDrawing_occurrence φ d ho
  obtain ⟨⟨c, i⟩, hci, hpc⟩ := List.mem_flatMap.mp hpc
  obtain ⟨hi, hc⟩ := List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp hci)
  change i < φ.length at hi
  change φ[i] = c at hc
  subst c
  obtain ⟨e, he, hr, hpos, hvar⟩ := positiveClauseBlock_incidence φ d i φ[i] hpc hlr
  exact ⟨i, hi, e, he, hr, hp.symm.trans hpos, hvar⟩

end Cslib.Complexity.SAT.ExactOne
