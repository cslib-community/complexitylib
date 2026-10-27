/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SAT.ExactOne.DrawingAssembly
public import Complexity.Computability.Complexity.Problems.SAT.ExactOne.DrawingRouteContacts
public import Complexity.Computability.Complexity.Problems.SAT.ExactOne.DrawingAvoidance
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup

/-!
# Validity of the actual positive exact-one drawing

Each actual output occurrence is identified with its finite local incidence. Source ports
splice into the original routes, and all contacts are checked on full real supports.

## Main results

* `positiveFormulaDrawing_valid`: all actual output vertices and routes satisfy the geometric
  incidence conditions.
* `positiveDrawing_isPlanarOrthogonalDrawing`: the emitted drawing realizes the actual compact
  positive exact-one formula.

## References

The global replacement and its continuous geometric correctness proof are original.
-/

@[expose] public section

namespace Cslib.Complexity.SAT.ExactOne

open Cslib.Logic.PL Orthogonal

/-- The actual occurrence-indexed compiler has exactly one clause point per output clause. -/
theorem positiveFormulaDrawing_clauseCount (φ : CNF ℕ) (d : Graph.OrthogonalDrawing) :
    (positiveFormulaDrawing φ d).clausePoints.length =
      (CNF.PositiveExactOneCompile.rawFormula φ).length := by
  simpa only [positiveFormulaDrawing, List.length_map] using
    congrArg List.length (positivePlacedClauses_formula φ d)

/-- Actual output clause positions identify their actual clause indices. -/
theorem positiveFormulaDrawing_clausePoint_injective {φ : CNF ℕ}
    {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph φ) d) {i j : ℕ}
    (hi : i < (CNF.PositiveExactOneCompile.rawFormula φ).length)
    (hj : j < (CNF.PositiveExactOneCompile.rawFormula φ).length)
    (he : (positiveFormulaDrawing φ d).clausePoints.getD i (0, 0) =
      (positiveFormulaDrawing φ d).clausePoints.getD j (0, 0)) : i = j := by
  have hlen := positiveFormulaDrawing_clauseCount φ d
  rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at he
  exact (positiveClausePositions_nodup hd).getElem_inj_iff.mp he

/-- A clause and its variable identify an actual output occurrence, since output clauses have
distinct variables. -/
theorem positiveFormulaDrawing_occurrence_injective (φ : CNF ℕ)
    {o t : Occurrence (CNF.PositiveExactOneCompile.Variable ℕ)}
    (ho : o ∈ Cslib.Logic.PL.occurrences (CNF.PositiveExactOneCompile.rawFormula φ))
    (ht : t ∈ Cslib.Logic.PL.occurrences (CNF.PositiveExactOneCompile.rawFormula φ))
    (hclause : o.1 = t.1) (hvar : o.2.2.1 = t.2.2.1) : o = t := by
  rcases o with ⟨i, j, l⟩
  rcases t with ⟨i', j', l'⟩
  change i = i' at hclause
  subst i'
  obtain ⟨hi, hj, hl⟩ := Cslib.Logic.PL.mem_occurrences.mp ho
  obtain ⟨_, hj', hl'⟩ := Cslib.Logic.PL.mem_occurrences.mp ht
  have hnd := CNF.PositiveExactOneCompile.nodup_rawFormula φ _ (List.getElem_mem hi)
  have he : (((CNF.PositiveExactOneCompile.rawFormula φ)[i]).map Prod.fst)[j]'(by
      simpa using hj) =
      (((CNF.PositiveExactOneCompile.rawFormula φ)[i]).map Prod.fst)[j']'(by simpa using hj') := by
    simpa only [List.getElem_map, ← hl, ← hl'] using hvar
  have hji : j = j' := hnd.getElem_inj_iff.mp he
  subst j'
  have hli : l = l' := hl.trans hl'.symm
  subst l'
  rfl

/-- Every actual route begins at its actual output clause and ends at its actual output variable. -/
theorem positiveFormulaDrawing_endpoints {φ : CNF ℕ} {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph φ) d)
    {o : Occurrence (CNF.PositiveExactOneCompile.Variable ℕ)}
    (ho : o ∈ Cslib.Logic.PL.occurrences (CNF.PositiveExactOneCompile.rawFormula φ)) :
    ((positiveFormulaDrawing φ d).incidenceRoute o).head? =
        some ((positiveFormulaDrawing φ d).clausePoints.getD o.1 (0, 0)) ∧
      ((positiveFormulaDrawing φ d).incidenceRoute o).getLast? =
        some ((positiveFormulaDrawing φ d).variablePoint o.2.2.1) := by
  obtain ⟨i, hi, e, he, hr, hc, hv⟩ := positiveFormulaDrawing_incidence φ d ho
  rw [hr, hc]
  change _ ∧ _ = some (positiveVariablePoint φ d o.2.2.1)
  rw [hv]
  exact positiveIncidenceRoute_endpoints hd hi (profilePrefixGeometry_check _) he

/-- Every actual output route is proper, orthogonal and continuously simple. -/
theorem positiveFormulaDrawing_regular {φ : CNF ℕ} {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph φ) d)
    {o : Occurrence (CNF.PositiveExactOneCompile.Variable ℕ)}
    (ho : o ∈ Cslib.Logic.PL.occurrences (CNF.PositiveExactOneCompile.rawFormula φ)) :
    IsOrthogonal ((positiveFormulaDrawing φ d).incidenceRoute o) ∧
      IsSimple ((positiveFormulaDrawing φ d).incidenceRoute o) := by
  obtain ⟨i, hi, e, he, hr, _, _⟩ := positiveFormulaDrawing_incidence φ d ho
  rw [hr]
  exact positiveIncidenceRoute_regular hd hi (profilePrefixGeometry_check _) he

/-- Full continuous contacts of distinct actual occurrences are their actual common endpoints. -/
theorem positiveFormulaDrawing_contacts {φ : CNF ℕ} {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph φ) d)
    {o t : Occurrence (CNF.PositiveExactOneCompile.Variable ℕ)}
    (ho : o ∈ Cslib.Logic.PL.occurrences (CNF.PositiveExactOneCompile.rawFormula φ))
    (ht : t ∈ Cslib.Logic.PL.occurrences (CNF.PositiveExactOneCompile.rawFormula φ))
    (hot : o ≠ t) {p : ℝ × ℝ}
    (hp : p ∈ support ((positiveFormulaDrawing φ d).incidenceRoute o))
    (hq : p ∈ support ((positiveFormulaDrawing φ d).incidenceRoute t)) :
    (o.2.2.1 = t.2.2.1 ∧ p = realPoint ((positiveFormulaDrawing φ d).variablePoint o.2.2.1)) ∨
      (o.1 = t.1 ∧ p = realPoint ((positiveFormulaDrawing φ d).clausePoints.getD o.1 (0, 0))) := by
  obtain ⟨i, hi, e, he, hr, hc, hv⟩ := positiveFormulaDrawing_incidence φ d ho
  obtain ⟨j, hj, f, hf, hs, hd', hw⟩ := positiveFormulaDrawing_incidence φ d ht
  have hne : (i, e) ≠ (j, f) := by
    intro hij
    have hij' : i = j := congrArg Prod.fst hij
    have hef : e = f := congrArg Prod.snd hij
    subst j
    subst f
    have hci := positiveFormulaDrawing_clausePoint_injective hd
      (Cslib.Logic.PL.mem_occurrences.mp ho).choose
      (Cslib.Logic.PL.mem_occurrences.mp ht).choose (hc.trans hd'.symm)
    exact hot (positiveFormulaDrawing_occurrence_injective φ ho ht hci (hv.trans hw.symm))
  rw [hr] at hp
  rw [hs] at hq
  rcases positiveIncidenceRoute_contacts hd hi hj (fun _ _ => profilePrefixGeometry_check _)
    he hf hne hp hq with h | h
  · obtain ⟨hij, hef, hp⟩ := h
    subst j
    have hpoints : (positiveFormulaDrawing φ d).clausePoints.getD o.1 (0, 0) =
        (positiveFormulaDrawing φ d).clausePoints.getD t.1 (0, 0) := by
      rw [hc, hd', hef]
    exact Or.inr ⟨positiveFormulaDrawing_clausePoint_injective hd
      (Cslib.Logic.PL.mem_occurrences.mp ho).choose
      (Cslib.Logic.PL.mem_occurrences.mp ht).choose hpoints, hc ▸ hp⟩
  · change profileVariableMap _ _ _ _ = profileVariableMap _ _ _ _ ∧ _ at h
    refine Or.inl ⟨hv.trans (h.1.trans hw.symm), ?_⟩
    change p = realPoint (positiveVariablePoint φ d o.2.2.1)
    rw [hv]
    exact h.2

/-- All actual output positions and full real route supports satisfy the incidence drawing laws. -/
theorem positiveFormulaDrawing_valid {φ : CNF ℕ} {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph φ) d) :
    (positiveFormulaDrawing φ d).Valid := by
  have hc := positiveFormulaDrawing_clauseCount φ d
  have hnd : (positiveFormulaDrawing φ d).positions.Nodup := by
    change ((positiveFormulaDrawing φ d).drawing).1.Nodup
    rw [positiveFormulaDrawing_drawing]
    exact positiveDrawing_positions_nodup hd
  have he := fun o ho => positiveFormulaDrawing_endpoints hd (o := o) ho
  have hcontacts := fun o ho t ht hot p hp hq =>
    positiveFormulaDrawing_contacts hd (o := o) (t := t) ho ht hot (p := p) hp hq
  refine ⟨hc, hnd, he, (fun o ho => (positiveFormulaDrawing_regular hd ho).1),
    (fun o ho => (positiveFormulaDrawing_regular hd ho).2), ?_, ?_, hcontacts⟩
  · exact FormulaDrawing.avoidsVariables_of_contacts hc hnd (fun o ho => (he o ho).2) hcontacts
  · apply FormulaDrawing.avoidsClauses_of_contacts hc hnd ?_ (fun o ho => (he o ho).1) hcontacts
    intro c hmem hnil
    have hlen := CNF.PositiveExactOneCompile.width_rawFormula φ c hmem
    rw [hnil] at hlen
    contradiction

/-- The emitted drawing realizes the incidence graph of the actual compact positive formula. -/
theorem positiveDrawing_isPlanarOrthogonalDrawing {φ : CNF ℕ} {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph φ) d) :
    Graph.IsPlanarOrthogonalDrawing
      (SAT.incidenceGraph (CNF.PositiveExactOneCompile.formula φ)) (positiveDrawing φ d) := by
  rw [← positiveFormulaDrawing_drawing φ d]
  exact FormulaDrawing.isPlanarOrthogonalDrawing_compact _ (positiveFormulaDrawing_valid hd)

end Cslib.Complexity.SAT.ExactOne
