/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SAT.ExactOne.DrawingData
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup

/-!
# Nonincident-vertex avoidance from actual occurrence contacts

Once every displayed variable and nonempty clause has its own incident route, pairwise contact
control already implies nonincident-vertex avoidance. The only possible ambiguity would identify
a variable point with a clause point; the distinct displayed positions exclude that ambiguity.

## Main results

* `FormulaDrawing.avoidsVariables_of_contacts`: used variable vertices cannot lie on other routes.
* `FormulaDrawing.avoidsClauses_of_contacts`: nonempty clause vertices cannot lie on other routes.

## References

These elementary consequences of occurrence-indexed drawing certificates are original.
-/

@[expose] public section

namespace Cslib.Complexity.SAT.ExactOne.FormulaDrawing

open Cslib.Logic.PL Orthogonal

variable {V : Type} [DecidableEq V] {φ : CNF V} {a : FormulaDrawing φ}

private theorem variablePoint_ne_clausePoint (hcount : a.clausePoints.length = φ.length)
    (hnd : a.positions.Nodup) {v : V} (hv : v ∈ φ.vars) {i : ℕ} (hi : i < φ.length) :
    a.variablePoint v ≠ a.clausePoints.getD i (0, 0) := by
  have hm : a.variablePoint v ∈ φ.distinctVars.map a.variablePoint :=
    List.mem_map_of_mem (CNF.mem_distinctVars.mpr hv)
  have hc : a.clausePoints.getD i (0, 0) ∈ a.clausePoints := by
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem (by omega)
  exact (List.nodup_append.mp hnd).2.2 _ hm _ hc

/-- Used variable vertices cannot lie on another incidence once actual endpoint contacts and
variable/clause separation have been checked. -/
theorem avoidsVariables_of_contacts (hcount : a.clausePoints.length = φ.length)
    (hnd : a.positions.Nodup)
    (hends : ∀ o ∈ Cslib.Logic.PL.occurrences φ,
      (a.incidenceRoute o).getLast? = some (a.variablePoint o.2.2.1))
    (hcontacts : ∀ o ∈ Cslib.Logic.PL.occurrences φ,
      ∀ t ∈ Cslib.Logic.PL.occurrences φ, o ≠ t →
        ∀ p ∈ support (a.incidenceRoute o), p ∈ support (a.incidenceRoute t) →
          (o.2.2.1 = t.2.2.1 ∧ p = realPoint (a.variablePoint o.2.2.1)) ∨
            (o.1 = t.1 ∧ p = realPoint (a.clausePoints.getD o.1 (0, 0)))) :
    ∀ o ∈ Cslib.Logic.PL.occurrences φ, ∀ v ∈ φ.vars,
      realPoint (a.variablePoint v) ∈ support (a.incidenceRoute o) → v = o.2.2.1 := by
  intro o ho v hv hp
  have hv' := hv
  rw [← Cslib.Logic.PL.map_occurrences] at hv'
  obtain ⟨t, ht, htv⟩ := List.mem_map.mp hv'
  by_cases hot : o = t
  · subst t
    exact htv.symm
  have hpt : realPoint (a.variablePoint v) ∈ support (a.incidenceRoute t) := by
    rw [← htv]
    exact Or.inl ⟨_, List.mem_of_getLast? (hends t ht), rfl⟩
  rcases hcontacts o ho t ht hot _ hp hpt with hc | hc
  · exact htv.symm.trans hc.1.symm
  · exact False.elim (variablePoint_ne_clausePoint hcount hnd hv
      (Cslib.Logic.PL.mem_occurrences.mp ho).choose (realPoint_injective hc.2))

/-- Every nonempty clause vertex avoids other incidence routes once actual endpoint contacts
and variable/clause separation have been checked. -/
theorem avoidsClauses_of_contacts (hcount : a.clausePoints.length = φ.length)
    (hnd : a.positions.Nodup) (hnonempty : ∀ c ∈ φ, c ≠ [])
    (hends : ∀ o ∈ Cslib.Logic.PL.occurrences φ,
      (a.incidenceRoute o).head? = some (a.clausePoints.getD o.1 (0, 0)))
    (hcontacts : ∀ o ∈ Cslib.Logic.PL.occurrences φ,
      ∀ t ∈ Cslib.Logic.PL.occurrences φ, o ≠ t →
        ∀ p ∈ support (a.incidenceRoute o), p ∈ support (a.incidenceRoute t) →
          (o.2.2.1 = t.2.2.1 ∧ p = realPoint (a.variablePoint o.2.2.1)) ∨
            (o.1 = t.1 ∧ p = realPoint (a.clausePoints.getD o.1 (0, 0)))) :
    ∀ o ∈ Cslib.Logic.PL.occurrences φ, ∀ i < φ.length,
      realPoint (a.clausePoints.getD i (0, 0)) ∈ support (a.incidenceRoute o) → i = o.1 := by
  intro o ho i hi hp
  have hlen : 0 < φ[i].length := List.length_pos_iff.mpr (hnonempty _ (List.getElem_mem hi))
  let t : Occurrence V := (i, 0, φ[i][0])
  have ht : t ∈ Cslib.Logic.PL.occurrences φ :=
    Cslib.Logic.PL.mem_occurrences.mpr ⟨hi, hlen, rfl⟩
  by_cases hot : o = t
  · exact (congrArg Prod.fst hot).symm
  have hpt : realPoint (a.clausePoints.getD i (0, 0)) ∈ support (a.incidenceRoute t) :=
    Or.inl ⟨_, List.mem_of_head? (hends t ht), rfl⟩
  rcases hcontacts o ho t ht hot _ hp hpt with hc | hc
  · exact False.elim (variablePoint_ne_clausePoint hcount hnd
      (Cslib.Logic.PL.variable_mem_of_mem_occurrences ho) hi (realPoint_injective hc.2).symm)
  · exact hc.1.symm

end Cslib.Complexity.SAT.ExactOne.FormulaDrawing
