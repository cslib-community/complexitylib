/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SAT.Planar.PairedCorrectness
public import Complexity.Logics.Propositional.CNF.Compact.ModelCount
import Complexity.Computability.Complexity.Problems.SAT.Planar.PathAssignments
import Mathlib.Data.List.GetD

/-!
# Parsimony of the actual paired-port compiler

For width-three inputs with at most three literal occurrences per variable, every satisfying
source assignment has a satisfying output extension. Its values on the occurring output
variables are uniquely determined by the source assignment. Conversely, reading the ordinary
source cells recovers the source assignment. Counts use only occurring variables on both sides.

## Main results

* `sourceVariable_mem_rawFormula`: every used source representative occurs in the actual output.
* `raw_assignments_agree_iff`: source and output agreement coincide for satisfying assignments.
* `exists_satisfying_extension`: every satisfying source assignment has an output extension.
* `modelCount_rawFormula`, `modelCount_formula`: the actual compiler preserves model counts.
* `satisfiable_formula_iff`: the corresponding satisfiability equivalence.

## References

These are original counting and assignment-correspondence proofs for `PairedCompile`.
-/

@[expose] public section

namespace Cslib.Complexity.SAT.ParsimoniousPlanar

open Cslib.Logic.PL Cslib.Logic.PL.CNF Orthogonal

/-- A used source variable has an indexed literal occurrence, including repeated literals. -/
private theorem exists_occurrence_of_mem_vars {φ : CNF ℕ} {v : ℕ} (hv : v ∈ φ.vars) :
    ∃ o ∈ Cslib.Logic.PL.occurrences φ, o.2.2.1 = v := by
  rw [← map_occurrences] at hv
  exact List.mem_map.mp hv

/-- Every used source cell is retained and receives an ordinary ring. -/
theorem source_cell_mem_ordinary {φ : CNF ℕ} {v : ℕ} (hv : v ∈ φ.vars) :
    Layout.center (φ.distinctVars.idxOf v) ∈ ordinaryCells φ := by
  obtain ⟨o, ho, rfl⟩ := exists_occurrence_of_mem_vars hv
  have hlen := PlanarCompile.occurrencePath_length_ge_two ho
  change 2 ≤ (occurrencePath φ o).length at hlen
  have hhead := (PlanarCompile.occurrencePath_endpoints ho).1
  change (occurrencePath φ o).head? = _ at hhead
  rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hhead
  have he := Option.some.inj hhead
  have hret : Layout.center (φ.distinctVars.idxOf o.2.2.1) ∈
      (occurrencePath φ o).dropLast := by
    rw [← he]
    have hi : 0 < (occurrencePath φ o).dropLast.length := by
      simp only [List.length_dropLast]
      omega
    rw [← List.getElem_dropLast hi]
    exact List.getElem_mem _
  exact (mem_ordinaryCells φ _).2
    ⟨⟨_, PlanarCompile.occurrencePath_mem_paths ho, hret⟩,
      PlanarCompile.source_center_not_crossing ho⟩

/-- Every used source representative is an occurring variable of the actual raw output. -/
theorem sourceVariable_mem_rawFormula {φ : CNF ℕ} {v : ℕ} (hv : v ∈ φ.vars) :
    (Layout.center (φ.distinctVars.idxOf v), Sum.inl (0, 0)) ∈ (rawFormula φ).vars := by
  have hp := source_cell_mem_ordinary hv
  have hm : (Layout.center (φ.distinctVars.idxOf v), Sum.inl (0, 0)) ∈
      CNF.vars ((ordinaryClauses (Layout.center (φ.distinctVars.idxOf v))).map Prod.fst) := by
    rw [map_fst_ordinaryClauses, CNF.vars_relabel]
    exact List.mem_map_of_mem (OrdinaryRing.variables_used (0, 0))
  obtain ⟨c, hc, b, hvar⟩ := CNF.mem_vars.mp hm
  obtain ⟨pc, hpc, rfl⟩ := List.mem_map.mp hc
  apply CNF.mem_vars.mpr
  refine ⟨pc.1, List.mem_map.mpr ⟨pc, ?_, rfl⟩, b, hvar⟩
  simp only [placedClauses, List.mem_append, List.mem_flatMap]
  exact Or.inl (Or.inl (Or.inr ⟨_, hp, hpc⟩))

private theorem pairedLinks_variable_value {V : Type*} (σ : V → Bool)
    (cells : List (PairedWire.Cell V)) (value : Bool)
    (h : ∀ c ∈ cells, ∀ lane, σ (c lane).1 = value ∧ σ (c lane).2 = value)
    {v : V} (hv : v ∈ (PairedWire.links cells).vars) : σ v = value := by
  obtain ⟨c, hc, b, hl⟩ := CNF.mem_vars.mp hv
  obtain ⟨p, hp, hc⟩ := List.mem_flatMap.mp hc
  have hm := List.of_mem_zip hp
  have hfirst := h p.1 hm.1
  have hnext := h p.2 (List.mem_of_mem_tail hm.2)
  simp only [PairedWire.gapClauses, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · rcases Clause.fst_mem_of_mem_imp hl with hv | hv
    · exact (congrArg σ (List.mem_singleton.mp hv)).trans (hfirst 0).2
    · exact (congrArg σ hv).trans (hnext 0).1
  · rcases Clause.fst_mem_of_mem_imp hl with hv | hv
    · exact (congrArg σ (List.mem_singleton.mp hv)).trans (hnext 1).1
    · exact (congrArg σ hv).trans (hfirst 1).2

/-- Source agreement determines every occurring raw output variable. Assignments outside the
formula's variable support are unrestricted. -/
theorem raw_assignments_agree {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3)
    {σ τ : Variable → Bool} (hσ : (rawFormula φ).eval σ = true)
    (hτ : (rawFormula φ).eval τ = true)
    (he : ∀ v ∈ φ.vars, sourceValue φ σ v = sourceValue φ τ v) :
    ∀ v ∈ (rawFormula φ).vars, σ v = τ v := by
  intro v hvar
  obtain ⟨c, hc, b, hl⟩ := CNF.mem_vars.mp hvar
  obtain ⟨pc, hpc, rfl⟩ := List.mem_map.mp hc
  simp only [placedClauses, List.mem_append, List.mem_flatMap] at hpc
  rcases hpc with ((hpc | ⟨p, hp, hpc⟩) | ⟨p, hp, hpc⟩) | ⟨o, ho, hpc⟩
  · obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp hpc
    obtain ⟨lr, hlr, heq⟩ := List.mem_map.mp hl
    obtain ⟨lj, hlj, rfl⟩ := List.mem_map.mp hlr
    have ho : (ci.2, lj.2, lj.1) ∈ Cslib.Logic.PL.occurrences φ :=
      List.mem_flatMap.mpr ⟨ci, hci, List.mem_map.mpr ⟨lj, hlj, rfl⟩⟩
    have heq' : (lastLiteral (crossingSites φ)
        (occurrencePath φ (ci.2, lj.2, lj.1)) lj.1.2).1.1 = v := congrArg Prod.fst heq
    rw [← heq']
    exact (lastLiteral_value hw hv hσ ho).trans
      ((he _ (variable_mem_of_mem_occurrences ho)).trans (lastLiteral_value hw hv hτ ho).symm)
  · obtain ⟨ci, _, rfl⟩ := List.mem_map.mp hpc
    obtain ⟨lit, _, heq⟩ := List.mem_map.mp hl
    have heq' : (p, Sum.inl lit.1) = v := congrArg Prod.fst heq
    rw [← heq']
    exact ordinary_assignments_agree hw hv hσ hτ he hp lit.1
  · obtain ⟨ci, _, rfl⟩ := List.mem_map.mp hpc
    obtain ⟨lit, _, heq⟩ := List.mem_map.mp hl
    have heq' : (p, Sum.inr lit.1) = v := congrArg Prod.fst heq
    rw [← heq']
    exact crossing_assignments_agree hw hv hσ hτ he hp lit.1
  · have hm : v ∈ CNF.vars ((links (crossingSites φ) (occurrencePath φ o)).map Prod.fst) :=
      CNF.mem_vars.mpr ⟨pc.1, List.mem_map.mpr ⟨pc, hpc, rfl⟩, b, hl⟩
    rw [map_fst_links] at hm
    exact (pairedLinks_variable_value σ _ _ (wire_values_source hw hv hσ ho) hm).trans
      ((he _ (variable_mem_of_mem_occurrences ho)).trans
        (pairedLinks_variable_value τ _ _ (wire_values_source hw hv hτ ho) hm).symm)

/-- Among satisfying assignments, agreement on raw variables is equivalent to agreement on the
occurring source variables read at their fixed source representatives. -/
theorem raw_assignments_agree_iff {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3)
    {σ τ : Variable → Bool} (hσ : (rawFormula φ).eval σ = true)
    (hτ : (rawFormula φ).eval τ = true) :
    (∀ v ∈ (rawFormula φ).vars, σ v = τ v) ↔
      ∀ v ∈ φ.vars, sourceValue φ σ v = sourceValue φ τ v :=
  ⟨fun he _ hm => he _ (sourceVariable_mem_rawFormula hm),
    raw_assignments_agree hw hv hσ hτ⟩

/-- Every satisfying source assignment extends to a satisfying raw output assignment with the
same source values. Together with `raw_assignments_agree_iff`, its occurring values are unique. -/
theorem exists_satisfying_extension {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3)
    (τ : ℕ → Bool) (hτ : φ.eval τ = true) :
    ∃ σ : Variable → Bool, (rawFormula φ).eval σ = true ∧
      ∀ v ∈ φ.vars, sourceValue φ σ v = τ v := by
  obtain ⟨σ, hcompat, hord, hcross⟩ := exists_compatible_assignment hw hv τ
  have hσ := eval_rawFormula_of_compatible τ σ hcompat hord hcross hτ
  refine ⟨σ, hσ, fun v hmem => ?_⟩
  obtain ⟨o, ho, rfl⟩ := exists_occurrence_of_mem_vars hmem
  obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil _ (wire_ne_nil ho)
  exact (wire_values_source hw hv hσ ho c hc 0).1.symm.trans (hcompat o ho c hc 0).1

/-- The actual raw compiler preserves satisfying-assignment counts under the source width and
literal-occurrence restrictions. Both sides count only occurring variables. -/
theorem modelCount_rawFormula (φ : CNF ℕ)
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3) :
    (rawFormula φ).modelCount = φ.modelCount := by
  refine CNF.modelCount_eq_card_filter
    (fun σ (v : φ.vars.toFinset) => sourceValue φ σ v)
    (fun τ => φ.eval (φ.extendAssignment τ) = true) (fun σ τ hσ hτ => ?_) fun τ => ?_
  · rw [funext_iff, Subtype.forall]
    simp only [List.mem_toFinset]
    exact (raw_assignments_agree_iff hw hv hσ hτ).symm
  · constructor
    · intro hτ
      obtain ⟨σ, hσ, he⟩ := exists_satisfying_extension hw hv (φ.extendAssignment τ) hτ
      exact ⟨σ, hσ, funext fun v => (he v (List.mem_toFinset.mp v.2)).trans
        (CNF.extendAssignment_of_mem _ (List.mem_toFinset.mp v.2))⟩
    · rintro ⟨σ, hσ, rfl⟩
      rw [CNF.eval_extendAssignment_restrict]
      exact eval_source_of_rawFormula hw hv hσ

/-- Compact natural-number labels preserve the raw compiler's exact model count. -/
theorem modelCount_formula (φ : CNF ℕ)
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3) :
    (formula φ).modelCount = φ.modelCount := by
  rw [formula, CNF.modelCount_compact, modelCount_rawFormula φ hw hv]

/-- The actual compact compiler preserves satisfiability under the source restrictions. -/
theorem satisfiable_formula_iff (φ : CNF ℕ)
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3) :
    (formula φ).Satisfiable ↔ φ.Satisfiable := by
  rw [← CNF.modelCount_pos_iff, ← CNF.modelCount_pos_iff, modelCount_formula φ hw hv]

end Cslib.Complexity.SAT.ParsimoniousPlanar
