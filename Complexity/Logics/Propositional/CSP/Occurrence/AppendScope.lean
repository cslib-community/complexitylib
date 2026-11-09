/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CSP.Occurrence
import Complexity.Logics.Propositional.CNF.ModelCount
import Mathlib.Data.List.GetD

/-!
# Actual occurrence coordinates for an appended scope

The old constraint occurrences and the new scope positions give disjoint coordinates on the
existing dependent `CSP.Occurrence` type. Repeated variables and identical constraints retain
their separate positions. The inverse is finite choice on these actual occurrence records;
this structural equivalence carries no runtime or planarity assertion.
-/

public section

namespace Cslib.Logic.PL.CSP

variable {Rel V : Type}

/-- The complete occurrence word consists of the old body and the appended indexed scope. -/
theorem occurrences_append_scope (F : CSP Rel V) (r : Rel) (scope : List V) :
    (F ++ [(r, scope)]).occurrences = F.occurrences ++
      scope.zipIdx.map (fun (v, j) => (F.length, j, v)) := by
  simp [CSP.occurrences, CSP.varCNF, Cslib.Logic.PL.occurrences, List.zipIdx_append,
    List.zipIdx_map, List.flatMap_append, List.map_flatMap, List.map_map, Function.comp_def]

/-- Inverse coordinates for actual valid occurrence records; no new occurrence model. -/
@[expose] noncomputable def occurrenceRecordEquiv (F : CSP Rel V) :
    F.Occurrence ≃ {record // record ∈ F.occurrences} :=
  Equiv.ofBijective (fun o => ⟨o.record, mem_occurrences.mpr ⟨o, rfl⟩⟩)
    ⟨fun _ _ h => Occurrence.record_injective (congrArg Subtype.val h), fun record => by
      obtain ⟨o, ho⟩ := mem_occurrences.mp record.property
      exact ⟨o, Subtype.ext ho⟩⟩

/-- The forward record coordinates are precisely the existing occurrence's original record. -/
theorem occurrenceRecordEquiv_apply (F : CSP Rel V) (o : F.Occurrence) :
    (occurrenceRecordEquiv F o).val = o.record := rfl

/-- Decoding a valid record recovers that very constraint/argument/variable triple. -/
theorem record_occurrenceRecordEquiv_symm (F : CSP Rel V)
    (record : {record // record ∈ F.occurrences}) :
    ((occurrenceRecordEquiv F).symm record).record = record.val :=
  congrArg Subtype.val ((occurrenceRecordEquiv F).apply_symm_apply record)

private def appendedScopeRecord (F : CSP Rel V) (scope : List V) :
    F.Occurrence ⊕ Fin scope.length → ℕ × ℕ × V :=
  Sum.elim Occurrence.record (fun j => (F.length, j.val, scope[j.val]))

private theorem appendedScopeRecord_mem (F : CSP Rel V) (r : Rel) (scope : List V)
    (o : F.Occurrence ⊕ Fin scope.length) :
    appendedScopeRecord F scope o ∈ (F ++ [(r, scope)]).occurrences := by
  rw [occurrences_append_scope, List.mem_append]
  cases o with
  | inl o => exact Or.inl (mem_occurrences.mpr ⟨o, rfl⟩)
  | inr j =>
    apply Or.inr
    exact List.mem_map.mpr ⟨(scope[j.val], j.val),
      List.mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem j.isLt), rfl⟩

private theorem appendedScopeRecord_bijective (F : CSP Rel V) (r : Rel) (scope : List V) :
    Function.Bijective (fun o : F.Occurrence ⊕ Fin scope.length =>
      (⟨appendedScopeRecord F scope o, appendedScopeRecord_mem F r scope o⟩ :
        {record // record ∈ (F ++ [(r, scope)]).occurrences})) := by
  constructor
  · intro a b he
    have h := congrArg Subtype.val he
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (Occurrence.record_injective h)
      | inr b =>
        have hc := congrArg Prod.fst h
        change a.1.val = F.length at hc
        exact (Nat.ne_of_lt a.1.isLt hc).elim
    | inr a =>
      cases b with
      | inl b =>
        have hc := congrArg Prod.fst h
        change F.length = b.1.val at hc
        exact (Nat.ne_of_lt b.1.isLt hc.symm).elim
      | inr b =>
        apply congrArg Sum.inr
        exact Fin.ext (congrArg (fun record => record.2.1) h)
  · intro record
    rcases record with ⟨record, hm⟩
    have hm' : record ∈ F.occurrences ∨
        record ∈ scope.zipIdx.map (fun (v, j) => (F.length, j, v)) := by
      simpa only [occurrences_append_scope, List.mem_append] using hm
    rcases hm' with hm' | hm'
    · obtain ⟨o, ho⟩ := mem_occurrences.mp hm'
      exact ⟨Sum.inl o, Subtype.ext ho⟩
    · obtain ⟨⟨v, j⟩, hj, he⟩ := List.mem_map.mp hm'
      obtain ⟨hjl, hjv⟩ := List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp hj)
      refine ⟨Sum.inr ⟨j, hjl⟩, Subtype.ext ?_⟩
      change (F.length, j, scope[j]) = record
      rw [hjv]
      exact he

/-- Original-body occurrences and the appended scope indices parametrize the exact original
occurrence type. Constraint and argument positions remain distinct when variable labels repeat. -/
noncomputable def appendScopeOccurrenceEquiv (F : CSP Rel V) (r : Rel) (scope : List V) :
    F.Occurrence ⊕ Fin scope.length ≃ (F ++ [(r, scope)]).Occurrence :=
  (Equiv.ofBijective (fun o =>
    (⟨appendedScopeRecord F scope o, appendedScopeRecord_mem F r scope o⟩ :
      {record // record ∈ (F ++ [(r, scope)]).occurrences}))
    (appendedScopeRecord_bijective F r scope)).trans (occurrenceRecordEquiv _).symm

/-- Old-body coordinates retain exactly their original positional record. -/
theorem record_appendScopeOccurrenceEquiv_inl (F : CSP Rel V) (r : Rel) (scope : List V)
    (o : F.Occurrence) :
    (appendScopeOccurrenceEquiv F r scope (Sum.inl o)).record = o.record := by
  exact record_occurrenceRecordEquiv_symm _ _

/-- New-scope coordinates retain the fresh constraint index and the actual selected variable. -/
theorem record_appendScopeOccurrenceEquiv_inr (F : CSP Rel V) (r : Rel) (scope : List V)
    (j : Fin scope.length) :
    (appendScopeOccurrenceEquiv F r scope (Sum.inr j)).record =
      (F.length, j.val, scope[j.val]) := by
  exact record_occurrenceRecordEquiv_symm _ _

/-- Function-indexed scopes use the same actual occurrence coordinates, without replacing
source scope positions by a set of variable names. -/
noncomputable def appendOfFnOccurrenceEquiv (F : CSP Rel V) (r : Rel) {n : ℕ}
    (scope : Fin n → V) : F.Occurrence ⊕ Fin n ≃ (F ++ [(r, List.ofFn scope)]).Occurrence :=
  (Equiv.sumCongr (Equiv.refl F.Occurrence)
    (finCongr (List.length_ofFn (f := scope)).symm)).trans
      (appendScopeOccurrenceEquiv F r (List.ofFn scope))

/-- Function-indexed old-body coordinates retain their actual original occurrence record. -/
theorem record_appendOfFnOccurrenceEquiv_inl (F : CSP Rel V) (r : Rel) {n : ℕ}
    (scope : Fin n → V) (o : F.Occurrence) :
    (appendOfFnOccurrenceEquiv F r scope (Sum.inl o)).record = o.record := by
  exact record_appendScopeOccurrenceEquiv_inl F r (List.ofFn scope) o

/-- The appended function-indexed scope has precisely its supplied variable at each position. -/
theorem record_appendOfFnOccurrenceEquiv_inr (F : CSP Rel V) (r : Rel) {n : ℕ}
    (scope : Fin n → V) (j : Fin n) :
    (appendOfFnOccurrenceEquiv F r scope (Sum.inr j)).record = (F.length, j.val, scope j) := by
  change (appendScopeOccurrenceEquiv F r (List.ofFn scope)
    (Sum.inr (finCongr (List.length_ofFn (f := scope)).symm j))).record = _
  rw [record_appendScopeOccurrenceEquiv_inr]
  simp only [List.getElem_ofFn, finCongr_apply, Fin.cast, Fin.eta]

end Cslib.Logic.PL.CSP
