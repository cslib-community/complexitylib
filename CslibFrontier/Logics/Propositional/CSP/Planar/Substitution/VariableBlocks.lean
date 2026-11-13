/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Planar.Substitution.Table
public import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.VariableCyclePartition
public import CslibFrontier.Computability.Complexity.Problems.CSP.IncidenceEnumeration
import CslibFrontier.Foundations.Data.List.KeyedFlatMap
import CslibFrontier.Foundations.Data.List.OfFnGetD
import Mathlib.Data.List.Sigma
import Mathlib.Data.List.GetD

/-!
# Exact source-incidence blocks and clockwise regrouping

The bounded scan for a source record selects its literal constraint-list position, regardless
of duplicate rows. Accepted source white cycles regroup these blocks in their supplied positive
cyclic order. The flattening only permutes source incidences; it does not identify repeated
variable names or replace the source rotation by a reflected or reconstructed order.
-/

public section

namespace Cslib.Complexity.CSP.GadgetRotation

open Cslib.Logic.PL Cslib.Logic.PL.CSP Graph

variable {Src Rel : Type}

/-- Scanning an actual indexed source incidence selects exactly its own copy and local port. -/
theorem blockAtRecord_occurrence (templates : Src → CSP Rel (Bool × ℕ))
    (freeBlocks : Src → List (List ℕ)) (F : CSP Src ℕ) (o : F.Occurrence) :
    blockAtRecord templates freeBlocks F (o.1.val, o.2.val) =
      shiftBlock (occurrencePrefix templates F o.1.val)
        ((freeBlocks o.relation).getD o.2.val []) := by
  unfold blockAtRecord
  exact List.flatMap_ite_key_eq F.zipIdx Prod.snd
    (fun entry => shiftBlock (occurrencePrefix templates F entry.2)
      ((freeBlocks entry.1.1).getD o.2.val []))
    (List.nodup_zipIdx_map_snd F)
    (a := (F[o.1.val], o.1.val))
    (List.mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_some_iff.mpr ⟨o.1.isLt, rfl⟩))

/-- Each actual even source-dart lookup retains that occurrence's own literal local block. -/
theorem incidenceBlock_occurrence (templates : Src → CSP Rel (Bool × ℕ))
    (freeBlocks : Src → List (List ℕ)) (F : CSP Src ℕ) (o : F.Occurrence) :
    incidenceBlock templates freeBlocks F (2 * incidenceEdgeIndex o) =
      shiftBlock (occurrencePrefix templates F o.1.val)
        ((freeBlocks o.relation).getD o.2.val []) := by
  unfold incidenceBlock
  have hd : 2 * incidenceEdgeIndex o / 2 = incidenceEdgeIndex o := by omega
  rw [hd, getD_occurrences_incidenceEdgeIndex]
  exact blockAtRecord_occurrence templates freeBlocks F o

/-- A source-variable block contains exactly the individual incidence blocks at that
original name. Every indexed repetition remains a separate selected source occurrence. -/
theorem mem_variableBlock_iff_occurrence (templates : Src → CSP Rel (Bool × ℕ))
    (freeBlocks : Src → List (List ℕ)) (F : CSP Src ℕ) (c : RotationCertificate)
    (hc : RotationCertificate.verifyRotation (incidenceGraph F) c = true)
    (v : ℕ) (hv : v ∈ F.vars) (index : ℕ) :
    index ∈ variableBlock templates freeBlocks F c v ↔
      ∃ o : F.Occurrence, o.var = v ∧ index ∈
        shiftBlock (occurrencePrefix templates F o.1.val)
          ((freeBlocks o.relation).getD o.2.val []) := by
  unfold variableBlock
  rw [CSP.map_occurrences]
  simp only [List.mem_flatMap, mem_first_variable_cycleWord_iff hc v hv]
  constructor
  · rintro ⟨dart, ⟨o, hd, hvar⟩, hm⟩
    rw [hd, incidenceBlock_occurrence] at hm
    exact ⟨o, hvar, hm⟩
  · rintro ⟨o, hvar, hm⟩
    refine ⟨2 * incidenceEdgeIndex o, ⟨o, rfl, hvar⟩, ?_⟩
    rwa [incidenceBlock_occurrence]

/-- Flattening the supplied source-variable cycles preserves every indexed source-incidence
block exactly once. Their clockwise order inside each variable remains the supplied one. -/
theorem flatten_variableBlocks_perm (templates : Src → CSP Rel (Bool × ℕ))
    (freeBlocks : Src → List (List ℕ)) (F : CSP Src ℕ) (c : RotationCertificate)
    (hc : RotationCertificate.verifyRotation (incidenceGraph F) c = true) :
    (F.distinctVars.flatMap (variableBlock templates freeBlocks F c)).Perm
      ((List.range F.occurrences.length).flatMap fun i =>
        incidenceBlock templates freeBlocks F (2 * i)) := by
  have h := List.Perm.flatMap_right (incidenceBlock templates freeBlocks F)
    (flatten_variableCycleWords_perm hc)
  unfold variableBlock
  simpa only [List.flatMap_assoc, CSP.map_occurrences, List.flatMap_map,
    Function.comp_def] using h

/-- The raw edge-index scan is exactly the typed occurrence scan of the selected free blocks. -/
theorem range_incidenceBlocks_eq (templates : Src → CSP Rel (Bool × ℕ))
    (freeBlocks : Src → List (List ℕ)) (F : CSP Src ℕ) :
    ((List.range F.occurrences.length).flatMap fun i =>
      incidenceBlock templates freeBlocks F (2 * i)) =
      (CSP.incidenceList F).flatMap fun o =>
        shiftBlock (occurrencePrefix templates F o.1.val)
          ((freeBlocks o.relation).getD o.2.val []) := by
  rw [← map_incidenceEdgeIndex_incidenceList, List.flatMap_map]
  simp only [incidenceBlock_occurrence]

/-- The complete source-incidence scan enumerates every free word in each copy exactly once.
The only arity premise is equality of the actual source scope and local free-word lengths. -/
theorem flatten_incidenceBlocks_eq (templates : Src → CSP Rel (Bool × ℕ))
    (freeBlocks : Src → List (List ℕ)) (F : CSP Src ℕ)
    (hfree : ∀ c ∈ F, (freeBlocks c.1).length = c.2.length) :
    ((List.range F.occurrences.length).flatMap fun i =>
      incidenceBlock templates freeBlocks F (2 * i)) =
      F.zipIdx.flatMap fun ⟨⟨relation, _⟩, i⟩ =>
        (freeBlocks relation).flatMap (shiftBlock (occurrencePrefix templates F i)) := by
  rw [range_incidenceBlocks_eq, CSP.incidenceList]
  conv_rhs => rw [← List.ofFn_getElem (xs := F.zipIdx)]
  simp only [List.flatten_eq_flatMap, List.flatMap_assoc, List.ofFn_eq_map,
    List.flatMap_map, List.length_zipIdx, List.getElem_zipIdx, Nat.zero_add,
    CSP.Occurrence.relation]
  apply List.flatMap_congr
  intro i _
  have hl := hfree F[i.val] (List.getElem_mem i.isLt)
  simp only [id_eq, List.flatMap_map, Fin.val_cast, Fin.getElem_fin]
  have he := List.ofFn_getD_eq_of_length [] hl
  simpa only [List.ofFn_eq_map, List.flatMap_map] using
    congrArg (List.flatMap (shiftBlock (occurrencePrefix templates F i.val))) he

end Cslib.Complexity.CSP.GadgetRotation
