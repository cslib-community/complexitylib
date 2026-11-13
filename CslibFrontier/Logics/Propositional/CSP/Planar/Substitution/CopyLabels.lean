/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Planar.Substitution.CopyPositions
public import CslibFrontier.Logics.Propositional.CSP.Planar.Substitution.BoundaryPartition
public import CslibFrontier.Computability.Complexity.Problems.CSP.IncidenceEnumeration
import Mathlib.Data.List.GetD

/-!
# Actual target labels at copied gadget occurrences

The target getters follow the existing template and instantiation operations. Free ports read
the actual source scope; auxiliary names retain their source-copy and local indices. A fixed
auxiliary bound separates all private copies, without requiring distinct source names or an
injection of a source scope. Binary labels are data, not enumeration bounds.
-/

public section

namespace Cslib.Complexity.CSP.GadgetRotation

open Cslib.Logic.PL Cslib.Logic.PL.CSP OrderedBoundary

variable {Src Rel : Type} {arity : Rel → ℕ} {sem : Rel → List Bool → Bool}
  {srcArity : Src → ℕ} {srcSem : Src → List Bool → Bool}

/-- A template's occurrence getter retains the canonical free/auxiliary port coordinates. -/
theorem getElem_template_vars_occurrence {n : ℕ} {R : Set (Fin n → Bool)}
    (g : PPGadget arity sem R) (o : g.body.Occurrence) :
    g.template.vars[incidenceEdgeIndex o]'(by
      simpa only [PPGadget.template, vars_relabel, List.length_map] using
        incidenceEdgeIndex_lt_vars o) =
      Sum.elim (fun i => (false, i.val)) (fun j => (true, j.val)) o.var := by
  simp only [PPGadget.template, vars_relabel, List.getElem_map,
    getElem_vars_incidenceEdgeIndex]

/-- Each typed gadget occurrence shifts to a bounded actual target position. -/
theorem copyIndex_lt_gadgetOccurrence
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (B : ℕ) (F : CSP Src ℕ) {i : ℕ} (hi : i < F.length)
    (o : (gadgets F[i].1).body.Occurrence) :
    occurrencePrefix (fun r => (gadgets r).template) F i + incidenceEdgeIndex o <
      (replaceGadgets B (fun r => (gadgets r).template) F).vars.length := by
  apply copyIndex_lt B _ F hi
  simpa only [PPGadget.template, vars_relabel, List.length_map] using
    incidenceEdgeIndex_lt_vars o

/-- The actual replacement variable at a copied occurrence is its original instantiated name. -/
theorem getElem_vars_gadgetCopy
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (B : ℕ) (F : CSP Src ℕ) {i : ℕ} (hi : i < F.length)
    (o : (gadgets F[i].1).body.Occurrence) :
    (replaceGadgets B (fun r => (gadgets r).template) F).vars[
      occurrencePrefix (fun r => (gadgets r).template) F i + incidenceEdgeIndex o]'
        (copyIndex_lt_gadgetOccurrence gadgets B F hi o) =
      Sum.elim (fun a => 2 * F[i].2.getD a.val 0)
        (fun j => 2 * (B * i + j.val) + 1) o.var := by
  have hj : incidenceEdgeIndex o < (gadgets F[i].1).template.vars.length := by
    simpa only [PPGadget.template, vars_relabel, List.length_map] using
      incidenceEdgeIndex_lt_vars o
  have h := getElem_vars_copyIndex B (fun r => (gadgets r).template) F hi hj
  rw [getElem_template_vars_occurrence] at h
  cases hvar : o.var with
  | inl a => simpa only [hvar, Sum.elim_inl, Bool.false_eq_true, ite_false] using h
  | inr j => simpa only [hvar, Sum.elim_inr, ite_true] using h

/-- Every bounded target position has an actual typed occurrence in one original gadget
copy. This recovers positions through the existing public incidence-index lookup. -/
theorem exists_gadgetCopy
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (B : ℕ) (F : CSP Src ℕ) {index : ℕ}
    (hi : index < (replaceGadgets B (fun r => (gadgets r).template) F).vars.length) :
    ∃ (i : ℕ) (hi : i < F.length) (o : (gadgets F[i].1).body.Occurrence),
      occurrencePrefix (fun r => (gadgets r).template) F i + incidenceEdgeIndex o = index := by
  obtain ⟨i, hi, j, hj, he⟩ := exists_copyIndex B (fun r => (gadgets r).template) F hi
  have hb : j < (incidenceGraph (gadgets F[i].1).body).edges.length := by
    simp only [PPGadget.template, vars_relabel, List.length_map] at hj
    simpa only [incidenceGraph_edges, List.length_map, ← CSP.map_occurrences,
      List.length_map] using hj
  obtain ⟨o, ho⟩ := exists_incidenceEdgeIndex (F := (gadgets F[i].1).body) j hb
  exact ⟨i, hi, o, by rw [ho]; exact he.symm⟩

/-- Every copied variable-word entry is a bounded target position carrying precisely its
instantiated canonical label. The same witness supplies the position and the target getter. -/
theorem shifted_boundaryBlock_spec
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (witnesses : ∀ r, GadgetWitness (gadgets r)) (B : ℕ) (F : CSP Src ℕ)
    {i : ℕ} (hi : i < F.length)
    (v : Fin (srcArity F[i].1) ⊕ Fin (gadgets F[i].1).numAux) {index : ℕ}
    (hm : index ∈ shiftBlock (occurrencePrefix (fun r => (gadgets r).template) F i)
      (boundaryBlock (gadgets F[i].1) (witnesses F[i].1) v)) :
    index < (replaceGadgets B (fun r => (gadgets r).template) F).vars.length ∧
      (replaceGadgets B (fun r => (gadgets r).template) F).vars.getD index 0 =
        Sum.elim (fun a => 2 * F[i].2.getD a.val 0)
          (fun j => 2 * (B * i + j.val) + 1) v := by
  obtain ⟨o, ho, hvar⟩ := (mem_shiftBlock_boundaryBlock_iff _ _ _ v index).mp hm
  rw [← ho]
  refine ⟨copyIndex_lt_gadgetOccurrence gadgets B F hi o, ?_⟩
  rw [List.getD_eq_getElem _ _ (copyIndex_lt_gadgetOccurrence gadgets B F hi o),
    getElem_vars_gadgetCopy, hvar]

/-- A shifted free block reads exactly its source-scope name, including repeated names. -/
theorem getD_vars_of_mem_shifted_freeBlock
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (witnesses : ∀ r, GadgetWitness (gadgets r)) (B : ℕ) (F : CSP Src ℕ)
    {i : ℕ} (hi : i < F.length) (a : Fin (srcArity F[i].1)) {index : ℕ}
    (hm : index ∈ shiftBlock (occurrencePrefix (fun r => (gadgets r).template) F i)
      ((freeBoundaryBlocks (gadgets F[i].1) (witnesses F[i].1)).getD a.val [])) :
    (replaceGadgets B (fun r => (gadgets r).template) F).vars.getD index 0 =
      2 * F[i].2.getD a.val 0 := by
  simpa only [Sum.elim_inl] using
    (shifted_boundaryBlock_spec gadgets witnesses B F hi (Sum.inl a) hm).2

/-- A shifted auxiliary block reads its actual private copy index and local auxiliary label. -/
theorem getD_vars_of_mem_shifted_auxiliaryBlock
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (witnesses : ∀ r, GadgetWitness (gadgets r)) (B : ℕ) (F : CSP Src ℕ)
    {i : ℕ} (hi : i < F.length) (a : Fin (gadgets F[i].1).numAux) {index : ℕ}
    (hm : index ∈ shiftBlock (occurrencePrefix (fun r => (gadgets r).template) F i)
      ((auxiliaryBoundaryBlocks (gadgets F[i].1) (witnesses F[i].1)).getD a.val [])) :
    (replaceGadgets B (fun r => (gadgets r).template) F).vars.getD index 0 =
      2 * (B * i + a.val) + 1 := by
  simpa only [Sum.elim_inr] using
    (shifted_boundaryBlock_spec gadgets witnesses B F hi (Sum.inr a) hm).2

/-- The existing odd auxiliary encoding retains both copy and local index under the actual
fixed bound. Zero auxiliary bounds cause no exception, since they admit no local index. -/
theorem auxiliaryName_eq_iff {B i k j q : ℕ} (hj : j < B) (hq : q < B) :
    2 * (B * i + j) + 1 = 2 * (B * k + q) + 1 ↔ i = k ∧ j = q := by
  constructor
  · intro he
    have hbase : B * i + j = B * k + q := by omega
    have hpos : 0 < B := by omega
    have hdiv := congrArg (fun v => v / B) hbase
    simp only [Nat.mul_add_div hpos, Nat.div_eq_of_lt hj, Nat.div_eq_of_lt hq,
      Nat.add_zero] at hdiv
    exact ⟨hdiv, by subst k; omega⟩
  · rintro ⟨rfl, rfl⟩
    rfl

end Cslib.Complexity.CSP.GadgetRotation
