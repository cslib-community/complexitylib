/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Planar.Substitution.CopyLabels
public import CslibFrontier.Logics.Propositional.CSP.Planar.Substitution.VariableBlocks
import Mathlib.Data.List.GetD

/-!
# Exact target-name fibers of the executed substitution words

Each source-variable word contains precisely the actual target occurrences at its even name.
Each auxiliary word contains precisely the actual occurrences at that copy's private odd name.
The proofs recover typed local occurrences using the public positional inverse lookup and
retain repeated source names. No target permutation, fiber or genus provider is an input.
-/

public section

namespace Cslib.Complexity.CSP.GadgetRotation

open Cslib.Logic.PL Cslib.Logic.PL.CSP OrderedBoundary Graph

variable {Src Rel : Type} {arity : Rel → ℕ} {sem : Rel → List Bool → Bool}
  {srcArity : Src → ℕ} {srcSem : Src → List Bool → Bool}

/-- The source's supplied white cycle splices exactly all target occurrences with that
original even name. Local free ports are distinct; source scope names need not be. -/
theorem mem_variableBlock_iff_targetName
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (witnesses : ∀ r, GadgetWitness (gadgets r)) (B : ℕ) (F : CSP Src ℕ)
    (hF : WellFormed srcArity F) (c : RotationCertificate)
    (hc : RotationCertificate.verifyRotation (incidenceGraph F) c = true)
    (v : ℕ) (hv : v ∈ F.vars) (index : ℕ) :
    index ∈ variableBlock (fun r => (gadgets r).template)
      (fun r => freeBoundaryBlocks (gadgets r) (witnesses r)) F c v ↔
      index < (replaceGadgets B (fun r => (gadgets r).template) F).vars.length ∧
        (replaceGadgets B (fun r => (gadgets r).template) F).vars.getD index 0 = 2 * v := by
  rw [mem_variableBlock_iff_occurrence _ _ F c hc v hv]
  constructor
  · rintro ⟨s, hvar, hm⟩
    let a : Fin (srcArity s.relation) := ⟨s.2.val, by
      change s.2.val < srcArity F[s.1.val].1
      rw [← hF F[s.1.val] (List.getElem_mem s.1.isLt)]
      exact s.2.isLt⟩
    obtain ⟨hb, hname⟩ := shifted_boundaryBlock_spec gadgets witnesses B F s.1.isLt
      (Sum.inl a) hm
    refine ⟨hb, ?_⟩
    rw [hname]
    change 2 * F[s.1.val].2.getD s.2.val 0 = 2 * v
    rw [List.getD_eq_getElem _ _ s.2.isLt]
    change 2 * s.var = 2 * v
    rw [hvar]
  · rintro ⟨hb, hname⟩
    obtain ⟨i, hi, o, ho⟩ := exists_gadgetCopy gadgets B F hb
    rw [← ho, List.getD_eq_getElem _ _ (copyIndex_lt_gadgetOccurrence gadgets B F hi o),
      getElem_vars_gadgetCopy] at hname
    cases hlocal : o.var with
    | inl a =>
      simp only [hlocal, Sum.elim_inl] at hname
      have hscope : F[i].2.getD a.val 0 = v := by omega
      have harg : a.val < F[i].2.length := by
        rw [hF F[i] (List.getElem_mem hi)]
        exact a.isLt
      let s : F.Occurrence := ⟨⟨i, hi⟩, ⟨a.val, harg⟩⟩
      have hsvar : s.var = v := by
        change F[i].2[a.val] = v
        rw [← List.getD_eq_getElem _ 0 harg]
        exact hscope
      refine ⟨s, hsvar, ?_⟩
      change index ∈ shiftBlock (occurrencePrefix (fun r => (gadgets r).template) F i)
        ((freeBoundaryBlocks (gadgets F[i].1) (witnesses F[i].1)).getD a.val [])
      exact (mem_shiftBlock_boundaryBlock_iff _ _ _ (Sum.inl a) index).mpr ⟨o, ho, hlocal⟩
    | inr j =>
      simp only [hlocal, Sum.elim_inr] at hname
      omega

/-- A copy's auxiliary word is exactly one private odd-name fiber of the actual target.
The uniform auxiliary bound separates copies even when source rows and names repeat. -/
theorem mem_shifted_auxiliaryBlock_iff_targetName
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (witnesses : ∀ r, GadgetWitness (gadgets r)) (B : ℕ)
    (hB : ∀ r, (gadgets r).numAux ≤ B) (F : CSP Src ℕ)
    {i : ℕ} (hi : i < F.length) (a : Fin (gadgets F[i].1).numAux) (index : ℕ) :
    index ∈ shiftBlock (occurrencePrefix (fun r => (gadgets r).template) F i)
      ((auxiliaryBoundaryBlocks (gadgets F[i].1) (witnesses F[i].1)).getD a.val []) ↔
      index < (replaceGadgets B (fun r => (gadgets r).template) F).vars.length ∧
        (replaceGadgets B (fun r => (gadgets r).template) F).vars.getD index 0 =
          2 * (B * i + a.val) + 1 := by
  constructor
  · intro hm
    simpa only [Sum.elim_inr] using
      shifted_boundaryBlock_spec gadgets witnesses B F hi (Sum.inr a) hm
  · rintro ⟨hb, hname⟩
    obtain ⟨k, hk, o, ho⟩ := exists_gadgetCopy gadgets B F hb
    rw [← ho, List.getD_eq_getElem _ _ (copyIndex_lt_gadgetOccurrence gadgets B F hk o),
      getElem_vars_gadgetCopy] at hname
    cases hlocal : o.var with
    | inl b =>
      simp only [hlocal, Sum.elim_inl] at hname
      omega
    | inr b =>
      simp only [hlocal, Sum.elim_inr] at hname
      have hcodes := (auxiliaryName_eq_iff (b.isLt.trans_le (hB _))
        (a.isLt.trans_le (hB _))).mp hname
      obtain ⟨rfl, he⟩ := hcodes
      have hba : b = a := Fin.ext he
      subst b
      exact (mem_shiftBlock_boundaryBlock_iff _ _ _ (Sum.inr a) index).mpr ⟨o, ho, hlocal⟩

end Cslib.Complexity.CSP.GadgetRotation
