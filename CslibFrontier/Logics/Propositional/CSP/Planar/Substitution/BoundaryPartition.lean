/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.ProbeOccurrences
public import CslibFrontier.Logics.Propositional.CSP.Planar.Substitution.BoundaryBlocks
import Mathlib.Data.List.GetD
import CslibFrontier.Foundations.GroupTheory.Perm.Fin

/-!
# The positional contents of a free boundary block

At a distinct boundary marker, the tail of its rooted variable cycle contains exactly the
actual body occurrences at that variable. No other probe occurrence survives in this tail.
This statement uses indexed occurrences rather than a set of relation tuples or variable
names. Repeated body variables and duplicate constraints retain separate positions.
-/

public section

namespace Cslib.Complexity.CSP.GadgetRotation

open Cslib.Logic.PL Cslib.Logic.PL.CSP OrderedBoundary Graph

variable {Rel : Type} {arity : Rel → ℕ} {sem : Rel → List Bool → Bool}
  {n : ℕ} {R : Set (Fin n → Bool)}

/-- The actual unique probe occurrence for a canonical gadget free port. -/
@[expose] noncomputable def gadgetProbeOccurrence (g : PPGadget arity sem R) (i : Fin n) :
    (probeBody g.body (List.ofFn Sum.inl)).Occurrence :=
  probeOccurrence g.body (List.ofFn Sum.inl) ⟨i.val, by simp⟩

/-- Positive argument succession on the actual gadget probe reverses the original free-port
cycle, with the exact canonical marker coordinates retained. -/
theorem argumentSuccessor_gadgetProbeOccurrence_reverse
    (g : PPGadget arity sem R) (i : Fin n) :
    argumentSuccessor (gadgetProbeOccurrence g (finRotate n i)) = gadgetProbeOccurrence g i := by
  let ports := List.ofFn (Sum.inl : Fin n → Fin n ⊕ Fin g.numAux)
  let a : Fin ports.length := ⟨i.val, by simpa only [ports, List.length_ofFn] using i.isLt⟩
  have he : (⟨(finRotate n i).val, by
        simpa only [ports, List.length_ofFn] using (finRotate n i).isLt⟩ : Fin ports.length) =
      finRotate ports.length a := Fin.ext (by
    simp only [val_finRotate, a, ports, List.length_ofFn])
  unfold gadgetProbeOccurrence
  rw [he, argumentSuccessor_probeOccurrence_reverse]

/-- The canonical marker occupies exactly the numeric slot used by free-block preprocessing. -/
theorem incidenceEdgeIndex_gadgetProbeOccurrence (g : PPGadget arity sem R) (i : Fin n) :
    incidenceEdgeIndex (gadgetProbeOccurrence g i) = g.body.vars.length + (n - 1 - i.val) := by
  rw [gadgetProbeOccurrence, incidenceEdgeIndex_probeOccurrence]
  simp only [List.length_ofFn]
  congr 1
  simpa only [List.length_map] using congrArg List.length (CSP.map_occurrences g.body)

/-- Canonical marker coordinates retain the named free port, even if it never occurs in
the actual gadget body. -/
theorem var_gadgetProbeOccurrence (g : PPGadget arity sem R) (i : Fin n) :
    (gadgetProbeOccurrence g i).var = Sum.inl i := by
  rw [gadgetProbeOccurrence, var_probeOccurrence]
  simp only [List.getElem_ofFn, Fin.eta]

/-- The raw fixed free-block scan is rooted at the actual reversed-scope probe occurrence. -/
theorem getD_freeBoundaryBlocks (g : PPGadget arity sem R) (w : GadgetWitness g) (i : Fin n) :
    (freeBoundaryBlocks g w).getD i.val [] =
      ((RotationCertificate.cycleWord w.certificate
        (incidenceDart (gadgetProbeOccurrence g i) false).index).tail).map (· / 2) := by
  rw [List.getD_eq_getElem _ _ (by simpa only [length_freeBoundaryBlocks] using i.isLt)]
  simp only [freeBoundaryBlocks, List.getElem_map, List.getElem_finRange]
  congr 3
  change 2 * (g.body.vars.length + (n - 1 - i.val)) =
    2 * incidenceEdgeIndex (gadgetProbeOccurrence g i) + 0
  rw [incidenceEdgeIndex_gadgetProbeOccurrence, Nat.add_zero]

/-- Free blocks contain exactly the indexed body-prefix occurrences with the selected
free label. Distinctness of canonical ports is proved internally from their `Fin` indices. -/
theorem mem_freeBoundaryBlock_iff (g : PPGadget arity sem R) (w : GadgetWitness g)
    (i : Fin n) (index : ℕ) :
    index ∈ (freeBoundaryBlocks g w).getD i.val [] ↔
      ∃ o : g.body.Occurrence, incidenceEdgeIndex o = index ∧ o.var = Sum.inl i := by
  rw [← exists_probe_prefix_occurrence_iff g.body (List.ofFn Sum.inl) index (Sum.inl i)]
  rw [getD_freeBoundaryBlocks]
  obtain ⟨hc, _, _⟩ := (verifyRotationCertificate_eq_true_iff _ _).mp w.probe_accepted
  have hn : (List.ofFn (Sum.inl : Fin n → Fin n ⊕ Fin g.numAux)).Nodup :=
    List.nodup_ofFn.mpr Sum.inl_injective
  have hp : g.body.occurrences.length ≤ incidenceEdgeIndex (gadgetProbeOccurrence g i) := by
    rw [incidenceEdgeIndex_gadgetProbeOccurrence]
    have hl := congrArg List.length (CSP.map_occurrences g.body)
    simp only [List.length_map] at hl
    omega
  simpa only [var_gadgetProbeOccurrence] using
    mem_probe_cycleBlock_iff g.body _ hn w.certificate hc (gadgetProbeOccurrence g i) hp index

/-- Each free block is a duplicate-free occurrence word, even at unused free ports. -/
theorem nodup_freeBoundaryBlock (g : PPGadget arity sem R) (w : GadgetWitness g) (i : Fin n) :
    ((freeBoundaryBlocks g w).getD i.val []).Nodup := by
  rw [getD_freeBoundaryBlocks]
  obtain ⟨hc, _, _⟩ := (verifyRotationCertificate_eq_true_iff _ _).mp w.probe_accepted
  simpa only [List.map_tail] using
    (nodup_variable_cycleBlock hc (gadgetProbeOccurrence g i)).tail

/-- At an occurring auxiliary port, the executed block is the literal accepted body cycle
at its first occurrence. This identifies its cyclic anchoring as well as its members. -/
theorem auxiliaryBoundaryBlock_eq_cycleBlock (g : PPGadget arity sem R)
    (w : GadgetWitness g) (j : Fin g.numAux) (hv : Sum.inr j ∈ g.body.vars) :
    ∃ o : g.body.Occurrence, o.var = Sum.inr j ∧
      (auxiliaryBoundaryBlocks g w).getD j.val [] =
        (RotationCertificate.cycleWord (bodyCertificate g.body w.certificate)
          (incidenceDart o false).index).map (· / 2) := by
  obtain ⟨o, ho, hvar⟩ := exists_occurrence_at_first_index (F := g.body) (Sum.inr j) hv
  refine ⟨o, hvar, ?_⟩
  rw [List.getD_eq_getElem _ _
    (by simpa only [length_auxiliaryBoundaryBlocks] using j.isLt)]
  simp only [auxiliaryBoundaryBlocks, List.getElem_map, List.getElem_finRange, Fin.cast_mk,
    Fin.eta, ite_eq_left hv]
  have hstart : 2 * g.body.vars.idxOf (Sum.inr j) = (incidenceDart o false).index := by
    change _ = 2 * incidenceEdgeIndex o + 0
    rw [ho, Nat.add_zero]
    simp only [List.idxOf, Bool.beq_eq_decide_eq]
  rw [hstart]

/-- Auxiliary blocks contain exactly the indexed occurrences of their original existential
label. Unused auxiliary ports have empty blocks rather than invented darts. -/
theorem mem_auxiliaryBoundaryBlock_iff (g : PPGadget arity sem R) (w : GadgetWitness g)
    (j : Fin g.numAux) (index : ℕ) :
    index ∈ (auxiliaryBoundaryBlocks g w).getD j.val [] ↔
      ∃ o : g.body.Occurrence, incidenceEdgeIndex o = index ∧ o.var = Sum.inr j := by
  by_cases hv : Sum.inr j ∈ g.body.vars
  · obtain ⟨o, hvar, he⟩ := auxiliaryBoundaryBlock_eq_cycleBlock g w j hv
    obtain ⟨hc, _, _⟩ := (verifyRotationCertificate_eq_true_iff _ _).mp w.body_accepted
    rw [he, mem_variable_cycleBlock_iff hc, hvar]
  · rw [List.getD_eq_getElem _ _
      (by simpa only [length_auxiliaryBoundaryBlocks] using j.isLt)]
    simp only [auxiliaryBoundaryBlocks, List.getElem_map, List.getElem_finRange, Fin.cast_mk,
      Fin.eta, ite_eq_right hv, List.not_mem_nil, false_iff]
    rintro ⟨o, _, ho⟩
    exact hv (ho ▸ o.var_mem)

/-- Every auxiliary cycle is a duplicate-free occurrence word. -/
theorem nodup_auxiliaryBoundaryBlock (g : PPGadget arity sem R) (w : GadgetWitness g)
    (j : Fin g.numAux) : ((auxiliaryBoundaryBlocks g w).getD j.val []).Nodup := by
  by_cases hv : Sum.inr j ∈ g.body.vars
  · obtain ⟨o, _, he⟩ := auxiliaryBoundaryBlock_eq_cycleBlock g w j hv
    obtain ⟨hc, _, _⟩ := (verifyRotationCertificate_eq_true_iff _ _).mp w.body_accepted
    rw [he]
    exact nodup_variable_cycleBlock hc o
  · rw [List.getD_eq_getElem _ _
      (by simpa only [length_auxiliaryBoundaryBlocks] using j.isLt)]
    simp only [auxiliaryBoundaryBlocks, List.getElem_map, List.getElem_finRange, Fin.cast_mk,
      Fin.eta, ite_eq_right hv, List.nodup_nil]

/-- Select the actual occurrence word for any declared canonical gadget variable.
Both free and existential ports retain their empty words when unused. -/
@[expose] def boundaryBlock (g : PPGadget arity sem R) (w : GadgetWitness g) :
    Fin n ⊕ Fin g.numAux → List ℕ :=
  Sum.elim (fun i => (freeBoundaryBlocks g w).getD i.val [])
    (fun j => (auxiliaryBoundaryBlocks g w).getD j.val [])

/-- Every local block is exactly the fiber of its named canonical variable. -/
theorem mem_boundaryBlock_iff (g : PPGadget arity sem R) (w : GadgetWitness g)
    (v : Fin n ⊕ Fin g.numAux) (index : ℕ) :
    index ∈ boundaryBlock g w v ↔
      ∃ o : g.body.Occurrence, incidenceEdgeIndex o = index ∧ o.var = v := by
  cases v with
  | inl i => exact mem_freeBoundaryBlock_iff g w i index
  | inr j => exact mem_auxiliaryBoundaryBlock_iff g w j index

/-- Shifting a local variable word retains the exact copy offset and original occurrence. -/
theorem mem_shiftBlock_boundaryBlock_iff (g : PPGadget arity sem R) (w : GadgetWitness g)
    (offset : ℕ) (v : Fin n ⊕ Fin g.numAux) (index : ℕ) :
    index ∈ shiftBlock offset (boundaryBlock g w v) ↔
      ∃ o : g.body.Occurrence, offset + incidenceEdgeIndex o = index ∧ o.var = v := by
  simp only [shiftBlock, List.mem_map, mem_boundaryBlock_iff]
  constructor
  · rintro ⟨j, ⟨o, ho, hv⟩, he⟩
    exact ⟨o, by rw [ho]; exact he, hv⟩
  · rintro ⟨o, he, hv⟩
    exact ⟨incidenceEdgeIndex o, ⟨o, rfl, hv⟩, he⟩

/-- Every selected word has no repeated occurrence positions. -/
theorem nodup_boundaryBlock (g : PPGadget arity sem R) (w : GadgetWitness g)
    (v : Fin n ⊕ Fin g.numAux) : (boundaryBlock g w v).Nodup := by
  cases v with
  | inl i => exact nodup_freeBoundaryBlock g w i
  | inr j => exact nodup_auxiliaryBoundaryBlock g w j

/-- Different canonical variables own disjoint occurrence words. Repeated source names
have no role here: canonical free ports remain distinct local variables. -/
theorem disjoint_boundaryBlock (g : PPGadget arity sem R) (w : GadgetWitness g)
    {v u : Fin n ⊕ Fin g.numAux} (hvu : v ≠ u) :
    (boundaryBlock g w v).Disjoint (boundaryBlock g w u) := by
  apply List.disjoint_left.mpr
  intro index hv hu
  obtain ⟨o, ho, hov⟩ := (mem_boundaryBlock_iff g w v index).mp hv
  obtain ⟨p, hp, hpu⟩ := (mem_boundaryBlock_iff g w u index).mp hu
  have he : o = p := incidenceEdgeIndex_injective (ho.trans hp.symm)
  exact hvu (hov.symm.trans (he ▸ hpu))

private theorem boundaryBlocks_eq_map (g : PPGadget arity sem R) (w : GadgetWitness g) :
    freeBoundaryBlocks g w ++ auxiliaryBoundaryBlocks g w =
      ((List.finRange n).map Sum.inl ++ (List.finRange g.numAux).map Sum.inr).map
        (boundaryBlock g w) := by
  rw [List.map_append, List.map_map, List.map_map]
  congr 1
  · apply List.ext_getElem
    · simp only [length_freeBoundaryBlocks, List.length_map, List.length_finRange]
    · intro i hi hj
      simp only [List.getElem_map, List.getElem_finRange, Function.comp_apply, boundaryBlock,
        Sum.elim_inl]
      exact (List.getD_eq_getElem _ [] hi).symm
  · apply List.ext_getElem
    · simp only [length_auxiliaryBoundaryBlocks, List.length_map, List.length_finRange]
    · intro i hi hj
      simp only [List.getElem_map, List.getElem_finRange, Function.comp_apply, boundaryBlock,
        Sum.elim_inr]
      exact (List.getD_eq_getElem _ [] hi).symm

/-- The complete free-plus-auxiliary table partitions local occurrence positions without
any duplication, including zero arities and unused ports. -/
theorem nodup_flatten_boundaryBlocks (g : PPGadget arity sem R) (w : GadgetWitness g) :
    (freeBoundaryBlocks g w ++ auxiliaryBoundaryBlocks g w).flatten.Nodup := by
  rw [boundaryBlocks_eq_map, ← List.flatMap]
  apply List.nodup_flatMap.mpr
  refine ⟨fun v _ => nodup_boundaryBlock g w v, ?_⟩
  have hn : ((List.finRange n).map (Sum.inl : Fin n → Fin n ⊕ Fin g.numAux) ++
      (List.finRange g.numAux).map Sum.inr).Nodup := by
    simp [List.nodup_append, List.nodup_map_iff, Sum.inl_injective, Sum.inr_injective,
      List.nodup_finRange]
  exact hn.imp fun h => disjoint_boundaryBlock g w h

/-- The local partition covers exactly the actual body's bounded occurrence indices.
No interval of variable names, unused port labels, or binary magnitudes is enumerated. -/
theorem mem_flatten_boundaryBlocks_iff (g : PPGadget arity sem R) (w : GadgetWitness g)
    (index : ℕ) :
    index ∈ (freeBoundaryBlocks g w ++ auxiliaryBoundaryBlocks g w).flatten ↔
      index < g.body.occurrences.length := by
  rw [boundaryBlocks_eq_map, ← List.flatMap]
  simp only [List.mem_flatMap, mem_boundaryBlock_iff]
  constructor
  · rintro ⟨v, _, o, ho, _⟩
    rw [← ho]
    simpa only [incidenceGraph_edges, List.length_map] using incidenceEdgeIndex_lt o
  · intro hi
    obtain ⟨o, ho⟩ := exists_incidenceEdgeIndex (F := g.body) index
      (by simpa only [incidenceGraph_edges, List.length_map] using hi)
    refine ⟨o.var, ?_, o, ho, rfl⟩
    cases o.var with
    | inl i => simp
    | inr j => simp

/-- The local words enumerate each actual body occurrence exactly once, in their stored
cyclic orders. Only the order between fibers differs from the flat occurrence enumeration. -/
theorem flatten_boundaryBlocks_perm_range (g : PPGadget arity sem R) (w : GadgetWitness g) :
    (freeBoundaryBlocks g w ++ auxiliaryBoundaryBlocks g w).flatten.Perm
      (List.range g.body.occurrences.length) := by
  apply (List.perm_ext_iff_of_nodup (nodup_flatten_boundaryBlocks g w)
    (List.nodup_range)).mpr
  intro index
  rw [mem_flatten_boundaryBlocks_iff, List.mem_range]

end Cslib.Complexity.CSP.GadgetRotation
