/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Probe
public import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.AppendScopeIndex
public import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.VariableCycleWords
import CslibFrontier.Logics.Propositional.CSP.Occurrence.Symbols
import CslibFrontier.Logics.Propositional.CSP.Occurrence.Positions
import CslibFrontier.Foundations.GroupTheory.Perm.Fin
import Mathlib.Data.List.GetD

/-!
# Actual body and marker coordinates in the structural boundary probe

Original body occurrences retain their literal indexed prefix positions. Canonical reversed
probe positions retain their original port labels. Every augmented occurrence is one of these
two kinds, without distinctness, nonempty-boundary or degree assumptions. At distinct ports,
the actual variable-cycle tail is exactly the original body prefix at the selected free label.
-/

public section

namespace Cslib.Complexity.CSP.OrderedBoundary

open Cslib.Logic.PL Graph

variable {Rel V : Type} [DecidableEq V]

/-- The actual reversed-scope probe occurrence belonging to an original boundary position.
This proof-only coordinate map does not supply or search for a rotation. -/
noncomputable def probeOccurrence (F : CSP Rel V) (ports : List V) (i : Fin ports.length) :
    (probeBody F ports).Occurrence :=
  CSP.appendScopeOccurrenceEquiv (F.map fun ⟨r, scope⟩ => ⟨some r, scope⟩) none ports.reverse
    (Sum.inr ⟨ports.length - 1 - i.val, by simp only [List.length_reverse]; omega⟩)

omit [DecidableEq V] in
/-- Every structural marker belongs to the one appended constraint position. -/
theorem probeOccurrence_constraint (F : CSP Rel V) (ports : List V) (i : Fin ports.length) :
    (probeOccurrence F ports i).1.val = F.length := by
  have hr := CSP.record_appendScopeOccurrenceEquiv_inr
    (F.map fun ⟨r, scope⟩ => ⟨some r, scope⟩) none ports.reverse
    (⟨ports.length - 1 - i.val, by simp only [List.length_reverse]; omega⟩ : Fin _)
  simpa only [probeOccurrence, CSP.Occurrence.record, List.length_map] using congrArg Prod.fst hr

omit [DecidableEq V] in
/-- The actual probe scope position is exactly the reverse of the original port position. -/
theorem probeOccurrence_argument (F : CSP Rel V) (ports : List V) (i : Fin ports.length) :
    (probeOccurrence F ports i).2.val = ports.length - 1 - i.val :=
  congrArg (fun record : ℕ × ℕ × V => record.2.1)
    (CSP.record_appendScopeOccurrenceEquiv_inr
      (F.map fun ⟨r, scope⟩ => ⟨some r, scope⟩) none ports.reverse
      (⟨ports.length - 1 - i.val, by simp only [List.length_reverse]; omega⟩ : Fin _))

omit [DecidableEq V] in
/-- The structural probe scope has exactly the number of original boundary positions. -/
theorem length_scope_probeOccurrence (F : CSP Rel V) (ports : List V) (i : Fin ports.length) :
    (probeOccurrence F ports i).scope.length = ports.length := by
  simp [CSP.Occurrence.scope, probeOccurrence_constraint, probeBody]

omit [DecidableEq V] in
/-- Positive argument succession on the literal reversed probe scope follows the reverse
of the original port cycle. This is a directed equality, with no reflection convention. -/
theorem argumentSuccessor_probeOccurrence_reverse (F : CSP Rel V) (ports : List V)
    (i : Fin ports.length) :
    argumentSuccessor (probeOccurrence F ports (finRotate ports.length i)) =
      probeOccurrence F ports i := by
  apply CSP.Occurrence.eq_of_positions
  · exact (probeOccurrence_constraint F ports _).trans
      (probeOccurrence_constraint F ports i).symm
  · change (finRotate _ (probeOccurrence F ports (finRotate ports.length i)).2).val = _
    rw [val_finRotate, probeOccurrence_argument]
    have hlen := length_scope_probeOccurrence F ports (finRotate ports.length i)
    change (probeBody F ports)[(probeOccurrence F ports (finRotate ports.length i)).1.val].2.length
      = ports.length at hlen
    rw [hlen, probeOccurrence_argument, val_finRotate]
    split_ifs <;> omega

/-- Probe positions follow the actual body prefix and the literal reversed port word. -/
theorem incidenceEdgeIndex_probeOccurrence (F : CSP Rel V) (ports : List V)
    (i : Fin ports.length) :
    incidenceEdgeIndex (probeOccurrence F ports i) =
      F.occurrences.length + (ports.length - 1 - i.val) := by
  erw [probeOccurrence, incidenceEdgeIndex_appendScopeOccurrenceEquiv_inr,
    CSP.occurrences_mapRelation]

omit [DecidableEq V] in
/-- Probe markers retain distinct indexed positions, even when their port names repeat. -/
theorem probeOccurrence_injective (F : CSP Rel V) (ports : List V) :
    Function.Injective (probeOccurrence F ports) := by
  intro i j he
  have hj := congrArg (fun p => p.2.val) he
  rw [probeOccurrence_argument, probeOccurrence_argument] at hj
  exact Fin.ext (by omega)

omit [DecidableEq V] in
/-- The reversed probe position still carries the original boundary label. -/
theorem var_probeOccurrence (F : CSP Rel V) (ports : List V) (i : Fin ports.length) :
    (probeOccurrence F ports i).var = ports[i.val] := by
  have hbound : ports.length - 1 - i.val < ports.reverse.length := by
    simp only [List.length_reverse]
    omega
  have h := CSP.record_appendScopeOccurrenceEquiv_inr
    (F.map fun ⟨r, scope⟩ => ⟨some r, scope⟩) none ports.reverse
    (⟨ports.length - 1 - i.val, hbound⟩ : Fin _)
  have hv := congrArg (fun record : ℕ × ℕ × V => record.2.2) h
  change (probeOccurrence F ports i).var = ports.reverse[ports.length - 1 - i.val]'hbound at hv
  rw [hv, List.getElem_reverse]
  congr 1
  omega

omit [DecidableEq V] in
/-- Retain an actual body occurrence in the probe-augmented body's positional prefix. -/
noncomputable def bodyOccurrence (F : CSP Rel V) (ports : List V) (o : F.Occurrence) :
    (probeBody F ports).Occurrence :=
  (CSP.occurrenceRecordEquiv _).symm ⟨o.record, by
    rw [occurrences_probeBody]
    exact List.mem_append_left _ (CSP.mem_occurrences.mpr ⟨o, rfl⟩)⟩

omit [DecidableEq V] in
/-- Appending the structural probe retains each original record literally. -/
theorem record_bodyOccurrence (F : CSP Rel V) (ports : List V) (o : F.Occurrence) :
    (bodyOccurrence F ports o).record = o.record :=
  CSP.record_occurrenceRecordEquiv_symm _ _

omit [DecidableEq V] in
/-- Appending the probe retains the complete original scope at each indexed body row. -/
theorem scope_bodyOccurrence (F : CSP Rel V) (ports : List V) (o : F.Occurrence) :
    (probeBody F ports)[(bodyOccurrence F ports o).1.val].2 = F[o.1.val].2 := by
  have hrow : (bodyOccurrence F ports o).1.val = o.1.val :=
    congrArg Prod.fst (record_bodyOccurrence F ports o)
  simp [hrow, probeBody, o.1.isLt]

omit [DecidableEq V] in
/-- Appending the structural probe retains every original positional occurrence identity. -/
theorem bodyOccurrence_injective (F : CSP Rel V) (ports : List V) :
    Function.Injective (bodyOccurrence F ports) := by
  intro o p he
  apply CSP.Occurrence.record_injective
  rw [← record_bodyOccurrence F ports o, ← record_bodyOccurrence F ports p, he]

/-- Probe augmentation leaves every original incidence edge index unchanged. -/
theorem incidenceEdgeIndex_bodyOccurrence (F : CSP Rel V) (ports : List V)
    (o : F.Occurrence) : incidenceEdgeIndex (bodyOccurrence F ports o) = incidenceEdgeIndex o := by
  unfold incidenceEdgeIndex
  rw [record_bodyOccurrence, occurrences_probeBody,
    List.idxOf_append_of_mem (CSP.mem_occurrences.mpr ⟨o, rfl⟩)]

omit [DecidableEq V] in
/-- Probe augmentation retains the named variable at every original body occurrence. -/
theorem var_bodyOccurrence (F : CSP Rel V) (ports : List V) (o : F.Occurrence) :
    (bodyOccurrence F ports o).var = o.var :=
  congrArg (fun record : ℕ × ℕ × V => record.2.2) (record_bodyOccurrence F ports o)

omit [DecidableEq V] in
/-- The retained body prefix follows its original positive cyclic argument order after the
probe is appended. The relation-symbol injection and appended marker row preserve all scopes. -/
theorem argumentSuccessor_bodyOccurrence (F : CSP Rel V) (ports : List V) (o : F.Occurrence) :
    argumentSuccessor (bodyOccurrence F ports o) =
      bodyOccurrence F ports (argumentSuccessor o) := by
  have hrow (p : F.Occurrence) : (bodyOccurrence F ports p).1.val = p.1.val :=
    congrArg Prod.fst (record_bodyOccurrence F ports p)
  have harg (p : F.Occurrence) : (bodyOccurrence F ports p).2.val = p.2.val :=
    congrArg (fun record : ℕ × ℕ × V => record.2.1) (record_bodyOccurrence F ports p)
  apply CSP.Occurrence.eq_of_positions
  · exact (hrow o).trans (hrow (argumentSuccessor o)).symm
  · change (finRotate _ (bodyOccurrence F ports o).2).val = _
    rw [harg, val_finRotate, harg]
    have hlen := congrArg List.length (scope_bodyOccurrence F ports o)
    change (if o.2.val + 1 = _ then 0 else o.2.val + 1) = (finRotate _ o.2).val
    rw [hlen, val_finRotate]

/-- Every indexed occurrence in the probe's body prefix is exactly an original occurrence. -/
theorem exists_bodyOccurrence_of_prefix (F : CSP Rel V) (ports : List V)
    (p : (probeBody F ports).Occurrence) (hp : incidenceEdgeIndex p < F.occurrences.length) :
    ∃ o : F.Occurrence, bodyOccurrence F ports o = p := by
  have hprefix : F.occurrences <+: (probeBody F ports).occurrences := by
    rw [occurrences_probeBody]
    exact List.prefix_append _ _
  have hm := (hprefix.mem_iff_idxOf_lt_length p.record).mpr hp
  obtain ⟨o, ho⟩ := CSP.mem_occurrences.mp hm
  exact ⟨o, CSP.Occurrence.record_injective ((record_bodyOccurrence F ports o).trans ho)⟩

/-- A body-prefix occurrence with a given variable and edge index is an original-body
occurrence with those same coordinates, in both directions. -/
theorem exists_probe_prefix_occurrence_iff (F : CSP Rel V) (ports : List V)
    (index : ℕ) (v : V) :
    (∃ p : (probeBody F ports).Occurrence, incidenceEdgeIndex p = index ∧
      p.var = v ∧ incidenceEdgeIndex p < F.occurrences.length) ↔
      ∃ o : F.Occurrence, incidenceEdgeIndex o = index ∧ o.var = v := by
  constructor
  · rintro ⟨p, hi, hv, hp⟩
    obtain ⟨o, rfl⟩ := exists_bodyOccurrence_of_prefix F ports p hp
    exact ⟨o, by simpa only [incidenceEdgeIndex_bodyOccurrence] using hi,
      by simpa only [var_bodyOccurrence] using hv⟩
  · rintro ⟨o, hi, hv⟩
    refine ⟨bodyOccurrence F ports o, ?_, ?_, ?_⟩
    · simpa only [incidenceEdgeIndex_bodyOccurrence] using hi
    · simpa only [var_bodyOccurrence] using hv
    · rw [incidenceEdgeIndex_bodyOccurrence]
      simpa only [incidenceGraph_edges, List.length_map] using incidenceEdgeIndex_lt o

omit [DecidableEq V] in
/-- Every actual probe-augmented occurrence is an original body occurrence or one literal
reversed-scope marker. This coordinate decomposition requires no distinctness of ports. -/
theorem exists_bodyOccurrence_or_probeOccurrence (F : CSP Rel V) (ports : List V)
    (p : (probeBody F ports).Occurrence) :
    (∃ o : F.Occurrence, bodyOccurrence F ports o = p) ∨
      ∃ i : Fin ports.length, probeOccurrence F ports i = p := by
  classical
  by_cases hi : incidenceEdgeIndex p < F.occurrences.length
  · exact Or.inl (exists_bodyOccurrence_of_prefix F ports p hi)
  have hc := constraint_of_probe_occurrence F ports p (Nat.le_of_not_gt hi)
  have harg : p.2.val < ports.length := by
    simpa [hc, probeBody] using p.2.isLt
  let i : Fin ports.length := ⟨ports.length - 1 - p.2.val, by omega⟩
  refine Or.inr ⟨i, CSP.Occurrence.eq_of_positions
    ((probeOccurrence_constraint F ports i).trans hc.symm) ?_⟩
  rw [probeOccurrence_argument]
  dsimp only [i]
  omega

/-- The local occurrence block read after a probe corner is exactly the actual body prefix
at that free variable. Canonical gadget ports discharge the boundary Nodup premise internally. -/
theorem mem_probe_cycleBlock_iff (F : CSP Rel V) (ports : List V) (hn : ports.Nodup)
    (c : RotationCertificate)
    (hc : RotationCertificate.verifyRotation (incidenceGraph (probeBody F ports)) c = true)
    (p : (probeBody F ports).Occurrence)
    (hp : F.occurrences.length ≤ incidenceEdgeIndex p) (index : ℕ) :
    index ∈ ((RotationCertificate.cycleWord c (incidenceDart p false).index).tail.map
      (fun j => j / 2)) ↔
      ∃ o : (probeBody F ports).Occurrence, incidenceEdgeIndex o = index ∧
        o.var = p.var ∧ incidenceEdgeIndex o < F.occurrences.length := by
  constructor
  · intro hm
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hm
    have hwhole := List.mem_of_mem_tail hj
    obtain ⟨e, he, hv⟩ :=
      (RotationCertificate.mem_cycleWord_iff_exists_dart hc (incidenceDart p false) j).mp hwhole
    obtain ⟨o, ho⟩ := exists_incidenceDart e
    have hf := (vertex_incidenceDart_eq_iff o p e.2 false).mp (by rw [ho]; exact hv)
    have hside : e.2 = false := hf.1
    have hvar : o.var = p.var := by simpa only [hside, Bool.false_eq_true, ite_false] using hf.2
    have heq : incidenceDart o false = e := by simpa only [hside] using ho
    have hindex : j / 2 = incidenceEdgeIndex o := by
      rw [← he, ← heq]
      simp [Graph.Dart.index, incidenceDart]
    refine ⟨o, hindex.symm, hvar, ?_⟩
    by_contra hout
    have hop := probe_occurrence_eq_of_var_eq F ports hn o p (Nat.le_of_not_gt hout) hp hvar
    have hepd : e = incidenceDart p false := by rw [← heq, hop]
    have htail := (RotationCertificate.mem_tail_cycleWord_iff hc (incidenceDart p false) e).mp
      (by simpa only [he] using hj)
    exact htail.2 hepd
  · rintro ⟨o, rfl, hv, ho⟩
    have hvertex : (incidenceDart o false).vertex = (incidenceDart p false).vertex :=
      (vertex_incidenceDart_eq_iff o p false false).mpr ⟨rfl, hv⟩
    have hne : incidenceDart o false ≠ incidenceDart p false := by
      intro he
      have hi := congrArg (fun d : Dart (incidenceGraph (probeBody F ports)) => d.1.val) he
      change incidenceEdgeIndex o = incidenceEdgeIndex p at hi
      omega
    apply List.mem_map.mpr
    refine ⟨(incidenceDart o false).index,
      (RotationCertificate.mem_tail_cycleWord_iff hc _ _).mpr ⟨hvertex, hne⟩, ?_⟩
    simp [Graph.Dart.index, incidenceDart]

end Cslib.Complexity.CSP.OrderedBoundary
