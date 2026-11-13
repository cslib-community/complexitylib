/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.EdgeCSP.Blossom.Ports
import CslibFrontier.Foundations.Data.List.Blocks
import Mathlib.Data.List.GetD

/-!
# Positional transport of the contracted reference labeling

Surviving old ports retain their labels. The old-constraint end of every fresh connector is
zero, and the new central end is the actual one-hot reference from Section 5.3 of
[KazdaKolmogorovRolinek2018], arXiv:1602.03124v6, printed p. 12.
All port constructors search finite actual position lists and use binary names only as data.
-/

public section

namespace Cslib.Logic.PL.CSP.Blossom

open Table Finset
open Cslib.BitString

variable {F : CSP Table ℕ}

/-- An original argument position survives exactly when its variable is outside the blossom. -/
theorem mem_outsidePositions (vs scope : List ℕ) (j : ℕ) :
    j ∈ outsidePositions scope.length (positions vs scope) ↔
      j < scope.length ∧ scope.getD j 0 ∉ vs := by
  simp [outsidePositions, positions]
  omega

/-- Every surviving port has a valid index in the actual old-constraint output scope. -/
theorem outside_length_le_scope (f : OccurrenceLabeling F Bool) (vs : List ℕ)
    (i : Fin F.length) :
    (outsidePositions F[i.val].scope.length (positions vs F[i.val].scope)).length ≤
      (constraint f vs i).scope.length := by
  rw [scope_constraint, ← outsideScope_eq_filter]
  simp

/-- Map a surviving original occurrence to its new scope position. Its original constraint
index is preserved, and its new argument index is found in the actual finite outside list. -/
@[expose] def oldPort (f : OccurrenceLabeling F Bool) (vs : List ℕ)
    (o : Occurrence F) (ho : o.var ∉ vs) : Occurrence (contract f vs) :=
  ⟨⟨o.1.val, by simpa only [length_contract] using Nat.lt_succ_of_lt o.1.isLt⟩,
    ⟨(outsidePositions F[o.1.val].scope.length (positions vs F[o.1.val].scope)).idxOf o.2.val, by
      have hm : o.2.val ∈ outsidePositions F[o.1.val].scope.length
          (positions vs F[o.1.val].scope) := by
        apply (mem_outsidePositions _ _ _).mpr
        exact ⟨o.2.isLt, by simpa only [List.getD_eq_getElem _ _ o.2.isLt, Occurrence.var] using ho⟩
      have hl := (List.idxOf_lt_length_iff.mpr hm).trans_le (outside_length_le_scope f vs o.1)
      simpa only [get_contract_old] using hl⟩⟩

/-- Surviving occurrence transport preserves the original binary variable name. -/
theorem oldPort_var (f : OccurrenceLabeling F Bool) (vs : List ℕ)
    (o : Occurrence F) (ho : o.var ∉ vs) : (oldPort f vs o ho).var = o.var := by
  let os := outsidePositions F[o.1.val].scope.length (positions vs F[o.1.val].scope)
  have hm : o.2.val ∈ os := (mem_outsidePositions _ _ _).mpr
    ⟨o.2.isLt, by simpa only [List.getD_eq_getElem _ _ o.2.isLt, Occurrence.var] using ho⟩
  have hl := List.idxOf_lt_length_iff.mpr hm
  have he := List.getElem_idxOf hl
  have hn : os.idxOf o.2.val < (contract f vs)[o.1.val].scope.length := by
    simpa only [get_contract_old] using hl.trans_le (outside_length_le_scope f vs o.1)
  change (contract f vs)[o.1.val].scope[os.idxOf o.2.val] = o.var
  simp only [get_contract_old, scope_constraint, ← outsideScope_eq_filter]
  change (os.map (fun j => F[o.1.val].scope.getD j 0) ++
    if (positions vs F[o.1.val].scope).isEmpty then [] else [connector F o.1])[os.idxOf o.2.val]'
      (by simp only [List.length_append, List.length_map]; omega) = _
  rw [List.getElem_append_left (by simpa only [List.length_map] using hl), List.getElem_map]
  change F[o.1.val].scope.getD (os[os.idxOf o.2.val]) 0 = o.var
  rw [he, List.getD_eq_getElem _ _ o.2.isLt]
  rfl

/-- The old reference buffer is the ordered outside projection, followed by a zero precisely
at touched constraints. Untouched constraints need no extra connector bit. -/
theorem referenceRows_project (f : OccurrenceLabeling F Bool) (vs : List ℕ)
    (i : Fin F.length) :
    (referenceRows f vs).getD i.val [] =
      project (localTuple f i)
          (outsidePositions F[i.val].scope.length (positions vs F[i.val].scope)) ++
        if (positions vs F[i.val].scope).isEmpty then [] else [false] := by
  rw [get_referenceRows_old]
  split
  next hp =>
    have he := List.isEmpty_iff.mp hp
    have hl : (localTuple f i).length = F[i.val].scope.length := by simp [localTuple]
    simp only [he, outsidePositions, List.contains_nil, Bool.not_false, List.filter_true,
      project, List.append_nil]
    rw [← hl, List.map_getD_range]
  · rfl

/-- The explicit finite contracted reference retains every old outside occurrence value. -/
theorem reference_oldPort (f : OccurrenceLabeling F Bool) (vs : List ℕ)
    (o : Occurrence F) (ho : o.var ∉ vs) : reference f vs (oldPort f vs o ho) = f o := by
  let os := outsidePositions F[o.1.val].scope.length (positions vs F[o.1.val].scope)
  have hm : o.2.val ∈ os := (mem_outsidePositions _ _ _).mpr
    ⟨o.2.isLt, by simpa only [List.getD_eq_getElem _ _ o.2.isLt, Occurrence.var] using ho⟩
  have hl := List.idxOf_lt_length_iff.mpr hm
  have he := List.getElem_idxOf hl
  change ((referenceRows f vs).getD o.1.val []).getD (os.idxOf o.2.val) false = f o
  rw [referenceRows_project]
  rw [List.getD_append _ _ _ _ (by simpa only [project, List.length_map] using hl)]
  rw [List.getD_eq_getElem _ _ (by simpa only [project, List.length_map] using hl)]
  simp only [project, List.getElem_map]
  change (localTuple f o.1).getD (os[os.idxOf o.2.val]) false = f o
  rw [he]
  simp [localTuple, o.2.isLt]

/-- The gathered outside list followed by the fresh port is the actual touched scope. -/
theorem scope_constraint_touched (f : OccurrenceLabeling F Bool) (vs : List ℕ)
    {i : Fin F.length} (hi : i ∈ touched F vs) :
    (constraint f vs i).scope =
      (outsidePositions F[i.val].scope.length (positions vs F[i.val].scope)).map
        (fun j => F[i.val].scope.getD j 0) ++ [connector F i] := by
  have hp : (positions vs F[i.val].scope).isEmpty = false := by
    simpa only [List.isEmpty_eq_false_iff] using (mem_touched vs i).mp hi
  rw [scope_constraint, ← outsideScope_eq_filter]
  simp only [hp, Bool.false_eq_true, ↓reduceIte]

/-- The new terminal port of a touched original constraint. -/
@[expose] def connectorPort (f : OccurrenceLabeling F Bool) (vs : List ℕ)
    (i : Fin F.length) (hi : i ∈ touched F vs) : Occurrence (contract f vs) :=
  ⟨⟨i.val, by simpa only [length_contract] using Nat.lt_succ_of_lt i.isLt⟩,
    ⟨(outsidePositions F[i.val].scope.length (positions vs F[i.val].scope)).length, by
      simp only [get_contract_old, scope_constraint_touched f vs hi,
        List.length_append, List.length_map, List.length_singleton]
      omega⟩⟩

/-- The central port at an actual connector-scope position. -/
@[expose] def centralPort (f : OccurrenceLabeling F Bool) (vs : List ℕ)
    (k : Fin (connectors F vs).length) : Occurrence (contract f vs) :=
  ⟨⟨F.length, by simp⟩, ⟨k.val, by simpa only [get_contract_central] using k.isLt⟩⟩

@[simp] theorem connectorPort_var (f : OccurrenceLabeling F Bool) (vs : List ℕ)
    (i : Fin F.length) (hi : i ∈ touched F vs) : (connectorPort f vs i hi).var = connector F i := by
  simp [connectorPort, Occurrence.var, get_contract_old, scope_constraint_touched f vs hi]

@[simp] theorem centralPort_var (f : OccurrenceLabeling F Bool) (vs : List ℕ)
    (k : Fin (connectors F vs).length) : (centralPort f vs k).var = (connectors F vs)[k.val] := by
  simp [centralPort, Occurrence.var, get_contract_central]

/-- The touched-constraint end of every connector is honestly zero in the reference. -/
@[simp] theorem reference_connectorPort (f : OccurrenceLabeling F Bool) (vs : List ℕ)
    (i : Fin F.length) (hi : i ∈ touched F vs) :
    reference f vs (connectorPort f vs i hi) = false := by
  have hp : (positions vs F[i.val].scope).isEmpty = false := by
    simpa only [List.isEmpty_eq_false_iff] using (mem_touched vs i).mp hi
  change ((referenceRows f vs).getD i.val []).getD
    (outsidePositions F[i.val].scope.length (positions vs F[i.val].scope)).length false = false
  rw [referenceRows_project]
  simp only [hp, Bool.false_eq_true, ↓reduceIte]
  rw [List.getD_append_right _ _ _ _ (by simp [project])]
  simp [project]

/-- The central end of exactly the first connector is one. -/
@[simp] theorem reference_centralPort (f : OccurrenceLabeling F Bool) (vs : List ℕ)
    (k : Fin (connectors F vs).length) :
    reference f vs (centralPort f vs k) = decide (0 = k.val) := by
  change ((referenceRows f vs).getD F.length []).getD k.val false = _
  rw [get_referenceRows_central]
  rw [List.getD_eq_getElem _ _ (by
    simpa only [listSingle, List.length_map, List.length_range] using k.isLt)]
  simp only [listSingle, List.getElem_map, List.getElem_range]

/-- Every old outside variable retains its exact defect status under reference transport. -/
theorem inconsistent_reference_old (hF : EdgeInstance F) (f : OccurrenceLabeling F Bool)
    (vs : List ℕ) (o : Occurrence F) (ho : o.var ∉ vs) :
    Inconsistent (reference f vs) o.var ↔ Inconsistent f o.var := by
  have hp : (hF.partner o).var ∉ vs := by rwa [← hF.partner_variable o]
  let p := oldPort f vs o ho
  let q := oldPort f vs (hF.partner o) hp
  have hG := edge_contract hF f vs
  have hv : q.var = p.var := by
    rw [oldPort_var, oldPort_var]
    exact (hF.partner_variable o).symm
  have hn : q ≠ p := by
    intro he
    have hi := congrArg (fun a : Occurrence (contract f vs) => a.1.val) he
    exact hF.partner_constraint_ne o (Fin.ext hi.symm)
  have hq : q = hG.partner p := (hG.eq_or_eq_partner hv).resolve_left hn
  calc
    _ ↔ Inconsistent (reference f vs) p.var := by rw [oldPort_var]
    _ ↔ reference f vs p ≠ reference f vs q := by rw [hG.inconsistent_iff, ← hq]
    _ ↔ f o ≠ f (hF.partner o) := by rw [reference_oldPort, reference_oldPort]
    _ ↔ _ := (hF.inconsistent_iff f o).symm

/-- The connector at central scope position `k` is defective exactly when `k = 0`. -/
theorem inconsistent_reference_connector (hF : EdgeInstance F) (f : OccurrenceLabeling F Bool)
    (vs : List ℕ) (k : Fin (touched F vs).length) :
    Inconsistent (reference f vs) (connector F (touched F vs)[k.val]) ↔ k.val = 0 := by
  let i := (touched F vs)[k.val]
  have hi : i ∈ touched F vs := List.getElem_mem k.isLt
  let p := connectorPort f vs i hi
  let q := centralPort f vs ⟨k.val, by simpa only [length_connectors] using k.isLt⟩
  have hG := edge_contract hF f vs
  have hv : q.var = p.var := by
    rw [centralPort_var, connectorPort_var]
    simp only [connectors, List.getElem_map]
    rfl
  have hn : q ≠ p := by
    intro he
    have hh := congrArg (fun a : Occurrence (contract f vs) => a.1.val) he
    change F.length = i.val at hh
    have := i.isLt
    omega
  have hq : q = hG.partner p := (hG.eq_or_eq_partner hv).resolve_left hn
  calc
    _ ↔ Inconsistent (reference f vs) p.var := by rw [connectorPort_var]
    _ ↔ reference f vs p ≠ reference f vs q := by rw [hG.inconsistent_iff, ← hq]
    _ ↔ k.val = 0 := by
      simp [p, q, reference_connectorPort, reference_centralPort, eq_comm]

/-- The first connector is the unique new defect of the honest contracted reference. -/
@[expose] def baseConnector (F : CSP Table ℕ) (vs : List ℕ) (hne : touched F vs ≠ []) : ℕ :=
  connector F ((touched F vs).head hne)

/-- Exact reference-defect transport: old outside defects survive and the single central
one-hot entry contributes exactly one fresh connector defect. -/
theorem defects_reference (hF : EdgeInstance F) (f : OccurrenceLabeling F Bool) (vs : List ℕ)
    (hne : touched F vs ≠ []) :
    defects (reference f vs) = (defects f \ vs.toFinset) ∪ {baseConnector F vs hne} := by
  have hpos : 0 < (touched F vs).length := List.length_pos_iff.mpr hne
  have hb : baseConnector F vs hne = connector F ((touched F vs)[0]) := by
    simp only [baseConnector, List.getElem_zero]
  ext v
  simp only [mem_defects, mem_union, mem_sdiff, List.mem_toFinset, mem_singleton]
  constructor
  · intro hv
    have hm : v ∈ (contract f vs).vars := by
      obtain ⟨o, p, ho, hp, hn⟩ := hv
      exact ho ▸ o.var_mem
    have hset : v ∈ (F.vars.toFinset \ vs.toFinset) ∪ (connectors F vs).toFinset := by
      rw [← vars_contract f vs]
      exact List.mem_toFinset.mpr hm
    rcases mem_union.mp hset with hset | hset
    · obtain ⟨hm, hn⟩ := mem_sdiff.mp hset
      obtain ⟨o, rfl⟩ := (exists_occurrence_iff v).mpr (List.mem_toFinset.mp hm)
      have hout : o.var ∉ vs := by simpa using hn
      exact Or.inl ⟨(inconsistent_reference_old hF f vs o hout).mp hv, hout⟩
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hset)
      obtain ⟨k, hk, he⟩ := List.mem_iff_getElem.mp hi
      have hz := (inconsistent_reference_connector hF f vs ⟨k, hk⟩).mp (he ▸ hv)
      change k = 0 at hz
      subst k
      exact Or.inr (hb.trans (congrArg (connector F) he)).symm
  · rintro (⟨hv, hn⟩ | rfl)
    · obtain ⟨o, p, ho, hp, hne⟩ := hv
      have hout : o.var ∉ vs := ho.symm ▸ hn
      rw [← ho]
      apply (inconsistent_reference_old hF f vs o hout).mpr
      exact ⟨o, p, rfl, hp.trans ho.symm, hne⟩
    · rw [hb]
      exact (inconsistent_reference_connector hF f vs ⟨0, hpos⟩).mpr rfl

/-- The finite reference defect count deletes all old internal defects and inserts one.
A blossom supplies exactly one old internal defect, yielding count preservation. -/
theorem card_defects_reference (hF : EdgeInstance F) (f : OccurrenceLabeling F Bool)
    (vs : List ℕ) (hne : touched F vs ≠ []) :
    (defects (reference f vs)).card + (defects f ∩ vs.toFinset).card = (defects f).card + 1 := by
  have hfresh : baseConnector F vs hne ∉ defects f := by
    intro hv
    obtain ⟨o, p, ho, hp, hn⟩ := mem_defects.mp hv
    have hm : baseConnector F vs hne ∈ F.vars := ho ▸ o.var_mem
    exact connector_not_mem ((touched F vs).head hne) hm
  rw [defects_reference hF f vs hne, union_singleton, card_insert_of_notMem
    (fun hm => hfresh (mem_sdiff.mp hm).1)]
  have hp := card_sdiff_add_card_inter (defects f) vs.toFinset
  omega

/-- Observation 26's exact defect-count relation for the actual prepared blossom reference. -/
theorem card_defects_reference_blossom (hF : EdgeInstance F) {f : OccurrenceLabeling F Bool}
    {w : Walk F} (hb : w.IsBlossom Table.sem f) :
    (defects (reference f (internal w))).card = (defects f).card := by
  have hc := card_defects_reference hF f (internal w) (touched_ne_nil w hb.2.2.1)
  rw [defects_inter_internal hb, card_singleton] at hc
  omega

end Cslib.Logic.PL.CSP.Blossom
