/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.EdgeCSP.Blossom.Reference
public import Complexity.Logics.Propositional.CSP.Table.ContractionRows
public import Complexity.Logics.Propositional.CSP.Edge.Ports
import Mathlib.Data.List.GetD
import Complexity.Foundations.Data.List.Blocks

/-!
# Transporting changed outside labels through whole contraction

The row projection in Section 5.3 of [KazdaKolmogorovRolinek2018], arXiv:1602.03124v6,
printed pp. 12–13, applies to actual original occurrence labels. Connector zero fixes the
internal reference bits but places no restriction on outside changes. Connector one records
one actual changed internal port. All constructors retain the original positional interface.
-/

public section

namespace Cslib.Logic.PL.CSP.Blossom

open Table Finset

variable {F : CSP Table ℕ}

/-- Project changed original labels, supplying each connector bit and the actual central row. -/
@[expose] def transport (f : OccurrenceLabeling F Bool) (vs : List ℕ)
    (g : OccurrenceLabeling F Bool) (bits : Fin F.length → Bool) (central : List Bool) :
    OccurrenceLabeling (contract f vs) Bool := labels _ (transportRows g vs bits central)

/-- The old-constraint row of a general transport buffer. -/
theorem get_transportRows_old (g : OccurrenceLabeling F Bool) (vs : List ℕ)
    (bits : Fin F.length → Bool) (central : List Bool) (i : Fin F.length) :
    (transportRows g vs bits central).getD i.val [] =
      if (positions vs F[i.val].2).isEmpty then localTuple g i
      else project (localTuple g i)
        (outsidePositions F[i.val].2.length (positions vs F[i.val].2)) ++ [bits i] := by
  rw [List.getD_eq_getElem _ _ (by simp [transportRows])]
  simp [transportRows]

/-- The general buffer retains its supplied central row verbatim. -/
theorem get_transportRows_central (g : OccurrenceLabeling F Bool) (vs : List ℕ)
    (bits : Fin F.length → Bool) (central : List Bool) :
    (transportRows g vs bits central).getD F.length [] = central := by
  simp [transportRows]

/-- Every projected old row has exactly the constructor's actual scope width. -/
theorem transportRow_length (f g : OccurrenceLabeling F Bool) (vs : List ℕ)
    (bits : Fin F.length → Bool) (central : List Bool) (i : Fin F.length) :
    ((transportRows g vs bits central).getD i.val []).length = (constraint f vs i).2.length := by
  rw [get_transportRows_old]
  unfold constraint
  split <;> simp [localTuple, project]

/-- All actual output row widths agree when the central row has its finite scope width. -/
theorem transportRows_length (f g : OccurrenceLabeling F Bool) (vs : List ℕ)
    (bits : Fin F.length → Bool) {central : List Bool}
    (hc : central.length = (connectors F vs).length) (i : Fin (contract f vs).length) :
    ((transportRows g vs bits central).getD i.val []).length = (contract f vs)[i.val].2.length := by
  by_cases hi : i.val < F.length
  · simpa only [get_contract_old f vs ⟨i.val, hi⟩] using
      transportRow_length f g vs bits central ⟨i.val, hi⟩
  · have he : i.val = F.length := by have := i.isLt; simp only [length_contract] at this; omega
    simpa only [he, get_transportRows_central, get_contract_central] using hc

/-- The old rows project outside coordinates in their original order, with a bit appended
precisely at touched constraints. -/
theorem transportRows_project (g : OccurrenceLabeling F Bool) (vs : List ℕ)
    (bits : Fin F.length → Bool) (central : List Bool) (i : Fin F.length) :
    (transportRows g vs bits central).getD i.val [] =
      project (localTuple g i) (outsidePositions F[i.val].2.length (positions vs F[i.val].2)) ++
        if (positions vs F[i.val].2).isEmpty then [] else [bits i] := by
  rw [get_transportRows_old]
  split
  next hp =>
    have he := List.isEmpty_iff.mp hp
    have hl : (localTuple g i).length = F[i.val].2.length := by simp [localTuple]
    simp only [he, outsidePositions, List.contains_nil, Bool.not_false, List.filter_true,
      project, List.append_nil]
    rw [← hl, List.map_getD_range]
  · rfl

/-- Arbitrarily changed outside values survive the actual positional transport. -/
theorem transport_oldPort (f g : OccurrenceLabeling F Bool) (vs : List ℕ)
    (bits : Fin F.length → Bool) (central : List Bool) (o : Occurrence F) (ho : o.var ∉ vs) :
    transport f vs g bits central (oldPort f vs o ho) = g o := by
  let os := outsidePositions F[o.1.val].2.length (positions vs F[o.1.val].2)
  have hm : o.2.val ∈ os := (mem_outsidePositions _ _ _).mpr
    ⟨o.2.isLt, by simpa only [List.getD_eq_getElem _ _ o.2.isLt, Occurrence.var] using ho⟩
  have hl := List.idxOf_lt_length_iff.mpr hm
  change ((transportRows g vs bits central).getD o.1.val []).getD
    (os.idxOf o.2.val) false = g o
  rw [transportRows_project, List.getD_append _ _ _ _
    (by simpa only [project, List.length_map] using hl), project_getD_idxOf _ _ hm]
  simp [localTuple, o.2.isLt]

/-- The connector's old-constraint endpoint reads its supplied finite bit. -/
theorem transport_connectorPort (f g : OccurrenceLabeling F Bool) (vs : List ℕ)
    (bits : Fin F.length → Bool) (central : List Bool) (i : Fin F.length)
    (hi : i ∈ touched F vs) :
    transport f vs g bits central (connectorPort f vs i hi) = bits i := by
  have hp : (positions vs F[i.val].2).isEmpty = false := by
    simpa only [List.isEmpty_eq_false_iff] using (mem_touched vs i).mp hi
  change ((transportRows g vs bits central).getD i.val []).getD
    (outsidePositions F[i.val].2.length (positions vs F[i.val].2)).length false = bits i
  rw [transportRows_project]
  simp only [hp, Bool.false_eq_true, ↓reduceIte]
  rw [List.getD_append_right _ _ _ _ (by simp [project])]
  simp [project]

/-- The central endpoint reads the supplied central row at the actual scope position. -/
theorem transport_centralPort (f g : OccurrenceLabeling F Bool) (vs : List ℕ)
    (bits : Fin F.length → Bool) (central : List Bool) (k : Fin (connectors F vs).length) :
    transport f vs g bits central (centralPort f vs k) = central.getD k.val false := by
  change ((transportRows g vs bits central).getD F.length []).getD k.val false = _
  rw [get_transportRows_central]

/-- Feasible original rows with at most one selected deviation transport to feasible actual
contracted labels, with their computed connector bits and any accepted central one-hot row. -/
theorem valid_transport {f g : OccurrenceLabeling F Bool} (hf : ValidLabeling sem f)
    (hg : ValidLabeling sem g) (vs : List ℕ) (bits : Fin F.length → Bool)
    {central : List Bool} (hc : (exactlyOne (connectors F vs)).sem central = true)
    (hd : ∀ i ∈ touched F vs, deviations (localTuple f i) (localTuple g i)
      (positions vs F[i.val].2) ≤ 1)
    (hb : ∀ i ∈ touched F vs, bits i = decide (deviations (localTuple f i)
      (localTuple g i) (positions vs F[i.val].2) = 1)) :
    ValidLabeling sem (transport f vs g bits central) := by
  apply valid_labels
  · exact transportRows_length f g vs bits (sem_exactlyOne_eq_true _ _ |>.mp hc).1
  · intro i
    by_cases hi : i.val < F.length
    · let j : Fin F.length := ⟨i.val, hi⟩
      rw [get_contract_old f vs j, get_transportRows_old g vs bits central j]
      unfold constraint
      split
      · exact hg j
      next hp =>
        have hj : j ∈ touched F vs := (mem_touched vs j).mpr (by simpa using hp)
        apply (sem_contract_eq_true (canContract_constraint hf vs j)).mpr
        exact ⟨localTuple g j, (sem_eq_true.mp (hg j)).2, hd j hj, by
          simp only [localTuple, List.length_ofFn, hb j hj]⟩
    · have he : i.val = F.length := by have := i.isLt; simp only [length_contract] at this; omega
      simpa only [he, get_contract_central, get_transportRows_central] using hc

/-- Zero connectors reflect validity for arbitrary outside changes when the internal reference
bits are retained. This is the local inverse used before the first new connector of a walk. -/
theorem valid_of_transport_zero {f g : OccurrenceLabeling F Bool} (hf : ValidLabeling sem f)
    (vs : List ℕ) {central : List Bool}
    (hc : central.length = (connectors F vs).length)
    (hi : ∀ o : Occurrence F, o.var ∈ vs → g o = f o)
    (hg : ValidLabeling sem (transport f vs g (fun _ => false) central)) :
    ValidLabeling sem g := by
  intro i
  let j : Fin (contract f vs).length := ⟨i.val, by
    have := i.isLt
    simp only [length_contract]
    omega⟩
  have hv := hg j
  change (contract f vs)[i.val].1.sem
    (localTuple (labels _ (transportRows g vs (fun _ => false) central)) j) = true at hv
  rw [localTuple_labels _ _ j (transportRows_length f g vs _ hc j),
    get_contract_old f vs i, get_transportRows_old g vs (fun _ => false) central i] at hv
  unfold constraint at hv
  split at hv
  · exact hv
  · apply (sem_contract_zero_iff (canContract_constraint hf vs i) (by simp [localTuple]) ?_).mp
      (by simpa only [localTuple, List.length_ofFn] using hv)
    intro k hk
    have hkb := List.mem_range.mp (List.mem_filter.mp hk).1
    have hkv := (mem_positions vs i ⟨k, hkb⟩).mp hk
    simpa [localTuple, hkb] using hi ⟨i, ⟨k, hkb⟩⟩ hkv

/-- Arbitrary outside defects are preserved exactly by projection. -/
theorem inconsistent_transport_old (hF : EdgeInstance F) (f g : OccurrenceLabeling F Bool)
    (vs : List ℕ) (bits : Fin F.length → Bool) (central : List Bool)
    (o : Occurrence F) (ho : o.var ∉ vs) :
    Inconsistent (transport f vs g bits central) o.var ↔ Inconsistent g o.var := by
  have hp : (hF.partner o).var ∉ vs := by rwa [← hF.partner_variable o]
  let p := oldPort f vs o ho
  let q := oldPort f vs (hF.partner o) hp
  have hv : q.var = p.var := by rw [oldPort_var, oldPort_var]; exact (hF.partner_variable o).symm
  have hn : q ≠ p := by
    intro he
    exact hF.partner_constraint_ne o
      (Fin.ext (congrArg (fun a : Occurrence (contract f vs) => a.1.val) he).symm)
  rw [← oldPort_var f vs o ho,
    EdgeInstance.inconsistent_iff_of_two (edge_contract hF f vs) _ p q hv hn]
  rw [transport_oldPort, transport_oldPort, oldPort_var]
  exact (hF.inconsistent_iff g o).symm

/-- The connector's defect is exactly disagreement of its two supplied endpoint bits. -/
theorem inconsistent_transport_connector (hF : EdgeInstance F)
    (f g : OccurrenceLabeling F Bool) (vs : List ℕ) (bits : Fin F.length → Bool)
    (central : List Bool) (k : Fin (touched F vs).length) :
    Inconsistent (transport f vs g bits central) (connector F (touched F vs)[k.val]) ↔
      bits (touched F vs)[k.val] ≠ central.getD k.val false := by
  let i := (touched F vs)[k.val]
  have hi : i ∈ touched F vs := List.getElem_mem k.isLt
  let p := connectorPort f vs i hi
  let q := centralPort f vs ⟨k.val, by simpa only [length_connectors] using k.isLt⟩
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
  rw [← connectorPort_var f vs i hi,
    EdgeInstance.inconsistent_iff_of_two (edge_contract hF f vs) _ p q hv hn]
  exact show transport f vs g bits central p ≠ transport f vs g bits central q ↔ _ from by
    rw [transport_connectorPort, transport_centralPort]

/-- The actual finite connector defects, scanned by distinct touched-constraint position. -/
@[expose] def connectorDefects (F : CSP Table ℕ) (vs : List ℕ)
    (bits : Fin F.length → Bool) (central : List Bool) : List ℕ :=
  ((List.finRange (touched F vs).length).filter fun k =>
    bits (touched F vs)[k.val] != central.getD k.val false).map
      fun k => connector F (touched F vs)[k.val]

/-- Exact defect transport for arbitrary outside values and arbitrary finite connector rows. -/
theorem defects_transport (hF : EdgeInstance F) (f g : OccurrenceLabeling F Bool)
    (vs : List ℕ) (bits : Fin F.length → Bool) (central : List Bool) :
    defects (transport f vs g bits central) =
      (defects g \ vs.toFinset) ∪ (connectorDefects F vs bits central).toFinset := by
  ext v
  simp only [mem_defects, mem_union, mem_sdiff, List.mem_toFinset]
  constructor
  · intro hv
    have hm : v ∈ (contract f vs).vars := by
      obtain ⟨o, _, ho, _, _⟩ := hv
      exact ho ▸ o.var_mem
    have hset : v ∈ (F.vars.toFinset \ vs.toFinset) ∪ (connectors F vs).toFinset := by
      rw [← vars_contract f vs]
      exact List.mem_toFinset.mpr hm
    rcases mem_union.mp hset with hset | hset
    · obtain ⟨hm, hn⟩ := mem_sdiff.mp hset
      obtain ⟨o, rfl⟩ := (exists_occurrence_iff v).mpr (List.mem_toFinset.mp hm)
      have hout : o.var ∉ vs := by simpa using hn
      exact Or.inl ⟨(inconsistent_transport_old hF f g vs bits central o hout).mp hv, hout⟩
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hset)
      obtain ⟨k, hk, he⟩ := List.mem_iff_getElem.mp hi
      have hd := (inconsistent_transport_connector hF f g vs bits central ⟨k, hk⟩).mp (he ▸ hv)
      exact Or.inr (List.mem_map.mpr ⟨⟨k, hk⟩,
        List.mem_filter.mpr ⟨by simp, by simpa using hd⟩, congrArg (connector F) he⟩)
  · rintro (⟨hv, hn⟩ | hv)
    · obtain ⟨o, p, ho, hp, hne⟩ := hv
      have hout : o.var ∉ vs := ho.symm ▸ hn
      rw [← ho]
      apply (inconsistent_transport_old hF f g vs bits central o hout).mpr
      exact ⟨o, p, rfl, hp.trans ho.symm, hne⟩
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hv
      exact (inconsistent_transport_connector hF f g vs bits central k).mpr
        (by simpa using (List.mem_filter.mp hk).2)

/-- Restore every original internal reference bit and read all changed outside bits from their
actual surviving contracted ports. This is a total executable finite-label construction. -/
@[expose] def expandZero (f : OccurrenceLabeling F Bool) (vs : List ℕ)
    (g : OccurrenceLabeling (contract f vs) Bool) : OccurrenceLabeling F Bool :=
  fun o => if ho : o.var ∈ vs then f o else g (oldPort f vs o ho)

/-- If the connector endpoints keep their reference values, projecting the restored labels
recovers every actual contracted label, including arbitrary changed outside values. -/
theorem transport_expandZero (hF : EdgeInstance F) (f : OccurrenceLabeling F Bool)
    (vs : List ℕ) (g : OccurrenceLabeling (contract f vs) Bool)
    (hbits : ∀ i (hi : i ∈ touched F vs), g (connectorPort f vs i hi) = false)
    (hcentral : ∀ k : Fin (connectors F vs).length,
      g (centralPort f vs k) = (oneHot (connectors F vs).length 0).getD k.val false) :
    transport f vs (expandZero f vs g) (fun _ => false)
      (oneHot (connectors F vs).length 0) = g := by
  let hG := edge_contract hF f vs
  funext o
  have hset : o.var ∈ (F.vars.toFinset \ vs.toFinset) ∪ (connectors F vs).toFinset := by
    rw [← vars_contract f vs]
    exact List.mem_toFinset.mpr o.var_mem
  rcases mem_union.mp hset with hv | hv
  · obtain ⟨hm, hn⟩ := mem_sdiff.mp hv
    obtain ⟨p, hp⟩ := (exists_occurrence_iff o.var).mpr (List.mem_toFinset.mp hm)
    have hpo : p.var ∉ vs := by simpa only [hp, List.mem_toFinset] using hn
    have hqo : (hF.partner p).var ∉ vs := by rwa [← hF.partner_variable p]
    let a := oldPort f vs p hpo
    let b := oldPort f vs (hF.partner p) hqo
    have hab : b.var = a.var := by
      rw [oldPort_var, oldPort_var]
      exact (hF.partner_variable p).symm
    have hne : b ≠ a := by
      intro he
      exact hF.partner_constraint_ne p
        (Fin.ext (congrArg (fun a : Occurrence (contract f vs) => a.1.val) he).symm)
    have hoa : o.var = a.var := by rw [oldPort_var, hp]
    rcases hG.eq_or_eq_of_two hoa hab hne with rfl | rfl
    · rw [transport_oldPort]
      simp only [expandZero, dite_eq_right hpo]
      rfl
    · rw [transport_oldPort]
      simp only [expandZero, dite_eq_right hqo]
      rfl
  · obtain ⟨i, hi, he⟩ := List.mem_map.mp (List.mem_toFinset.mp hv)
    obtain ⟨k, hk, hki⟩ := List.mem_iff_getElem.mp hi
    let a := connectorPort f vs i hi
    let b := centralPort f vs ⟨k, by simpa only [length_connectors] using hk⟩
    have hab : b.var = a.var := by
      rw [centralPort_var, connectorPort_var]
      simp only [connectors, List.getElem_map, hki]
    have hne : b ≠ a := by
      intro hba
      have hh := congrArg (fun a : Occurrence (contract f vs) => a.1.val) hba
      change F.length = i.val at hh
      have := i.isLt
      omega
    have hoa : o.var = a.var := by rw [connectorPort_var]; exact he.symm
    rcases hG.eq_or_eq_of_two hoa hab hne with rfl | rfl
    · rw [transport_connectorPort, hbits i hi]
    · rw [transport_centralPort, hcentral]

/-- Restoring a valid zero-connector comparison gives a valid original labeling; outside
coordinates need not agree with the prepared reference. -/
theorem valid_expandZero (hF : EdgeInstance F) {f : OccurrenceLabeling F Bool}
    (hf : ValidLabeling sem f) (vs : List ℕ) (g : OccurrenceLabeling (contract f vs) Bool)
    (hg : ValidLabeling sem g)
    (hbits : ∀ i (hi : i ∈ touched F vs), g (connectorPort f vs i hi) = false)
    (hcentral : ∀ k : Fin (connectors F vs).length,
      g (centralPort f vs k) = (oneHot (connectors F vs).length 0).getD k.val false) :
    ValidLabeling sem (expandZero f vs g) := by
  apply valid_of_transport_zero hf vs (central := oneHot (connectors F vs).length 0)
    (by simp [oneHot]) (fun o ho => by simp only [expandZero, dite_eq_left ho])
  rwa [transport_expandZero hF f vs g hbits hcentral]

/-- Zero old connector ends and the honest central reference create one fresh defect. -/
theorem connectorDefects_zero (vs : List ℕ) (hne : touched F vs ≠ []) :
    (connectorDefects F vs (fun _ => false)
      (oneHot (connectors F vs).length 0)).toFinset = {baseConnector F vs hne} := by
  have hpos : 0 < (touched F vs).length := List.length_pos_iff.mpr hne
  have hpred (k : Fin (touched F vs).length) :
      (false != (oneHot (connectors F vs).length 0).getD k.val false) = true ↔ k.val = 0 := by
    rw [List.getD_eq_getElem _ _ (by simp [oneHot])]
    simp [oneHot, eq_comm]
  ext v
  simp only [connectorDefects, List.mem_toFinset, List.mem_map, List.mem_filter,
    List.mem_finRange, true_and, hpred, mem_singleton]
  constructor
  · rintro ⟨k, hk, he⟩
    have heq : k = ⟨0, hpos⟩ := Fin.ext hk
    subst k
    simpa only [baseConnector, List.getElem_zero] using he.symm
  · rintro rfl
    exact ⟨⟨0, hpos⟩, rfl, by simp only [baseConnector, List.getElem_zero]⟩

/-- General zero-connector transport deletes the old internal defects and inserts exactly one
fresh connector defect, even when every outside value has changed. -/
theorem card_defects_transport_zero (hF : EdgeInstance F) (f g : OccurrenceLabeling F Bool)
    (vs : List ℕ) (hne : touched F vs ≠ []) :
    (defects (transport f vs g (fun _ => false) (oneHot (connectors F vs).length 0))).card +
      (defects g ∩ vs.toFinset).card = (defects g).card + 1 := by
  have hfresh : baseConnector F vs hne ∉ defects g := by
    intro hv
    obtain ⟨o, _, ho, _, _⟩ := mem_defects.mp hv
    have hm : baseConnector F vs hne ∈ F.vars := ho ▸ o.var_mem
    exact connector_not_mem ((touched F vs).head hne) hm
  rw [defects_transport hF, connectorDefects_zero vs hne, union_singleton,
    card_insert_of_notMem (fun hm => hfresh (mem_sdiff.mp hm).1)]
  have hp := card_sdiff_add_card_inter (defects g) vs.toFinset
  omega

/-- A prepared blossom's internal defect is retained by zero expansion, and therefore the
expanded original labeling has exactly the returned comparison's defect count. -/
theorem card_defects_expandZero (hF : EdgeInstance F) {f : OccurrenceLabeling F Bool}
    {w : Walk F} (hb : w.IsBlossom sem f) (g : OccurrenceLabeling (contract f (internal w)) Bool)
    (hbits : ∀ i (hi : i ∈ touched F (internal w)),
      g (connectorPort f (internal w) i hi) = false)
    (hcentral : ∀ k : Fin (connectors F (internal w)).length,
      g (centralPort f (internal w) k) =
        (oneHot (connectors F (internal w)).length 0).getD k.val false) :
    (defects (expandZero f (internal w) g)).card = (defects g).card := by
  let e := expandZero f (internal w) g
  have hi : defects e ∩ (internal w).toFinset = defects f ∩ (internal w).toFinset :=
    defects_inter_eq_of_eqOn _ (fun o ho => by
      simp only [e, expandZero, dite_eq_left (List.mem_toFinset.mp ho)])
  have hc := card_defects_transport_zero hF f e (internal w) (touched_ne_nil w hb.2.2.1)
  rw [transport_expandZero hF f (internal w) g hbits hcentral, hi,
    defects_inter_internal hb, card_singleton] at hc
  change (defects e).card = (defects g).card
  omega

end Cslib.Logic.PL.CSP.Blossom
