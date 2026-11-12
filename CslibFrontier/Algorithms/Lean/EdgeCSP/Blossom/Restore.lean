/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.EdgeCSP.Blossom.Transport
public import CslibFrontier.Logics.Propositional.CSP.Edge.Walk.Map
public import CslibFrontier.Logics.Propositional.CSP.Occurrence.Enumeration
import Mathlib.Data.List.GetD

/-!
# Restoring surviving original incidences

Finite lookup in the actual original port list inverts whole-instance contraction away from
fresh connectors. The walk map retains original constraint positions and binary variable names.
The fallback is used only to make lookup total; the proved domain never reaches it.
-/

public section

namespace Cslib.Logic.PL.CSP.Blossom

open Table Finset
open Cslib.BitString

variable {F : CSP Table ℕ}

/-- Every nonconnector port of the actual contracted edge instance is a surviving old port. -/
theorem exists_oldPort (hF : EdgeInstance F) (f : OccurrenceLabeling F Bool) (vs : List ℕ)
    (o : Occurrence (contract f vs)) (ho : o.var ∉ connectors F vs) :
    ∃ p : Occurrence F, ∃ hp : p.var ∉ vs, oldPort f vs p hp = o := by
  have hv : o.var ∈ F.vars.toFinset \ vs.toFinset := by
    have hm : o.var ∈ (F.vars.toFinset \ vs.toFinset) ∪ (connectors F vs).toFinset := by
      rw [← vars_contract f vs]
      exact List.mem_toFinset.mpr o.var_mem
    exact (mem_union.mp hm).resolve_right (by simpa using ho)
  obtain ⟨p, hpv⟩ := (exists_occurrence_iff o.var).mpr (List.mem_toFinset.mp (mem_sdiff.mp hv).1)
  have hp : p.var ∉ vs := by simpa only [hpv, List.mem_toFinset] using (mem_sdiff.mp hv).2
  have hq : (hF.partner p).var ∉ vs := by rwa [← hF.partner_variable p]
  let a := oldPort f vs p hp
  let b := oldPort f vs (hF.partner p) hq
  have hab : b.var = a.var := by
    rw [oldPort_var, oldPort_var]
    exact (hF.partner_variable p).symm
  have hne : b ≠ a := by
    intro he
    exact hF.partner_constraint_ne p
      (Fin.ext (congrArg (fun a : Occurrence (contract f vs) => a.1.val) he).symm)
  have hoa : o.var = a.var := by rw [oldPort_var, hpv]
  rcases (edge_contract hF f vs).eq_or_eq_of_two hoa hab hne with he | he
  · exact ⟨p, hp, he.symm⟩
  · exact ⟨hF.partner p, hq, he.symm⟩

/-- A connector port at an old constraint is exactly that constraint's terminal fresh port.
The central alternative is excluded by its appended constraint index. -/
theorem exists_connectorPort (hF : EdgeInstance F) (f : OccurrenceLabeling F Bool)
    (vs : List ℕ) (o : Occurrence (contract f vs)) (ho : o.var ∈ connectors F vs)
    (hindex : o.1.val < F.length) :
    ∃ i : Fin F.length, ∃ hi : i ∈ touched F vs, connectorPort f vs i hi = o := by
  obtain ⟨i, hi, he⟩ := List.mem_map.mp ho
  obtain ⟨k, hk, hki⟩ := List.mem_iff_getElem.mp hi
  let a := connectorPort f vs i hi
  let b := centralPort f vs ⟨k, by simpa only [length_connectors] using hk⟩
  have hab : b.var = a.var := by
    rw [centralPort_var, connectorPort_var]
    simp only [connectors, List.getElem_map, hki]
  have hne : b ≠ a := by
    intro hh
    have hh := congrArg (fun a : Occurrence (contract f vs) => a.1.val) hh
    change F.length = i.val at hh
    have := i.isLt
    omega
  have hoa : o.var = a.var := by rw [connectorPort_var]; exact he.symm
  rcases (edge_contract hF f vs).eq_or_eq_of_two hoa hab hne with heq | heq
  · exact ⟨i, hi, heq.symm⟩
  · have hh := congrArg (fun a : Occurrence (contract f vs) => a.1.val) heq
    change o.1.val = F.length at hh
    omega

/-- Find an original outside port by scanning actual original incidences. -/
@[expose] def restorePort (f : OccurrenceLabeling F Bool) (vs : List ℕ)
    (o : Occurrence (contract f vs)) : Option (Occurrence F) :=
  (incidenceList F).find? fun p =>
    if hp : p.var ∈ vs then false else oldPort f vs p hp == o

/-- Nonconnector lookup returns an actual surviving port with exactly the requested image. -/
theorem restorePort_spec (hF : EdgeInstance F) (f : OccurrenceLabeling F Bool) (vs : List ℕ)
    (o : Occurrence (contract f vs)) (ho : o.var ∉ connectors F vs) :
    ∃ p, restorePort f vs o = some p ∧ ∃ hp : p.var ∉ vs, oldPort f vs p hp = o := by
  obtain ⟨q, hq, heq⟩ := exists_oldPort hF f vs o ho
  cases he : restorePort f vs o with
  | none =>
    have hh := List.find?_eq_none.mp he q (mem_incidenceList q)
    exact (hh (by simp only [dite_eq_right hq, heq, beq_self_eq_true])).elim
  | some p =>
    have hfind : (incidenceList F).find? (fun p =>
        if hp : p.var ∈ vs then false else oldPort f vs p hp == o) = some p := he
    have hh := List.find?_some hfind
    by_cases hp : p.var ∈ vs
    · simp only [dite_eq_left hp, Bool.false_eq_true] at hh
    · exact ⟨p, rfl, hp, by simpa only [dite_eq_right hp, beq_iff_eq] using hh⟩

/-- Total original-port lookup, with an explicit actual fallback for malformed requests. -/
@[expose] def restorePortOr (f : OccurrenceLabeling F Bool) (vs : List ℕ)
    (fallback : Occurrence F) (o : Occurrence (contract f vs)) : Occurrence F :=
  (restorePort f vs o).getD fallback

/-- On the certified domain the fallback is irrelevant and lookup is the actual inverse. -/
theorem restorePortOr_spec (hF : EdgeInstance F) (f : OccurrenceLabeling F Bool) (vs : List ℕ)
    (fallback : Occurrence F) (o : Occurrence (contract f vs))
    (ho : o.var ∉ connectors F vs) :
    ∃ hp : (restorePortOr f vs fallback o).var ∉ vs,
      oldPort f vs (restorePortOr f vs fallback o) hp = o := by
  obtain ⟨p, he, hp, ho⟩ := restorePort_spec hF f vs o ho
  simp only [restorePortOr, he, Option.getD_some]
  exact ⟨hp, ho⟩

/-- Successful restoration retains the original binary variable name. -/
theorem restorePortOr_var (hF : EdgeInstance F) (f : OccurrenceLabeling F Bool) (vs : List ℕ)
    (fallback : Occurrence F) (o : Occurrence (contract f vs)) (ho : o.var ∉ connectors F vs) :
    (restorePortOr f vs fallback o).var = o.var := by
  obtain ⟨hp, he⟩ := restorePortOr_spec hF f vs fallback o ho
  exact (oldPort_var f vs _ hp).symm.trans (congrArg Occurrence.var he)

/-- Successful restoration retains the actual original constraint position. -/
theorem restorePortOr_constraint (hF : EdgeInstance F) (f : OccurrenceLabeling F Bool)
    (vs : List ℕ) (fallback : Occurrence F) (o : Occurrence (contract f vs))
    (ho : o.var ∉ connectors F vs) : (restorePortOr f vs fallback o).1.val = o.1.val := by
  obtain ⟨hp, he⟩ := restorePortOr_spec hF f vs fallback o ho
  exact congrArg (fun p : Occurrence (contract f vs) => p.1.val) he

/-- Surviving original ports are embedded injectively in the actual output occurrence type. -/
theorem oldPort_injective (hF : EdgeInstance F) (f : OccurrenceLabeling F Bool) (vs : List ℕ)
    {o p : Occurrence F} (ho : o.var ∉ vs) (hp : p.var ∉ vs)
    (he : oldPort f vs o ho = oldPort f vs p hp) : o = p := by
  have hv : o.var = p.var := by
    rw [← oldPort_var f vs o ho, ← oldPort_var f vs p hp]
    exact congrArg Occurrence.var he
  have hc : o.1 = p.1 := Fin.ext
    (congrArg (fun a : Occurrence (contract f vs) => a.1.val) he)
  exact hF.eq_of_constraint_eq hv hc

/-- Restoring an actual outside original port cancels the positional embedding. -/
theorem restorePortOr_oldPort (hF : EdgeInstance F) (f : OccurrenceLabeling F Bool)
    (vs : List ℕ) (fallback o : Occurrence F) (ho : o.var ∉ vs) :
    restorePortOr f vs fallback (oldPort f vs o ho) = o := by
  have hn : (oldPort f vs o ho).var ∉ connectors F vs := by
    rw [oldPort_var]
    intro hc
    obtain ⟨i, _, he⟩ := List.mem_map.mp hc
    exact connector_not_mem i (he ▸ o.var_mem)
  obtain ⟨hp, he⟩ := restorePortOr_spec hF f vs fallback (oldPort f vs o ho) hn
  exact oldPort_injective hF f vs hp ho he

/-- Restore each actual port of a contracted walk by the finite original-port lookup. -/
@[expose] def restoreWalk (f : OccurrenceLabeling F Bool) (vs : List ℕ)
    (fallback : Occurrence F) (p : Walk (contract f vs)) : Walk F :=
  Walk.mapPorts (restorePortOr f vs fallback) p

/-- A contracted trail avoiding connectors restores to an actual outside original trail with
the same variable endpoints. Repeated original constraints remain positional. -/
theorem restoreWalk_spec (hF : EdgeInstance F) (f : OccurrenceLabeling F Bool) (vs : List ℕ)
    (fallback : Occurrence F) {p : Walk (contract f vs)} (hp : p.IsWalk)
    (hno : ∀ o ∈ p.edges, o.var ∉ connectors F vs) :
    (restoreWalk f vs fallback p).IsWalk ∧
      (restoreWalk f vs fallback p).finish = p.finish ∧
      ∀ o ∈ (restoreWalk f vs fallback p).edges, o.var ∉ vs := by
  have hv := fun o ho => restorePortOr_var hF f vs fallback o (hno o ho)
  refine ⟨hp.mapPorts _ hv ?_ ?_, Walk.finish_mapPorts _ _ hv, ?_⟩
  · intro s hs
    have h1 : s.1 ∈ p.edges := List.mem_flatMap.mpr ⟨s, hs, by simp⟩
    have h2 : s.2 ∈ p.edges := List.mem_flatMap.mpr ⟨s, hs, by simp⟩
    apply Fin.ext
    rw [restorePortOr_constraint hF f vs fallback s.1 (hno _ h1),
      restorePortOr_constraint hF f vs fallback s.2 (hno _ h2)]
    exact congrArg Fin.val (DAG.linked_constraint hp.1 hs)
  · intro o ho q hq heq
    obtain ⟨hro, hero⟩ := restorePortOr_spec hF f vs fallback o (hno o ho)
    obtain ⟨hrq, herq⟩ := restorePortOr_spec hF f vs fallback q (hno q hq)
    have he : (⟨restorePortOr f vs fallback o, hro⟩ : {a : Occurrence F // a.var ∉ vs}) =
        ⟨restorePortOr f vs fallback q, hrq⟩ := Subtype.ext heq
    exact hero.symm.trans ((congrArg (fun a => oldPort f vs a.val a.property) he).trans herq)
  · intro o ho
    rw [restoreWalk, Walk.edges_mapPorts] at ho
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ho
    obtain ⟨hqout, _⟩ := restorePortOr_spec hF f vs fallback q (hno q hq)
    exact hqout

/-- Membership in a restored outside trail is the exact inverse of surviving-port transport. -/
theorem mem_restoreWalk_edges (hF : EdgeInstance F) (f : OccurrenceLabeling F Bool)
    (vs : List ℕ) (fallback : Occurrence F) (p : Walk (contract f vs))
    (hno : ∀ o ∈ p.edges, o.var ∉ connectors F vs) (o : Occurrence F) (ho : o.var ∉ vs) :
    o ∈ (restoreWalk f vs fallback p).edges ↔ oldPort f vs o ho ∈ p.edges := by
  rw [restoreWalk, Walk.edges_mapPorts, List.mem_map]
  constructor
  · rintro ⟨q, hq, heq⟩
    obtain ⟨hrq, herq⟩ := restorePortOr_spec hF f vs fallback q (hno q hq)
    have he : (⟨restorePortOr f vs fallback q, hrq⟩ : {a : Occurrence F // a.var ∉ vs}) =
        ⟨o, ho⟩ := Subtype.ext heq
    have hh := (congrArg (fun a => oldPort f vs a.val a.property) he).symm.trans herq
    exact hh ▸ hq
  · intro hm
    exact ⟨oldPort f vs o ho, hm, restorePortOr_oldPort hF f vs fallback o ho⟩

/-- Flipping a restored outside walk is exactly zero-expansion of the actual contracted flip. -/
theorem restoreWalk_flip (hF : EdgeInstance F) (f : OccurrenceLabeling F Bool)
    (vs : List ℕ) (fallback : Occurrence F) (p : Walk (contract f vs))
    (hno : ∀ o ∈ p.edges, o.var ∉ connectors F vs) :
    (restoreWalk f vs fallback p).flip f = expandZero f vs (p.flip (reference f vs)) := by
  funext o
  by_cases ho : o.var ∈ vs
  · have hn : o ∉ (restoreWalk f vs fallback p).edges := by
      rw [restoreWalk, Walk.edges_mapPorts]
      rintro hm
      obtain ⟨q, hq, he⟩ := List.mem_map.mp hm
      obtain ⟨hrq, _⟩ := restorePortOr_spec hF f vs fallback q (hno q hq)
      exact hrq (congrArg Occurrence.var he ▸ ho)
    simp only [expandZero, dite_eq_left ho, Walk.flip, BitString.flipOn_apply,
      List.mem_toFinset, hn, ↓reduceIte]
  · have hm := mem_restoreWalk_edges hF f vs fallback p hno o ho
    simp only [expandZero, dite_eq_right ho, Walk.flip, BitString.flipOn_apply,
      List.mem_toFinset, hm, reference_oldPort]

/-- Avoiding connector variables leaves both endpoint values of every fresh connector at the
actual reference values, including the honest central one-hot row. -/
theorem flip_reference_connectors (f : OccurrenceLabeling F Bool) (vs : List ℕ)
    (p : Walk (contract f vs)) (hno : ∀ o ∈ p.edges, o.var ∉ connectors F vs) :
    (∀ i (hi : i ∈ touched F vs),
      p.flip (reference f vs) (connectorPort f vs i hi) = false) ∧
    (∀ k : Fin (connectors F vs).length,
      p.flip (reference f vs) (centralPort f vs k) =
        (listSingle (connectors F vs).length 0).getD k.val false) := by
  have hunchanged : ∀ o : Occurrence (contract f vs), o.var ∈ connectors F vs →
      p.flip (reference f vs) o = reference f vs o := by
    intro o ho
    have hn : o ∉ p.edges := fun he => hno o he ho
    simp [Walk.flip, BitString.flipOn_apply, hn]
  constructor
  · intro i hi
    rw [hunchanged _ (by rw [connectorPort_var]; exact List.mem_map.mpr ⟨i, hi, rfl⟩),
      reference_connectorPort]
  · intro k
    rw [hunchanged _ (by rw [centralPort_var]; exact List.getElem_mem k.isLt),
      reference_centralPort, List.getD_eq_getElem _ _ (by
        simpa only [listSingle, List.length_map, List.length_range] using k.isLt)]
    simp [listSingle]

/-- Every connector-free contracted f-prefix restores to an original f-prefix. Each actual
intermediate row is reflected through connector zero, so arbitrary outside changes are allowed. -/
theorem restoreWalk_isFPrefix (hF : EdgeInstance F) {f : OccurrenceLabeling F Bool}
    (hf : ValidLabeling sem f) (vs : List ℕ) (fallback : Occurrence F)
    {p : Walk (contract f vs)} (hp : p.IsFPrefix sem (reference f vs))
    (hno : ∀ o ∈ p.edges, o.var ∉ connectors F vs) :
    (restoreWalk f vs fallback p).IsFPrefix sem f := by
  have hw := (restoreWalk_spec hF f vs fallback hp.1 hno).1
  refine ⟨hw, ?_, ?_⟩
  · apply hp.2.1.mapPorts (restorePortOr f vs fallback)
    intro o ho
    obtain ⟨hr, _⟩ := restorePortOr_spec hF f vs fallback o (hno o ho)
    have hd := (inconsistent_reference_old hF f vs (restorePortOr f vs fallback o) hr).symm
    simpa only [restorePortOr_var hF f vs fallback o (hno o ho)] using hd
  · apply Walk.prefixValid_iff_forall_take.mpr
    intro n hn
    have hnp : n ≤ p.steps.length := by simpa only [restoreWalk, Walk.mapPorts,
      List.length_map] using hn
    have hno' : ∀ o ∈ (p.take n).edges, o.var ∉ connectors F vs := by
      intro o ho
      exact hno o ((List.take_sublist n p.steps).flatMap (fun s => [s.1, s.2]) |>.subset ho)
    obtain ⟨hbits, hcentral⟩ := flip_reference_connectors f vs (p.take n) hno'
    have hv := valid_expandZero hF hf vs ((p.take n).flip (reference f vs))
      (hp.valid_take n hnp) hbits hcentral
    rw [← restoreWalk_flip hF f vs fallback (p.take n) hno'] at hv
    have ht : restoreWalk f vs fallback (p.take n) = (restoreWalk f vs fallback p).take n :=
      Walk.mapPorts_take _ _ _
    rw [ht, Walk.flip, Walk.edges, ← Walk.flipSteps_eq_flipOn f _ (hw.take n).2] at hv
    exact hv

/-- Distinct endpoints are retained when restoring a contracted f-walk avoiding connectors. -/
theorem restoreWalk_isFWalk (hF : EdgeInstance F) {f : OccurrenceLabeling F Bool}
    (hf : ValidLabeling sem f) (vs : List ℕ) (fallback : Occurrence F)
    {p : Walk (contract f vs)} (hp : p.IsFWalk sem (reference f vs))
    (hno : ∀ o ∈ p.edges, o.var ∉ connectors F vs) :
    (restoreWalk f vs fallback p).IsFWalk sem f := by
  refine ⟨restoreWalk_isFPrefix hF hf vs fallback hp.1 hno, ?_⟩
  rw [(restoreWalk_spec hF f vs fallback hp.1.1 hno).2.1]
  exact hp.2

/-- The connector-free case of Lemma 44 returns the actual restored finite walk flip and
removes exactly two original defects, with no condition on changed outside comparison values. -/
theorem restore_augmentation (hF : EdgeInstance F) {f : OccurrenceLabeling F Bool}
    {w : Walk F} (hb : w.IsBlossom sem f) (hf : ValidLabeling sem f) (fallback : Occurrence F)
    {p : Walk (contract f (internal w))} (hp : p.IsAugmenting sem (reference f (internal w)))
    (hno : ∀ o ∈ p.edges, o.var ∉ connectors F (internal w)) :
    ValidLabeling sem ((restoreWalk f (internal w) fallback p).flip f) ∧
      (defects ((restoreWalk f (internal w) fallback p).flip f)).card + 2 = (defects f).card := by
  have hq := restoreWalk_isFPrefix hF hf (internal w) fallback hp.1.1 hno
  constructor
  · have hv := hq.valid_take (restoreWalk f (internal w) fallback p).steps.length le_rfl
    simpa only [Walk.take, List.take_length] using hv
  · obtain ⟨hbits, hcentral⟩ := flip_reference_connectors f (internal w) p hno
    have hc := card_defects_expandZero hF hb (p.flip (reference f (internal w))) hbits hcentral
    rw [← restoreWalk_flip hF f (internal w) fallback p hno] at hc
    rw [hc]
    exact (hp.card_defects_flip_add_two (edge_contract hF f (internal w))).trans
      (card_defects_reference_blossom hF hb)

end Cslib.Logic.PL.CSP.Blossom
