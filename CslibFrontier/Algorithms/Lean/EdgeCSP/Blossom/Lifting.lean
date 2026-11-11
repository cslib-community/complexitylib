/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.EdgeCSP.Blossom.Exchange
public import CslibFrontier.Algorithms.Lean.EdgeCSP.Blossom.ExternalPrefix
public import CslibFrontier.Logics.Propositional.CSP.Edge.Walk.Boundary
public import CslibFrontier.Logics.Propositional.CSP.Edge.Augmenting

/-!
# Constructive lifting from the actual contracted instance

Lemma 44 of [KazdaKolmogorovRolinek2018], arXiv:1602.03124v6, printed pp. 20–22,
uses an actual contracted augmenting walk. Its prefix before the first connector restores
through the zero-connector row semantics, and the first connector step supplies an actual
original exchange. The shortest exit and full no-shortcut DAG argument then lift the change.
-/

public section

namespace Cslib.Logic.PL.CSP.Blossom

open Table DAG Finset
open Cslib.BitString

variable {F : CSP Table ℕ} {w : Walk F}

/-- The first connector of a contracted augmenting walk yields a valid original improvement.
Every outside-prefix and local-exchange fact is derived from the actual returned walk. -/
theorem lift_entering_augmentation (hF : EdgeInstance F) {f : OccurrenceLabeling F Bool}
    (hb : w.IsBlossom sem f) (hf : ValidLabeling sem f)
    (hM : EdgeInstance.EvenConstraints sem F) (fallback : Occurrence F)
    {p : Walk (contract f (internal w))} (hp : p.IsAugmenting sem (reference f (internal w)))
    (hx : p.start ≠ baseConnector F (internal w) (touched_ne_nil w hb.steps_ne_nil))
    (hex : ∃ o ∈ p.edges, o.var ∈ connectors F (internal w)) :
    ∃ g, liftPrefix f w (restoreWalk f (internal w) fallback
      (p.take (p.boundaryIndex (connectors F (internal w))))) = some g ∧
      ValidLabeling sem g ∧ (defects g).card + 2 = (defects f).card := by
  let vs := internal w
  have hrootset : p.start ∈ defects f \ vs.toFinset := by
    have hm := mem_defects.mpr hp.2.1
    rw [defects_reference hF f vs (touched_ne_nil w hb.2.2.1)] at hm
    exact (mem_union.mp hm).resolve_right (by simpa only [mem_singleton] using hx)
  have hroot : Inconsistent f p.start := mem_defects.mp (mem_sdiff.mp hrootset).1
  have hstart : p.start ∉ vs := by simpa only [List.mem_toFinset] using (mem_sdiff.mp hrootset).2
  have hstartconn : p.start ∉ connectors F vs := by
    intro hm
    obtain ⟨i, _, hi⟩ := List.mem_map.mp hm
    obtain ⟨o, _, ho, _, _⟩ := hroot
    have hmem : p.start ∈ F.vars := ho ▸ o.var_mem
    exact connector_not_mem i (hi.symm ▸ hmem)
  obtain ⟨hk, hbin, hno⟩ := Walk.boundaryIndex_spec hp.1.1.1
    (connectors F vs) hstartconn hex
  let k := p.boundaryIndex (connectors F vs)
  let a := p.steps[k].1
  let b := p.steps[k].2
  let q := p.take k
  let r := restoreWalk f vs fallback q
  have hqno : ∀ o ∈ q.edges, o.var ∉ connectors F vs := hno
  have haroot : a.var = q.finish := hp.1.1.1.input_eq_finish_take k hk
  have haout : a.var ∉ connectors F vs := haroot.symm ▸
    q.finish_property (P := fun v => v ∉ connectors F vs) hstartconn hqno
  let o := restorePortOr f vs fallback a
  obtain ⟨hout, himage⟩ := restorePortOr_spec hF f vs fallback a haout
  have hav := restorePortOr_var hF f vs fallback a haout
  have hai := restorePortOr_constraint hF f vs fallback a haout
  have hab := linked_constraint hp.1.1.1.1 (List.getElem_mem hk)
  change a.1 = b.1 at hab
  have hbindex : b.1.val < F.length := by
    rw [← hab, ← hai]
    exact o.1.isLt
  obtain ⟨i, hit, hconnector⟩ := exists_connectorPort hF f vs b hbin hbindex
  have hoi : o.1 = i := Fin.ext (hai.trans
    ((congrArg Fin.val hab).trans (congrArg (fun a : Occurrence (contract f vs) => a.1.val)
      hconnector).symm))
  have hot : o.1 ∈ touched F vs := hoi.symm ▸ hit
  have hcp : connectorPort f vs o.1 hot = b := by simpa only [hoi] using hconnector
  have hr := restoreWalk_isFPrefix hF hf vs fallback (hp.1.1.take k) hqno
  have hrv := (restoreWalk_spec hF f vs fallback (hp.1.1.1.take k) hqno).2
  have hcurrent : ValidLabeling sem (r.flip f) := by
    have hh := hr.valid_take r.steps.length le_rfl
    change ValidLabeling sem ((r.take r.steps.length).flip f) at hh
    simpa only [Walk.take, List.take_length] using hh
  have hinside : ∀ e : Occurrence F, e.var ∈ vs → r.flip f e = f e := by
    intro e he
    have hn : e ∉ r.edges := fun hm => hrv.2 e hm he
    simp [Walk.flip, BitString.flipOn_apply, hn]
  obtain ⟨hbits, hcentral⟩ := flip_reference_connectors f vs q hqno
  have htransport : transport f vs (r.flip f) (fun _ => false)
      (listSingle (connectors F vs).length 0) = q.flip (reference f vs) := by
    rw [restoreWalk_flip hF f vs fallback q hqno]
    exact transport_expandZero hF f vs _ hbits hcentral
  have hnew : ValidLabeling sem (pairFlip
      (transport f vs (r.flip f) (fun _ => false) (listSingle (connectors F vs).length 0))
      (oldPort f vs o hout) (connectorPort f vs o.1 hot)) := by
    rw [htransport, himage, hcp]
    have hv := hp.1.1.valid_take (k + 1) (by omega)
    rw [hp.1.1.1.flip_take_succ _ hk] at hv
    exact hv
  obtain ⟨e, hei, hevs, hevalid⟩ := exchange_of_connector hF hf hcurrent vs hinside
    o hout hot _ hnew
  have hecycle : e ∈ w.edges := (var_mem_internal_iff hF hb.1 hb.2.1 e).mp hevs
  have hunused : o ∉ r.edges := by
    intro hm
    have haa := (mem_restoreWalk_edges hF f vs fallback q hqno o hout).mp hm
    rw [himage] at haa
    have hn := (hp.1.1.1.take (k + 1)).2
    change (Walk.edgesOf (p.steps.take (k + 1))).Nodup at hn
    rw [List.take_succ_eq_append_getElem hk, Walk.edgesOf_append] at hn
    have ham : a ∈ Walk.edgesOf [p.steps[k]] := by
      change a ∈ [a, b]
      exact List.mem_cons_self
    exact (List.nodup_append.mp hn).2.2 _ haa _ ham rfl
  have hend : r.steps = [] ∨ r.start ≠ r.finish := by
    by_cases hk0 : k = 0
    · exact Or.inl (by simp [r, q, hk0, restoreWalk, Walk.mapPorts, Walk.take])
    · apply Or.inr
      have hc := hp.1.1.not_inconsistent_finish_take (n := k) (by omega) hk
      intro he
      have he' : p.start = q.finish := he.trans hrv.1
      exact hc (he' ▸ hp.2.1)
  apply liftPrefix_spec hF hb hM hr hend hroot hstart hrv.2
  refine ⟨r.steps.length, le_rfl, ?_⟩
  apply List.ne_nil_of_mem ((mem_exitsAt f w r r.steps.length o e).mpr ?_)
  simp only [Walk.take, List.take_length]
  exact ⟨hecycle, hav.trans (haroot.trans hrv.1.symm), hei.symm, hunused, hevalid⟩

/-- Lift an actual contracted augmenting walk. The fallback is taken from an actual cycle
step. Connector-free walks restore directly; all other walks use their first connector. -/
@[expose] def liftWalk (f : OccurrenceLabeling F Bool) (w : Walk F)
    (p : Walk (contract f (internal w))) : Option (OccurrenceLabeling F Bool) :=
  match w.steps with
  | [] => none
  | (fallback, _) :: _ =>
    if p.edges.all (fun o => !(connectors F (internal w)).contains o.var) then
      some ((restoreWalk f (internal w) fallback p).flip f)
    else liftPrefix f w (restoreWalk f (internal w) fallback
      (p.take (p.boundaryIndex (connectors F (internal w)))))

/-- Lemma 44 on actual positional augmenting walks: the constructor always returns valid
original labels and removes exactly two original defects. It supports both connector outcomes. -/
theorem liftWalk_spec (hF : EdgeInstance F) {f : OccurrenceLabeling F Bool}
    (hb : w.IsBlossom sem f) (hf : ValidLabeling sem f)
    (hM : EdgeInstance.EvenConstraints sem F)
    {p : Walk (contract f (internal w))} (hp : p.IsAugmenting sem (reference f (internal w)))
    (hx : p.start ≠ baseConnector F (internal w) (touched_ne_nil w hb.steps_ne_nil)) :
    ∃ g, liftWalk f w p = some g ∧ ValidLabeling sem g ∧
      (defects g).card + 2 = (defects f).card := by
  cases he : w.steps with
  | nil => exact (hb.2.2.1 he).elim
  | cons s ss =>
    rcases s with ⟨fallback, output⟩
    by_cases hall : p.edges.all (fun o => !(connectors F (internal w)).contains o.var) = true
    · have hno : ∀ o ∈ p.edges, o.var ∉ connectors F (internal w) := by
        intro o ho
        have hh := List.all_eq_true.mp hall o ho
        simpa using hh
      obtain ⟨hv, hc⟩ := restore_augmentation hF hb hf fallback hp hno
      exact ⟨_, by simp only [liftWalk, he, hall, ↓reduceIte], hv, hc⟩
    · have hex : ∃ o ∈ p.edges, o.var ∈ connectors F (internal w) := by
        by_contra hn
        apply hall
        apply List.all_eq_true.mpr
        intro o ho
        have hnot : o.var ∉ connectors F (internal w) := fun hv => hn ⟨o, ho, hv⟩
        simpa using hnot
      obtain ⟨g, hg, hv, hc⟩ := lift_entering_augmentation hF hb hf hM fallback hp hx hex
      exact ⟨g, by simpa only [liftWalk, he, hall, Bool.false_eq_true, ↓reduceIte] using hg,
        hv, hc⟩

/-- Lift an arbitrary improving valid contracted comparison. Lemma 31 constructs its actual
augmenting walk starting away from the single new reference defect; Lemma 44 lifts that walk.
The output is a strict improvement by two, as in the source, rather than an asserted equality
with the possibly much smaller comparison's defect count. -/
@[expose] def liftComparison (f : OccurrenceLabeling F Bool) (w : Walk F)
    (g : OccurrenceLabeling (contract f (internal w)) Bool) :
    Option (OccurrenceLabeling F Bool) :=
  if h : touched F (internal w) = [] then none else do
    let p ← EdgeInstance.augmentingWalk sem (reference f (internal w)) g
      (baseConnector F (internal w) h)
    liftWalk f w p

/-- Constructive strict-improvement transfer for every actual returned contracted labeling.
No global model, outside-comparison promise, or solver/lifting provider is assumed. -/
theorem liftComparison_spec (hF : EdgeInstance F) {f : OccurrenceLabeling F Bool}
    (hb : w.IsBlossom sem f) (hf : ValidLabeling sem f)
    (hM : EdgeInstance.EvenConstraints sem F)
    (g : OccurrenceLabeling (contract f (internal w)) Bool) (hg : ValidLabeling sem g)
    (hlt : (defects g).card < (defects (reference f (internal w))).card) :
    ∃ result, liftComparison f w g = some result ∧ ValidLabeling sem result ∧
      (defects result).card + 2 = (defects f).card := by
  have hne := touched_ne_nil w hb.2.2.1
  obtain ⟨p, hp, ha, hx, _⟩ := EdgeInstance.augmentingWalk_spec
    (edge_contract hF f (internal w)) (even_contract hf hM (internal w) hne)
    (valid_reference hf (internal w) hne) hg hlt (baseConnector F (internal w) hne)
  obtain ⟨result, hr, hv, hc⟩ := liftWalk_spec hF hb hf hM ha hx
  refine ⟨result, ?_, hv, hc⟩
  simp only [liftComparison, dite_eq_right hne, hp, Option.bind_eq_bind, Option.bind_some]
  exact hr

end Cslib.Logic.PL.CSP.Blossom
