/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.EdgeCSP.Blossom.Arms
import Complexity.Logics.Propositional.CSP.Edge.Ports
import Complexity.Foundations.Data.Finset.SymmDiff

/-!
# Preserving a blossom through an outside prefix

Lemma 43 of [KazdaKolmogorovRolinek2018], arXiv:1602.03124v6, printed p. 20, transfers the
full six-invariant DAG through a shortest externally extendible prefix. This wrapper retains
the original cycle, copied-step distinctness, and its one internal defect. It imposes no
agreement condition on outside comparison labels.
-/

public section

namespace Cslib.Logic.PL.CSP.Blossom

open DAG Finset
open scoped symmDiff

variable {F : CSP Table ℕ} {w q : Walk F}

/-- For a nonempty linked cycle, the displayed graph support is its actual internal variables. -/
theorem blossomDAG_vars_eq_internal (hw : w.IsWalk) (hn : w.steps ≠ []) {ts : List ℕ}
    (hl : ts.length = w.steps.length) (pivot : ℕ) :
    (blossomDAG w ts pivot).vars = (internal w).toFinset := by
  rw [blossomDAG_vars _ _ _ hl]
  have hs := hw.start_mem_vars hn
  ext v
  simp only [internal, List.mem_toFinset, List.mem_dedup, mem_insert]
  exact or_iff_right_of_imp (fun he => he ▸ hs)

/-- An outside prefix with no earlier feasible extension preserves the actual blossom witness.
The supplied no-extension test concerns original incidences, in both DAG orientations. -/
theorem blossom_after_prefix {f : OccurrenceLabeling F Bool} (hb : w.IsBlossom Table.sem f)
    (hM : EdgeInstance.EvenConstraints Table.sem F) (hq : q.IsFWalk Table.sem f)
    (hstart : q.start ∉ internal w) (hvars : ∀ o ∈ q.edges, o.var ∉ internal w)
    (hno : ∀ n < q.steps.length, ∀ e ∈ w.edges, ∀ o : Occurrence F,
      o.var = (q.take n).finish → o.1 = e.1 →
        ¬ ((q.take n).snoc o e).IsFWalk Table.sem f) :
    w.IsBlossom Table.sem (q.flip f) := by
  obtain ⟨ts, pivot, hd, hp0, hp1, h⟩ := hb.2.2.2.2.2
  have hnative : (blossomDAG w ts pivot).IsFDAG Table.sem f := by
    have hi : Classical.decEq ℕ = instDecidableEqNat := Subsingleton.elim _ _
    exact congrArg (fun d => @blossomDAG Table ℕ F d w ts pivot) hi ▸ h
  have hsupport := blossomDAG_vars_eq_internal hb.1 hb.2.2.1 hd.1 pivot
  have hdag : (blossomDAG w ts pivot).IsFDAG Table.sem (q.flip f) := by
    apply hnative.flip_walk_of_no_prefix_extension hM hq
    · rwa [hsupport, List.mem_toFinset]
    · intro o ho
      rw [hsupport, List.mem_toFinset]
      exact hvars o ho
    · intro n hn a ha o hov hoc
      have ham : a.occurrence ∈ w.edges := by
        apply List.mem_toFinset.mp
        rw [← blossomDAG_occurrences _ _ _ hd.1]
        exact mem_image.mpr ⟨a, ha, rfl⟩
      exact hno n hn a.occurrence ham o hov hoc
  have hagree : ∀ o : Occurrence F, o.var ∈ internal w → q.flip f o = f o := by
    intro o ho
    have hon : o ∉ q.edges := fun he => hvars o he ho
    simp [Walk.flip, BitString.flipOn_apply, hon]
  have hstartmem : w.start ∈ internal w := List.mem_dedup.mpr
    (hb.1.start_mem_vars hb.2.2.1)
  have hbase := (inconsistent_congr (fun o ho => hagree o (ho ▸ hstartmem))).mpr hb.2.2.2.1
  have hcons : Walk.InternallyConsistent (q.flip f) w.steps := by
    apply (Walk.internallyConsistent_iff_splits _ _).mpr
    intro pre o p a b post he
    have hp : p.var ∈ internal w := by
      apply List.mem_dedup.mpr
      apply List.mem_map.mpr
      refine ⟨p, ?_, rfl⟩
      exact List.mem_flatMap.mpr ⟨(o, p), by simp [he], by simp⟩
    exact fun hi => ((Walk.internallyConsistent_iff_splits f _).mp hb.2.2.2.2.1
      pre o p a b post he) ((inconsistent_congr (fun o ho => hagree o (ho ▸ hp))).mp hi)
  refine ⟨hb.1, hb.2.1, hb.2.2.1, hbase, hcons, ts, pivot, hd, hp0, hp1, ?_⟩
  have hi : instDecidableEqNat = Classical.decEq ℕ := Subsingleton.elim _ _
  exact congrArg (fun d => @blossomDAG Table ℕ F d w ts pivot) hi ▸ hdag

/-- Actual unused outside ports and cycle ports allowing an exchange at a given prefix. -/
@[expose] def exitsAt (f : OccurrenceLabeling F Bool) (w r : Walk F)
    (n : ℕ) : List (Occurrence F × Occurrence F) :=
  (incidenceList F).flatMap fun o =>
    (w.edges.filter fun e => decide (o.var = (r.take n).finish ∧ o.1 = e.1 ∧
      o ∉ (r.take n).edges ∧ ValidLabeling Table.sem (pairFlip ((r.take n).flip f) o e))).map
        fun e => (o, e)

/-- The exit scan reads precisely actual ports and the feasible two-port exchange. -/
theorem mem_exitsAt (f : OccurrenceLabeling F Bool) (w r : Walk F) (n : ℕ)
    (o e : Occurrence F) : (o, e) ∈ exitsAt f w r n ↔
    e ∈ w.edges ∧ o.var = (r.take n).finish ∧ o.1 = e.1 ∧ o ∉ (r.take n).edges ∧
      ValidLabeling Table.sem (pairFlip ((r.take n).flip f) o e) := by
  simp [exitsAt, mem_incidenceList, List.mem_flatMap, List.mem_map, List.mem_filter]

/-- Data returned by the first-exit scan; no mathematical certificate is stored in the data. -/
structure Exit (F : CSP Table ℕ) where
  /-- Number of whole original steps before the attachment. -/
  length : ℕ
  /-- Actual outside occurrence, unused in that prefix. -/
  input : Occurrence F
  /-- Actual cycle occurrence at the same original constraint. -/
  output : Occurrence F

/-- Find the first externally extendible prefix, then its first actual pair of ports. -/
@[expose] def firstExit (f : OccurrenceLabeling F Bool) (w r : Walk F) : Option (Exit F) :=
  let n := (List.range (r.steps.length + 1)).findIdx fun n => !(exitsAt f w r n).isEmpty
  if n < r.steps.length + 1 then
    match exitsAt f w r n with
    | [] => none
    | (o, e) :: _ => some ⟨n, o, e⟩
  else none

/-- The executable prefix selection succeeds when a local exit exists and proves that every
earlier prefix fails every local exit test. It scans whole steps and actual ports only. -/
theorem firstExit_spec (f : OccurrenceLabeling F Bool) (w r : Walk F)
    (hex : ∃ n ≤ r.steps.length, exitsAt f w r n ≠ []) :
    ∃ ex, firstExit f w r = some ex ∧ ex.length ≤ r.steps.length ∧
      (ex.input, ex.output) ∈ exitsAt f w r ex.length ∧
      ∀ n < ex.length, exitsAt f w r n = [] := by
  let pred := fun n => !(exitsAt f w r n).isEmpty
  let ns := List.range (r.steps.length + 1)
  let n := ns.findIdx pred
  have hlt : n < ns.length := List.findIdx_lt_length.mpr (by
    obtain ⟨k, hk, he⟩ := hex
    exact ⟨k, List.mem_range.mpr (by omega), by simpa [pred] using he⟩)
  have hn : n ≤ r.steps.length := by simpa [ns] using hlt
  have hyes : exitsAt f w r n ≠ [] := by
    have hh := List.findIdx_getElem (p := pred) (xs := ns) (w := hlt)
    simpa [ns, pred] using hh
  have hno : ∀ k < n, exitsAt f w r k = [] := by
    intro k hk
    have hh := List.not_of_lt_findIdx (p := pred) (xs := ns) hk
    simpa [ns, pred] using hh
  cases he : exitsAt f w r n with
  | nil => exact (hyes he).elim
  | cons p ps =>
    rcases p with ⟨o, e⟩
    refine ⟨⟨n, o, e⟩, ?_, hn, by rw [he]; exact List.mem_cons_self, hno⟩
    simp only [firstExit]
    change (if n < r.steps.length + 1 then
      match exitsAt f w r n with
      | [] => none
      | (o, e) :: _ => some (⟨n, o, e⟩ : Exit F)
      else none) = some (⟨n, o, e⟩ : Exit F)
    simp only [show n < r.steps.length + 1 by omega, ↓reduceIte, he]

private theorem snoc_exchange {f : OccurrenceLabeling F Bool} {p : Walk F}
    {o e : Occurrence F} (h : (p.snoc o e).IsFWalk Table.sem f) :
    o ∉ p.edges ∧ ValidLabeling Table.sem (pairFlip (p.flip f) o e) := by
  have hn := h.1.1.2
  change (Walk.edgesOf (p.steps ++ [(o, e)])).Nodup at hn
  rw [Walk.edgesOf_append] at hn
  change (p.edges ++ [o, e]).Nodup at hn
  have hsplit := List.nodup_append.mp hn
  have hno : o ∉ p.edges := fun ho => hsplit.2.2 _ ho _ (by simp) rfl
  have hoe : o ≠ e := by simpa using (List.nodup_cons.mp hsplit.2.1).1
  have hp : p.edges.Nodup := hsplit.1
  have hv := (Walk.prefixValid_iff_forall_take.mp h.1.2.2) (p.snoc o e).steps.length le_rfl
  simp only [List.take_length] at hv
  change ValidLabeling Table.sem (Walk.flipSteps f (p.steps ++ [(o, e)])) at hv
  rw [Walk.flipSteps_append, Walk.flipSteps, Walk.flipSteps,
    Walk.flipSteps_eq_flipOn f p.steps hp, ← pairFlip_eq _ hoe] at hv
  exact ⟨hno, hv⟩

/-- The first local exit proves the exact no-earlier-extension hypothesis of Lemma 43.
An f-walk extension passes the local scan, so minimality forbids every such extension. -/
theorem firstExit_no_extension (f : OccurrenceLabeling F Bool) (w r : Walk F)
    {k : ℕ} (hk : k ≤ r.steps.length) (hno : ∀ n < k, exitsAt f w r n = []) :
    ∀ n < (r.take k).steps.length, ∀ e ∈ w.edges, ∀ o : Occurrence F,
      o.var = ((r.take k).take n).finish → o.1 = e.1 →
        ¬ (((r.take k).take n).snoc o e).IsFWalk Table.sem f := by
  intro n hn e he o hov hoc hfw
  have hn' : n < k := by simpa [Walk.take, List.length_take, Nat.min_eq_left hk] using hn
  have htake : (r.take k).take n = r.take n := by
    simp [Walk.take, List.take_take, Nat.min_eq_left (Nat.le_of_lt hn')]
  rw [htake] at hov hfw
  obtain ⟨hunused, hv⟩ := snoc_exchange hfw
  have hm := (mem_exitsAt f w r n o e).mpr ⟨he, hov, hoc, hunused, hv⟩
  simp only [hno n hn', List.not_mem_nil] at hm

/-- Execute the shortest outside prefix and the valid original blossom arm selected after it. -/
@[expose] def liftPrefix (f : OccurrenceLabeling F Bool) (w r : Walk F) :
    Option (OccurrenceLabeling F Bool) := do
  let ex ← firstExit f w r
  let current := (r.take ex.length).flip f
  let arm ← attachmentWalk current w ex.input
  return arm.flip current

/-- Constructive difficult-case lifting in Lemma 44: an outside trail from an old defect,
with any feasible local exit into the blossom, yields an actual valid labeling removing two
old defects. Outside changes are performed before the arm scan and are fully accounted for. -/
theorem liftPrefix_spec (hF : EdgeInstance F) {f : OccurrenceLabeling F Bool}
    (hb : w.IsBlossom Table.sem f) (hM : EdgeInstance.EvenConstraints Table.sem F)
    {r : Walk F} (hr : r.IsFPrefix Table.sem f) (hend : r.steps = [] ∨ r.start ≠ r.finish)
    (hroot : Inconsistent f r.start) (hstart : r.start ∉ internal w)
    (hvars : ∀ o ∈ r.edges, o.var ∉ internal w)
    (hex : ∃ n ≤ r.steps.length, exitsAt f w r n ≠ []) :
    ∃ g, liftPrefix f w r = some g ∧ ValidLabeling Table.sem g ∧
      (defects g).card + 2 = (defects f).card := by
  obtain ⟨ex, hexit, hk, hports, hno⟩ := firstExit_spec f w r hex
  obtain ⟨he, hov, hoc, _, hv⟩ := (mem_exitsAt f w r ex.length ex.input ex.output).mp hports
  let q := r.take ex.length
  have hq : q.IsFPrefix Table.sem f := hr.take ex.length
  have hqvars : ∀ o ∈ q.edges, o.var ∉ internal w := by
    intro o ho
    exact hvars o ((List.take_sublist ex.length r.steps).flatMap
      (fun s => [s.1, s.2]) |>.subset ho)
  have hB : w.IsBlossom Table.sem (q.flip f) := by
    by_cases hk0 : ex.length = 0
    · simpa only [q, hk0, Walk.take, List.take_zero, Walk.flip, Walk.edges, Walk.edgesOf,
        List.flatMap_nil, List.toFinset_nil, BitString.flipOn_empty] using hb
    · have hqends : q.start ≠ q.finish := by
        by_cases heq : ex.length = r.steps.length
        · have he : q = r := by simp [q, heq, Walk.take]
          rw [he]
          exact hend.resolve_left (fun hn => by simp [hn] at hk; omega)
        · have hcons := hr.not_inconsistent_finish_take (n := ex.length) (by omega) (by omega)
          exact fun he => hcons (he ▸ hroot)
      exact blossom_after_prefix hb hM ⟨hq, hqends⟩ hstart hqvars
        (firstExit_no_extension f w r hk hno)
  have hx : ex.input.var ∉ internal w := by
    rw [hov]
    by_cases hqn : q.steps = []
    · have heq : q.finish = r.start := by
        change Walk.finishFrom r.start q.steps = r.start
        rw [hqn]
        rfl
      exact heq ▸ hstart
    · obtain ⟨s, hs, heq⟩ := Walk.finish_step q hqn
      exact heq ▸ hqvars s.2 (List.mem_flatMap.mpr ⟨s, hs, by simp⟩)
  obtain ⟨p, hp, _, hpw, hps, hpf, hpv⟩ := attachmentWalk_spec hB hM ex.input hx
    ⟨ex.output, he, hoc, hv⟩
  have hne : w.start ≠ r.start := by
    intro he
    exact hstart (he ▸ List.mem_dedup.mpr (hb.1.start_mem_vars hb.2.2.1))
  have hbasemem : w.start ∈ (defects f).erase r.start :=
    mem_erase.mpr ⟨hne, mem_defects.mpr hb.2.2.2.1⟩
  refine ⟨p.flip (q.flip f), ?_, hpv, ?_⟩
  · simp only [liftPrefix, hexit, Option.bind_eq_bind, Option.bind_some]
    change (attachmentWalk (q.flip f) w ex.input).bind
      (fun arm => some (arm.flip (q.flip f))) = _
    rw [hp]
    rfl
  · have hd : defects (p.flip (q.flip f)) = ((defects f).erase r.start).erase w.start := by
      rw [hpw.defects_flip hF, hr.1.take ex.length |>.defects_flip hF, hps, hpf, hov]
      change defects f ∆ {r.start} ∆ {q.finish} ∆ {w.start} ∆ {q.finish} = _
      rw [symmDiff_right_comm (defects f ∆ {r.start} ∆ {q.finish})
        {w.start} {q.finish}, symmDiff_symmDiff_cancel_right,
        symmDiff_singleton_eq (defects f) r.start, ite_eq_left (mem_defects.mpr hroot),
        symmDiff_singleton_eq, ite_eq_left hbasemem]
    rw [hd]
    have ha := Finset.card_erase_add_one (mem_defects.mpr hroot)
    have hb0 := Finset.card_erase_add_one hbasemem
    omega

end Cslib.Logic.PL.CSP.Blossom
