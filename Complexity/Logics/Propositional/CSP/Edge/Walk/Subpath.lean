/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CSP.Edge.DAGPaths
public import Complexity.Logics.Propositional.CSP.Edge.Walk.Operations

/-!
# Variable-ended subpaths of directed incidence trails

Dropping whole steps starts at the actual endpoint of the removed prefix. Directed paths
inherit their ambient DAG certificate on suffixes, so Corollary 36 applies to suffixes without
assuming that reversal preserves arbitrary f-walk validity.
-/

public section

namespace Cslib.Logic.PL.CSP

variable {Rel V : Type*} {F : CSP Rel V}

namespace Walk

/-- Append one linked step at two distinct unused incidences. -/
theorem IsWalk.snoc {w : Walk F} (hw : w.IsWalk) {o p : Occurrence F}
    (ho : o.var = w.finish) (hc : o.1 = p.1) (hne : o ≠ p)
    (hno : o ∉ w.edges) (hnp : p ∉ w.edges) : (w.snoc o p).IsWalk :=
  ⟨hw.1.snoc ho hc, nodup_edges_snoc w o p hw.2 hno hnp hne⟩

/-- Reversing a linked walk preserves consistency of its internal variables. This says
nothing about prefix validity, which need not survive reversal. -/
theorem InternallyConsistent.reverse {v : V} {ss : List (Occurrence F × Occurrence F)}
    {f : OccurrenceLabeling F Bool} (hl : Linked v ss) (hc : InternallyConsistent f ss) :
    InternallyConsistent f (ss.reverse.map Prod.swap) := by
  induction ss generalizing v with
  | nil => trivial
  | cons s ss ih =>
    rcases s with ⟨o, p⟩
    rw [List.reverse_cons, List.map_append]
    apply (ih hl.2.2 hc.2).snoc (finishFrom p.var ss) p o
    rcases hc.1 with he | he
    · subst ss
      exact Or.inl rfl
    · apply Or.inr
      rw [hl.2.2.finishFrom_reverse]
      exact he

/-- Remove the first `n` steps, starting at the endpoint of that prefix. -/
@[expose] def drop (w : Walk F) (n : ℕ) : Walk F :=
  ⟨(w.take n).finish, w.steps.drop n⟩

/-- A suffix of a linked incidence trail remains a linked incidence trail. -/
theorem IsWalk.drop {w : Walk F} (hw : w.IsWalk) (n : ℕ) : (w.drop n).IsWalk := by
  refine ⟨?_, ((List.drop_sublist n w.steps).flatMap fun (o, p) => [o, p]).nodup hw.2⟩
  exact ((linked_append_iff w.start (w.steps.take n) (w.steps.drop n)).mp
    (by simpa only [List.take_append_drop] using hw.1)).2

/-- The prefix and suffix recover the exact candidate steps and starting variable. -/
@[simp] theorem take_append_drop (w : Walk F) (n : ℕ) :
    (w.take n).append (w.drop n) = w := by
  cases w
  simp [take, drop, append]

/-- Removing a prefix does not change the final variable. -/
@[simp] theorem finish_drop (w : Walk F) (n : ℕ) : (w.drop n).finish = w.finish := by
  change finishFrom (finishFrom w.start (w.steps.take n)) (w.steps.drop n) = _
  rw [← finishFrom_append, List.take_append_drop]
  rfl

/-- A nonempty candidate ends at the output variable of one of its actual steps. -/
theorem finish_step (w : Walk F) (hne : w.steps ≠ []) :
    ∃ s ∈ w.steps, s.2.var = w.finish := by
  rcases w with ⟨v, ss⟩
  induction ss using List.reverseRecOn with
  | nil => exact False.elim (hne rfl)
  | append_singleton ss s ih =>
    exact ⟨s, List.mem_append_right _ (List.mem_singleton_self _), by
      simp only [finish, finishFrom_append, finishFrom]⟩

/-- The prefix through a selected step ends at that step's output variable. -/
theorem finish_take_succ (w : Walk F) {k : ℕ} (hk : k < w.steps.length) :
    (w.take (k + 1)).finish = w.steps[k].2.var := by
  change finishFrom w.start (w.steps.take (k + 1)) = _
  rw [List.take_succ_eq_append_getElem hk, finishFrom_append]
  rfl

/-- Extending a trail prefix by its next actual step performs exactly the corresponding
two-port move, with cancellation handled by `DAG.pairFlip`. -/
theorem IsWalk.flip_take_succ {w : Walk F} (hw : w.IsWalk)
    (f : OccurrenceLabeling F Bool) {k : ℕ} (hk : k < w.steps.length) :
    (w.take (k + 1)).flip f =
      DAG.pairFlip ((w.take k).flip f) w.steps[k].1 w.steps[k].2 := by
  have hn := (hw.take (k + 1)).2
  change (edgesOf (w.steps.take (k + 1))).Nodup at hn
  rw [List.take_succ_eq_append_getElem hk, edgesOf_append] at hn
  have hp := List.nodup_append.mp hn
  have hne : w.steps[k].1 ≠ w.steps[k].2 := by simpa [edgesOf] using hp.2.1
  have hno : w.steps[k].1 ∉ (w.take k).edges := by
    intro hm
    exact hp.2.2 _ hm _ (by simp [edgesOf]) rfl
  have hnp : w.steps[k].2 ∉ (w.take k).edges := by
    intro hm
    exact hp.2.2 _ hm _ (by simp [edgesOf]) rfl
  have he : w.take (k + 1) = (w.take k).snoc w.steps[k].1 w.steps[k].2 := by
    apply congrArg (Walk.mk w.start)
    exact List.take_succ_eq_append_getElem hk
  rw [he, flip_snoc _ f _ _ (hw.take k) hno hnp hne, DAG.pairFlip_eq _ hne]

/-- Join two disjoint trails at a fresh constraint step, traversing the second trail in
reverse. Prefix validity is a separate theorem about directed DAG paths. -/
theorem IsWalk.join_meeting {w z : Walk F} (hw : w.IsWalk) (hz : z.IsWalk)
    {a b : Occurrence F} (ha : a.var = w.finish) (hb : b.var = z.finish)
    (hc : a.1 = b.1) (hne : a ≠ b) (hd : List.Disjoint w.edges z.edges)
    (haw : a ∉ w.edges) (hbw : b ∉ w.edges) (haz : a ∉ z.edges) (hbz : b ∉ z.edges) :
    ((w.snoc a b).append z.reverse).IsWalk := by
  apply (hw.snoc ha hc hne haw hbw).append hz.reverse
  · rw [finish_snoc]
    exact hb
  · intro o ho hz'
    rw [edges_reverse, List.mem_reverse] at hz'
    change o ∈ edgesOf (w.steps ++ [(a, b)]) at ho
    rw [edgesOf_append] at ho
    rcases List.mem_append.mp ho with ho | ho
    · exact hd ho hz'
    · rcases (show o = a ∨ o = b by simpa [edgesOf] using ho) with rfl | rfl
      · exact haz hz'
      · exact hbz hz'

/-- Joining at the second trail's endpoint and reading it backward ends at its start. -/
theorem finish_join_meeting (w z : Walk F) (a b : Occurrence F)
    (hz : Linked z.start z.steps) (hb : b.var = z.finish) :
    ((w.snoc a b).append z.reverse).finish = z.start := by
  simp only [append, snoc, reverse, finish, finishFrom_append, finishFrom]
  rw [hb]
  exact hz.finishFrom_reverse

end Walk

namespace DAG

/-- A directed path remains directed in a larger incidence graph. -/
theorem DirectedPath.mono {S T : DAG F} {w : Walk F} {time : Occurrence F → ℕ}
    (hp : DirectedPath S w time) (hst : S.Subgraph T) : DirectedPath T w time where
  walk := hp.walk
  start_mem := hst.1 hp.start_mem
  incoming s hs := hst.2.2 (hp.incoming s hs)
  outgoing s hs := hst.2.2 (hp.outgoing s hs)
  copies_injective := hp.copies_injective

/-- Copied constraints of a directed path are exactly the copied nodes of its steps. -/
theorem DirectedPath.mem_copies [DecidableEq V] {T : DAG F} {w : Walk F}
    {time : Occurrence F → ℕ}
    (hp : DirectedPath T w time) {c : Copy F} :
    c ∈ (pathDAG w time).copies ↔ ∃ s ∈ w.steps, (inArc time s).copy = c := by
  classical
  have hcopy : ∀ s ∈ w.steps, (outArc time s).copy = (inArc time s).copy := by
    intro s hs
    obtain ⟨ss, ts, he⟩ := List.mem_iff_append.mp hs
    have hl := hp.walk.1
    rw [he, Walk.linked_append_iff] at hl
    exact Prod.ext hl.2.2.1.symm rfl
  simp only [pathDAG, pathArcs, Finset.mem_image, Finset.mem_biUnion, List.mem_toFinset,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨a, ⟨s, hs, rfl | rfl⟩, rfl⟩
    · exact ⟨s, hs, rfl⟩
    · exact ⟨s, hs, (hcopy s hs).symm⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨inArc time s, ⟨s, hs, Or.inl rfl⟩, rfl⟩

/-- Both endpoints of a directed path belong to its ambient graph's variable support. -/
theorem DirectedPath.finish_mem {T : DAG F} {w : Walk F} {time : Occurrence F → ℕ}
    (hp : DirectedPath T w time) (hs : T.Supported) : w.finish ∈ T.vars := by
  rcases w with ⟨v, ss⟩
  induction ss using List.reverseRecOn with
  | nil => exact hp.start_mem
  | append_singleton ss s ih =>
    have hm : s ∈ ss ++ [s] := List.mem_append_right _ (List.mem_singleton_self _)
    have hv := (hs _ (hp.outgoing s hm)).1
    simpa only [outArc, Walk.finish, Walk.finishFrom_append, Walk.finishFrom] using hv

/-- A suffix is a directed path in the same ambient graph, at the original timestamps. -/
theorem DirectedPath.drop {T : DAG F} {w : Walk F} {time : Occurrence F → ℕ}
    (hp : DirectedPath T w time) (hs : T.Supported) (n : ℕ) :
    DirectedPath T (w.drop n) time where
  walk := hp.walk.drop n
  start_mem := (hp.take n).finish_mem hs
  incoming s hm := hp.incoming s (List.mem_of_mem_drop hm)
  outgoing s hm := hp.outgoing s (List.mem_of_mem_drop hm)
  copies_injective s hm t hn :=
    hp.copies_injective s (List.mem_of_mem_drop hm) t (List.mem_of_mem_drop hn)

/-- Copied-node disjointness of paths in an f-DAG implies disjointness of their actual
incidence lists, by the original-incidence uniqueness condition. -/
theorem DirectedPath.disjoint_edges [DecidableEq V] {sem : Rel → List Bool → Bool}
    {f : OccurrenceLabeling F Bool} {T : DAG F} {w z : Walk F}
    {timeW timeZ : Occurrence F → ℕ} (hw : DirectedPath T w timeW)
    (hz : DirectedPath T z timeZ) (h : T.IsFDAG sem f)
    (hd : Disjoint (pathDAG w timeW).copies (pathDAG z timeZ).copies) :
    List.Disjoint w.edges z.edges := by
  have lift : ∀ (q : Walk F) (time : Occurrence F → ℕ) (o : Occurrence F),
      o ∈ q.edges → ∃ a ∈ pathArcs q time, a.occurrence = o := by
    intro q time o ho
    obtain ⟨s, hs, ho⟩ := List.mem_flatMap.mp ho
    rcases (show o = s.1 ∨ o = s.2 by simpa using ho) with rfl | rfl
    · exact ⟨inArc time s, Finset.mem_biUnion.mpr
        ⟨s, List.mem_toFinset.mpr hs, by simp⟩, rfl⟩
    · exact ⟨outArc time s, Finset.mem_biUnion.mpr
        ⟨s, List.mem_toFinset.mpr hs, by simp⟩, rfl⟩
  intro o ho hp
  obtain ⟨a, ha, he⟩ := lift w timeW o ho
  obtain ⟨b, hb, hf⟩ := lift z timeZ o hp
  have hab := h.unique a ((hw.subgraph h.supported).2.2 ha)
    b ((hz.subgraph h.supported).2.2 hb) (he.trans hf.symm)
  exact Finset.disjoint_left.mp hd ((pathDAG_supported w timeW) a ha).2
    (hab ▸ ((pathDAG_supported z timeZ) b hb).2)

/-- The graph flip at two meeting paths equals the flip of their joined positional walk.
This identity alone does not assert validity of any prefix. -/
theorem meeting_flip_eq [DecidableEq V] (w z : Walk F)
    (timeW timeZ : Occurrence F → ℕ) (a b : Arc F) (f : OccurrenceLabeling F Bool) :
    ((((pathDAG w timeW).union (pathDAG z timeZ)).union (terminalPair a b)).flip f) =
      ((w.snoc a.occurrence b.occurrence).append z.reverse).flip f := by
  have image_path : ∀ (q : Walk F) (time : Occurrence F → ℕ),
      (pathArcs q time).image Arc.occurrence = q.edges.toFinset := by
    intro q time
    ext o
    simp only [pathArcs, Finset.mem_image, Finset.mem_biUnion, List.mem_toFinset,
      Finset.mem_insert, Finset.mem_singleton, Walk.edges, Walk.edgesOf, List.mem_flatMap]
    constructor
    · rintro ⟨e, ⟨s, hs, rfl | rfl⟩, rfl⟩ <;> exact ⟨s, hs, by simp [inArc, outArc]⟩
    · rintro ⟨s, hs, ho⟩
      rcases (show o = s.1 ∨ o = s.2 by simpa using ho) with rfl | rfl
      · exact ⟨inArc time s, ⟨s, hs, Or.inl rfl⟩, rfl⟩
      · exact ⟨outArc time s, ⟨s, hs, Or.inr rfl⟩, rfl⟩
  unfold DAG.flip
  simp only [DAG.union, terminalPair, pathDAG, Finset.image_union, image_path,
    Finset.image_insert, Finset.image_singleton]
  apply congrArg (fun s => BitString.flipOn s f)
  rw [Walk.edges_append, Walk.edges_reverse]
  change _ = (Walk.edgesOf (w.steps ++ [(a.occurrence, b.occurrence)]) ++ z.edges.reverse).toFinset
  rw [Walk.edgesOf_append]
  simp only [List.toFinset_append, List.toFinset_reverse]
  have hsingle : (Walk.edgesOf [(a.occurrence, b.occurrence)]).toFinset =
      {a.occurrence, b.occurrence} := by simp [Walk.edgesOf]
  rw [hsingle]
  change w.edges.toFinset ∪ z.edges.toFinset ∪ {a.occurrence, b.occurrence} =
    (w.edges.toFinset ∪ {a.occurrence, b.occurrence}) ∪ z.edges.toFinset
  ext o
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  tauto

/-- Every variable-ended prefix of the walk formed by two meeting directed paths has a
valid flip. Prefixes after the meeting use suffixes of the second directed path in Corollary
36; this does not assume reversal closure of f-walks. -/
theorem DirectedPath.valid_take_meeting [DecidableEq V] {sem : Rel → List Bool → Bool}
    {f : OccurrenceLabeling F Bool} {T : DAG F} {w z : Walk F}
    {timeW timeZ : Occurrence F → ℕ} {a b : Arc F}
    (hw : DirectedPath T w timeW) (hz : DirectedPath T z timeZ)
    (h : T.IsFDAG sem f) (hM : EdgeInstance.EvenConstraints sem F)
    (ha : a ∈ T.arcs) (hb : b ∈ T.arcs) (hai : a.incoming = true)
    (hcopy : a.copy = b.copy) (hne : a ≠ b)
    (hd : Disjoint (pathDAG w timeW).copies (pathDAG z timeZ).copies)
    (hwfresh : a.copy ∉ (pathDAG w timeW).copies)
    (hzfresh : a.copy ∉ (pathDAG z timeZ).copies) (n : ℕ) :
    ValidLabeling sem ((((w.snoc a.occurrence b.occurrence).append z.reverse).take n).flip f) := by
  by_cases hn : n ≤ w.steps.length
  · have he : ((w.snoc a.occurrence b.occurrence).append z.reverse).take n = w.take n := by
      apply congrArg (Walk.mk w.start)
      simp [Walk.append, Walk.snoc, List.take_append, Nat.sub_eq_zero_of_le hn]
    rw [he]
    exact hw.valid_take h hM n
  · let k := z.steps.length - (n - (w.steps.length + 1))
    have hsub : (pathDAG (z.drop k) timeZ).copies ⊆ (pathDAG z timeZ).copies := by
      intro c hc
      obtain ⟨s, hs, he⟩ := (hz.drop h.supported k).mem_copies.mp hc
      exact hz.mem_copies.mpr ⟨s, List.mem_of_mem_drop hs, he⟩
    have hv := hw.valid_flip_meeting (hz.drop h.supported k) h hM ha hb hai hcopy hne
      (hd.mono_right hsub) hwfresh (fun hc => hzfresh (hsub hc))
    rw [meeting_flip_eq] at hv
    have hlen : (w.steps ++ [(a.occurrence, b.occurrence)]).length ≤ n := by
      simp only [List.length_append, List.length_singleton]
      omega
    have he : ((w.snoc a.occurrence b.occurrence).append z.reverse).take n =
        (w.snoc a.occurrence b.occurrence).append (z.drop k).reverse := by
      apply congrArg (Walk.mk w.start)
      change ((w.steps ++ [(a.occurrence, b.occurrence)]) ++ z.steps.reverse.map Prod.swap).take n =
        (w.steps ++ [(a.occurrence, b.occurrence)]) ++ (z.steps.drop k).reverse.map Prod.swap
      rw [List.take_append, List.take_of_length_le hlen, ← List.map_take, List.take_reverse]
      simp only [List.length_append, List.length_singleton]
      rfl
    rwa [he]

end DAG

end Cslib.Logic.PL.CSP
