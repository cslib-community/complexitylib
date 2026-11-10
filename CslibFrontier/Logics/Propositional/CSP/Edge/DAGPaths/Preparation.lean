/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Edge.Walk.Subpath

/-!
# Preparing a later f-DAG by an earlier directed path

The earlier-copy surgery in Lemma 35 of [KazdaKolmogorovRolinek2018], arXiv v6,
printed pp. 16–17, transfers validity, feasibility, and no shortcuts to a supported
subgraph whose copied constraints all have later timestamps. This form permits unused
earlier branches to be discarded while preparing a blossom root path.
-/

public section

namespace Cslib.Logic.PL.CSP.DAG

variable {Rel V : Type*} {F : CSP Rel V}

/-- An incidence already used at an earlier timestamp cannot occur on a later directed
path, by the ambient DAG's original-incidence uniqueness condition. -/
theorem DirectedPath.occurrence_not_mem_of_earlier {sem : Rel → List Bool → Bool}
    {f : OccurrenceLabeling F Bool} {T : DAG F} {w : Walk F} {time : Occurrence F → ℕ}
    (hp : DirectedPath T w time) (h : T.IsFDAG sem f) {a : Arc F} (ha : a ∈ T.arcs)
    (ht : ∀ s ∈ w.steps, a.time < time s.1) : a.occurrence ∉ w.edges := by
  intro ho
  obtain ⟨s, hs, ho⟩ := List.mem_flatMap.mp ho
  rcases (show a.occurrence = s.1 ∨ a.occurrence = s.2 by simpa using ho) with ho | ho
  · have hh := congrArg Arc.time (h.unique a ha (inArc time s) (hp.incoming s hs) ho)
    have hl := ht s hs
    change a.time = time s.1 at hh
    omega
  · have hh := congrArg Arc.time (h.unique a ha (outArc time s) (hp.outgoing s hs) ho)
    have hl := ht s hs
    change a.time = time s.1 at hh
    omega

/-- Along a directed path, every output variable lies strictly after the starting root
in any topological ranking of the ambient graph. -/
theorem DirectedPath.rank_lt_output {T : DAG F} {w : Walk F} {time : Occurrence F → ℕ}
    (hp : DirectedPath T w time) (hsup : T.Supported) {rank : Node F → ℕ}
    (hr : ∀ x y, T.edge x y → rank x < rank y)
    {s : Occurrence F × Occurrence F} (hs : s ∈ w.steps) :
    rank (.inl w.start) < rank (.inl s.2.var) := by
  rcases w with ⟨v, ss⟩
  induction ss generalizing v with
  | nil => simp at hs
  | cons t ss ih =>
    have hin : rank (.inl t.1.var) < rank (.inr (t.1.1, time t.1)) :=
      hr _ _ ⟨inArc time t, hp.incoming t List.mem_cons_self, rfl, rfl⟩
    have hout : rank (.inr (t.2.1, time t.1)) < rank (.inl t.2.var) :=
      hr _ _ ⟨outArc time t, hp.outgoing t List.mem_cons_self, rfl, rfl⟩
    have hstart := hp.walk.1.1
    have hcopy := hp.walk.1.2.1
    have hfirst : rank (.inl v) < rank (.inl t.2.var) := by
      rw [hstart, hcopy] at hin
      exact hin.trans hout
    rcases List.mem_cons.mp hs with rfl | hs
    · exact hfirst
    · have htail : DirectedPath T (⟨t.2.var, ss⟩ : Walk F) time := by
        refine ⟨⟨hp.walk.1.2.2, ?_⟩, ?_, ?_, ?_, ?_⟩
        · have hn := hp.walk.2
          change (t.1 :: t.2 :: Walk.edgesOf ss).Nodup at hn
          exact (List.nodup_cons.mp (List.nodup_cons.mp hn).2).2
        · exact (hsup _ (hp.outgoing t List.mem_cons_self)).1
        · intro s hs; exact hp.incoming s (List.mem_cons_of_mem t hs)
        · intro s hs; exact hp.outgoing s (List.mem_cons_of_mem t hs)
        · intro s hs u hu; exact hp.copies_injective s (List.mem_cons_of_mem t hs)
            u (List.mem_cons_of_mem t hu)
      exact hfirst.trans (ih t.2.var htail hs)

/-- A nonempty directed path in an f-DAG cannot return to its starting variable. -/
theorem DirectedPath.finish_ne_start {sem : Rel → List Bool → Bool}
    {f : OccurrenceLabeling F Bool} {T : DAG F} {w : Walk F} {time : Occurrence F → ℕ}
    (hp : DirectedPath T w time) (h : T.IsFDAG sem f) (hne : w.steps ≠ []) :
    w.finish ≠ w.start := by
  obtain ⟨rank, hr⟩ := h.ordered.2
  have hout : ∀ s ∈ w.steps, rank (.inl w.start) < rank (.inl s.2.var) :=
    fun _ hs => hp.rank_lt_output h.supported (fun x y he => hr x y (Or.inl he)) hs
  rcases w with ⟨v, ss⟩
  induction ss using List.reverseRecOn with
  | nil => exact False.elim (hne rfl)
  | append_singleton ss s ih =>
    have hh := hout s (List.mem_append_right _ (List.mem_singleton_self _))
    intro he
    have hv : s.2.var = v := by
      simpa only [Walk.finish, Walk.finishFrom_append, Walk.finishFrom] using he
    rw [hv] at hh
    exact Nat.lt_irrefl _ hh

/-- In the arc graph of a nonempty directed path, the first incoming incidence is the only
arc incident with its starting variable. This is the leaf condition used in root surgery. -/
theorem DirectedPath.start_arc_eq {sem : Rel → List Bool → Bool}
    {f : OccurrenceLabeling F Bool} {T : DAG F} {w : Walk F} {time : Occurrence F → ℕ}
    (hp : DirectedPath T w time) (h : T.IsFDAG sem f)
    {first : Occurrence F × Occurrence F} {tail : List (Occurrence F × Occurrence F)}
    (he : w.steps = first :: tail) {a : Arc F} (ha : a ∈ pathArcs w time)
    (hv : a.occurrence.var = w.start) : a = inArc time first := by
  obtain ⟨rank, hr⟩ := h.ordered.2
  have hout : ∀ s ∈ w.steps, s.2.var ≠ w.start := by
    intro s hs hv
    have hh := hp.rank_lt_output h.supported (fun x y he => hr x y (Or.inl he)) hs
    rw [hv] at hh
    exact Nat.lt_irrefl _ hh
  have htail : Walk.Linked first.2.var tail := by
    have hl := hp.walk.1
    rw [he] at hl
    exact hl.2.2
  have hinputs : ∀ (ss : List (Occurrence F × Occurrence F)) (v : V),
      Walk.Linked v ss → v ≠ w.start → (∀ s ∈ ss, s.2.var ≠ w.start) →
      ∀ s ∈ ss, s.1.var ≠ w.start := by
    intro ss
    induction ss with
    | nil => simp
    | cons t ss ih =>
      intro v hl hv ho s hs
      rcases List.mem_cons.mp hs with rfl | hs
      · exact fun he => hv (hl.1.symm.trans he)
      · exact ih _ hl.2.2 (ho t List.mem_cons_self)
          (fun u hu => ho u (List.mem_cons_of_mem _ hu)) s hs
  have hni := hinputs tail first.2.var htail (hout first (he ▸ List.mem_cons_self))
    (fun s hs => hout s (he ▸ List.mem_cons_of_mem _ hs))
  obtain ⟨s, hs, ha⟩ := Finset.mem_biUnion.mp ha
  have hsm := List.mem_toFinset.mp hs
  rcases (show a = inArc time s ∨ a = outArc time s by simpa using ha) with rfl | rfl
  · rw [he] at hsm
    rcases List.mem_cons.mp hsm with rfl | hs
    · rfl
    · exact False.elim (hni s hs hv)
  · exact False.elim (hout s hsm hv)

/-- Flipping an earlier pair preserves all six f-DAG conditions on any supported later
subgraph. This is a deletion form of Lemma 35, retaining isolated supported nodes. -/
theorem IsFDAG.flip_later_subgraph {sem : Rel → List Bool → Bool}
    {f : OccurrenceLabeling F Bool} {S T : DAG F} (h : T.IsFDAG sem f)
    (hM : EdgeInstance.EvenConstraints sem F) {a b : Arc F}
    (ha : a ∈ T.arcs) (hb : b ∈ T.arcs) (hai : a.incoming = true)
    (hbo : b.incoming = false) (hc : a.copy = b.copy)
    (hst : S.Subgraph T) (hs : S.Supported)
    (hl : ∀ c ∈ S.copies, a.time < c.2) :
    S.IsFDAG sem (pairFlip f a.occurrence b.occurrence) := by
  have hh := h.subgraph hst hs
  have hne := h.occurrence_ne_of_orientation_ne ha hb (by simp [hai, hbo])
  refine ⟨h.feasible a ha b hb hai hc, hs, hh.unique, hh.indegree, hh.ordered, ?_, ?_⟩
  · intro x hx y hy hxi hxy
    exact h.feasible_after_earlier hM ha hb (hst.2.2 hx) (hst.2.2 hy) hai hne hc hxi hxy
      (hl x.copy (hs x hx).2)
  · intro x hx y hy hxi hxy ht
    exact h.noShortcut_after_earlier hM ha hb (hst.2.2 hx) (hst.2.2 hy) hai hne hc hxi hxy
      (hl x.copy (hs x hx).2) ht

/-- Flipping a chronological directed path preserves the full f-DAG invariant on any
supported subgraph strictly later than every step of the path. Original constraints may
repeat; strict chronology concerns copied constraints. -/
theorem DirectedPath.flip_later_subgraph {sem : Rel → List Bool → Bool}
    {f : OccurrenceLabeling F Bool} {S T : DAG F} {w : Walk F}
    {time : Occurrence F → ℕ} (hp : DirectedPath T w time) (h : T.IsFDAG sem f)
    (hM : EdgeInstance.EvenConstraints sem F)
    (ho : w.steps.Pairwise (fun s t => time s.1 < time t.1))
    (hst : S.Subgraph T) (hs : S.Supported)
    (hl : ∀ c ∈ S.copies, ∀ s ∈ w.steps, time s.1 < c.2) :
    S.IsFDAG sem (w.flip f) := by
  classical
  rcases w with ⟨v, ss⟩
  induction ss using List.reverseRecOn generalizing S with
  | nil =>
    simpa [Walk.flip, Walk.edges, Walk.edgesOf] using h.subgraph hst hs
  | append_singleton ss s ih =>
    have hinit : DirectedPath T (⟨v, ss⟩ : Walk F) time := by
      simpa only [Walk.take, List.take_append_length] using hp.take ss.length
    have ho' := List.pairwise_append.mp ho
    have hlinked := hp.walk.1
    rw [Walk.linked_append_iff] at hlinked
    have hc : (inArc time s).copy = (outArc time s).copy := Prod.ext hlinked.2.2.1 rfl
    have hm : s ∈ ss ++ [s] := List.mem_append_right _ (List.mem_singleton_self _)
    have ha := hp.incoming s hm
    have hb := hp.outgoing s hm
    have hterm : (terminalPair (inArc time s) (outArc time s)).Supported := by
      intro a ha'
      rcases (show a = inArc time s ∨ a = outArc time s by
        simpa only [terminalPair, Finset.mem_insert, Finset.mem_singleton] using ha') with rfl | rfl
      · exact ⟨by simp [terminalPair], Finset.mem_singleton_self _⟩
      · exact ⟨by simp [terminalPair], Finset.mem_singleton.mpr hc.symm⟩
    have hsub : (terminalPair (inArc time s) (outArc time s)).Subgraph T := by
      refine ⟨?_, ?_, ?_⟩
      · intro u hu
        rcases (show u = s.1.var ∨ u = s.2.var by
          simpa [terminalPair, inArc, outArc] using hu) with rfl | rfl
        · exact (h.supported _ ha).1
        · exact (h.supported _ hb).1
      · intro c hc'
        have he := Finset.mem_singleton.mp hc'
        exact he ▸ (h.supported _ ha).2
      · intro a ha'
        rcases (show a = inArc time s ∨ a = outArc time s by
          simpa only [terminalPair, Finset.mem_insert, Finset.mem_singleton] using ha') with
          rfl | rfl
        · exact ha
        · exact hb
    let U := S.union (terminalPair (inArc time s) (outArc time s))
    have hu : U.IsFDAG sem ((⟨v, ss⟩ : Walk F).flip f) := by
      apply ih (hst.union hsub) (hs.union hterm) hinit ho'.1
      intro c hc' t ht
      rcases Finset.mem_union.mp hc' with hc' | hc'
      · exact hl c hc' t (List.mem_append_left _ ht)
      · have he := Finset.mem_singleton.mp hc'
        rw [he]
        exact ho'.2.2 t ht s (List.mem_singleton_self _)
    have hsu : S.Subgraph U :=
      ⟨Finset.subset_union_left, Finset.subset_union_left, Finset.subset_union_left⟩
    have hv := hu.flip_later_subgraph hM
      (a := inArc time s) (b := outArc time s)
      (Finset.mem_union_right _ (by simp [terminalPair]))
      (Finset.mem_union_right _ (by simp [terminalPair])) rfl rfl hc hsu hs
      (fun c hc' => hl c hc' s hm)
    have hnodup := hp.walk.2
    change (Walk.edgesOf (ss ++ [s])).Nodup at hnodup
    rw [Walk.edgesOf_append] at hnodup
    have hn := List.nodup_append.mp hnodup
    have hne : s.1 ≠ s.2 := by
      have hh := hn.2.1
      simpa [Walk.edgesOf] using hh
    have hno : s.1 ∉ (⟨v, ss⟩ : Walk F).edges := by
      intro hx
      exact hn.2.2 s.1 hx s.1 (by simp [Walk.edgesOf]) rfl
    have hnp : s.2 ∉ (⟨v, ss⟩ : Walk F).edges := by
      intro hx
      exact hn.2.2 s.2 hx s.2 (by simp [Walk.edgesOf]) rfl
    have he := Walk.flip_snoc (⟨v, ss⟩ : Walk F) f s.1 s.2 hinit.walk hno hnp hne
    change S.IsFDAG sem (pairFlip ((⟨v, ss⟩ : Walk F).flip f) s.1 s.2) at hv
    rw [pairFlip_eq _ hne] at hv
    rwa [← he] at hv

end Cslib.Logic.PL.CSP.DAG
