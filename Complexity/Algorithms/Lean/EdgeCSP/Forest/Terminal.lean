/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.EdgeCSP.Forest.Ancestry

/-!
# Partial scans and terminal forest graphs

Lemma 34 of [KazdaKolmogorovRolinek2018], arXiv:1602.03124v6, printed pp. 15–16,
including a scan before saturation and the graph obtained by pruning every outgoing arc
of the terminal copy. Certificates below are derived from the executable scan and run.
They impose no even-delta-matroid assumption: incidence uniqueness, the old scans' saturation,
and validity of the reference labeling suffice.

## Main results

* `scan_isFDAG`: any partial feasible-partner scan preserves all six f-DAG conditions.
* `search_terminal_isFDAG`: both the actual partial forest and its terminal pruned graph
  are f-DAGs, including the isolated children retained in the variable support.
-/

public section

namespace Cslib.Logic.PL.CSP.Forest

open DAG

variable {Rel V : Type*} {F : CSP Rel V} [DecidableEq V]

namespace Log

/-- With unique discovery variables, every outgoing port identifies its actual parent.
The original constraint position, rather than the timestamp, is tested in step 4b. -/
theorem sameParent_of_mem_outgoing {es : Log F} (hn : es.children.Nodup)
    {o : Occurrence F} (ho : o ∈ es.outgoing) : es.SameParent o.var o.1 := by
  induction es with
  | nil => simp [outgoing] at ho
  | cons e es ih =>
    have hn' := List.nodup_append.mp hn
    rcases List.mem_append.mp ho with ho | ho
    · cases hfind : e.outputs.find? (fun p => p.var == o.var) with
      | none => exact False.elim (List.find?_eq_none.mp hfind o ho (by simp))
      | some p =>
        have hv : p.var = o.var := by simpa only [beq_iff_eq] using List.find?_some hfind
        have he := List.inj_on_of_nodup_map hn'.1 (List.mem_of_find?_eq_some hfind) ho hv
        subst p
        simp [SameParent, parent?, hfind]
    · have hnone : e.outputs.find? (fun p => p.var == o.var) = none := by
        apply List.find?_eq_none.mpr
        intro p hp
        have hnot : p.var ≠ o.var := fun he => hn'.2.2
          p.var (List.mem_map.mpr ⟨p, hp, rfl⟩) o.var
          (by rw [children_eq_map_outgoing]; exact List.mem_map.mpr ⟨o, ho, rfl⟩) he
        simpa only [beq_iff_eq] using hnot
      simpa only [SameParent, parent?, hnone] using ih hn'.2.1 ho


end Log

namespace Grown

variable {sem : Rel → List Bool → Bool} {f : OccurrenceLabeling F Bool}
  {rs : List V} {es : Log F}

/-- A fresh port cannot be a feasible partner of an older incoming port. Saturation of the
older scan, including step-4b skips, is the essential reason. -/
theorem not_partner_of_unused (hg : Grown sem f rs es) (hF : EdgeInstance F)
    {a : Arc F} (ha : a ∈ es.arcs) (hi : a.incoming = true)
    {b : Occurrence F} (hu : b ∉ es.used) (hc : a.occurrence.1 = b.1) :
    ¬ ValidLabeling sem (pairFlip f a.occurrence b) := by
  intro hv
  by_cases he : a.occurrence.var = b.var
  · exact hu (hF.eq_of_constraint_eq he hc ▸ (es.mem_arcs ha).1)
  · obtain ⟨c, hm, he, _, _⟩ := hg.saturated ha hi
      ((mem_partners sem f _ _).mpr ⟨hc, he, hv⟩)
    exact hu (he ▸ (es.mem_arcs hm).1)

end Grown

/-- Local facts about the current expansion before its scan is complete. In contrast to
`Grown`, no saturation condition on the current copy is asserted. -/
structure Partial (sem : Rel → List Bool → Bool) (f : OccurrenceLabeling F Bool)
    (rs : List V) (es : Log F) (e : Expansion F) : Prop where
  /-- Older scans really completed. -/
  grown : Grown sem f rs es
  /-- Step 2 chose a visited variable. -/
  visited : es.Visited rs e.input.var
  /-- Step 2 chose an unused incidence. -/
  unused : e.input ∉ es.used
  /-- Every inserted child is a new variable. -/
  fresh : ∀ o ∈ e.outputs, ¬ es.Visited rs o.var
  /-- No child was inserted twice. -/
  distinct : (e.outputs.map Occurrence.var).Nodup
  /-- Every inserted child passed the actual partner test. -/
  feasible : ∀ o ∈ e.outputs, o ∈ partners sem f e.input

namespace Partial

variable {sem : Rel → List Bool → Bool} {f : OccurrenceLabeling F Bool}
  {rs : List V} {es : Log F} {e : Expansion F}

/-- The new ports of a partial expansion are all unused in the older log. -/
theorem port_unused (h : Partial sem f rs es e) {o : Occurrence F}
    (ho : o = e.input ∨ o ∈ e.outputs) : o ∉ es.used := by
  rcases ho with rfl | ho
  · exact h.unused
  · exact Log.Grown.output_not_used h.grown h.fresh ho

private theorem arc_cases (_h : Partial sem f rs es e) {a : Arc F}
    (ha : a ∈ Log.arcs (e :: es)) :
    a ∈ es.arcs ∨ a = ⟨e.input, es.length, true⟩ ∨
      ∃ o ∈ e.outputs, a = ⟨o, es.length, false⟩ := by
  simpa only [Log.arcs, List.mem_cons, List.mem_append, List.mem_map, eq_comm,
    or_comm, or_left_comm, or_assoc] using ha

private theorem new_copy (h : Partial sem f rs es e) {a : Arc F}
    (ha : a = ⟨e.input, es.length, true⟩ ∨
      ∃ o ∈ e.outputs, a = ⟨o, es.length, false⟩) :
    a.copy = (e.input.1, es.length) := by
  rcases ha with rfl | ⟨o, ho, rfl⟩
  · rfl
  · exact Prod.ext ((mem_partners sem f _ _).mp (h.feasible o ho)).1.symm rfl

/-- Partial scans preserve uniqueness of used positional incidences. -/
theorem used_nodup (h : Partial sem f rs es e) : (Log.used (e :: es)).Nodup := by
  rw [Log.used, List.nodup_cons, List.nodup_append]
  refine ⟨?_, h.distinct.of_map _, h.grown.used_nodup, ?_⟩
  · intro ho
    rcases List.mem_append.mp ho with ho | ho
    · exact h.fresh _ ho h.visited
    · exact h.unused ho
  · intro o ho p hp he
    exact h.port_unused (Or.inr ho) (he.symm ▸ hp)

/-- Partial scans preserve unique discovery variables. -/
theorem children_nodup (h : Partial sem f rs es e) :
    (Log.children (e :: es)).Nodup := by
  rw [Log.children, List.nodup_append]
  refine ⟨h.distinct, h.grown.children_nodup, ?_⟩
  intro v hv w hw he
  obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hv
  exact h.fresh o ho (Or.inr (he.symm ▸ hw))

private theorem unique (h : Partial sem f rs es e) {a b : Arc F}
    (ha : a ∈ Log.arcs (e :: es)) (hb : b ∈ Log.arcs (e :: es))
    (he : a.occurrence = b.occurrence) : a = b := by
  have hn := h.used_nodup
  rw [← Log.map_arcs_occurrence] at hn
  exact List.inj_on_of_nodup_map hn ha hb he

private theorem rank_arc (h : Partial sem f rs es e) {a : Arc F}
    (ha : a ∈ Log.arcs (e :: es)) :
    if a.incoming then Log.birth (e :: es) a.occurrence.var < 2 * a.time + 1
    else 2 * a.time + 1 < Log.birth (e :: es) a.occurrence.var := by
  have hold : ∀ v, es.Visited rs v → Log.birth (e :: es) v = es.birth v := by
    intro v hv
    have hn : v ∉ e.outputs.map Occurrence.var := by
      rintro hm
      obtain ⟨o, ho, he⟩ := List.mem_map.mp hm
      exact h.fresh o ho (he.symm ▸ hv)
    simp [Log.birth, hn]
  rcases h.arc_cases ha with ha | rfl | ⟨o, ho, rfl⟩
  · rw [hold _ (Log.Grown.used_visited h.grown (es.mem_arcs ha).1)]
    exact h.grown.rank_arc ha
  · simp only [↓reduceIte, hold _ h.visited]
    have := es.birth_le e.input.var
    omega
  · have hm : o.var ∈ e.outputs.map Occurrence.var := List.mem_map.mpr ⟨o, ho, rfl⟩
    simp only [Bool.false_eq_true, ↓reduceIte, Log.birth, hm]
    omega

/-- Every partial scan satisfies all six f-DAG conditions. The current copy need not yet
be saturated, and the local relations need not be even delta-matroids. -/
theorem isFDAG (h : Partial sem f rs es e) (hF : EdgeInstance F)
    (hf : ValidLabeling sem f) : (Log.toDAG rs (e :: es)).IsFDAG sem f where
  valid := hf
  supported := Log.toDAG_supported _ _
  unique _ ha _ hb := h.unique (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb)
  indegree a ha b hb hai hbi he := by
    have hn := h.children_nodup
    rw [← Log.map_outgoing_arcs] at hn
    exact List.inj_on_of_nodup_map hn
      (List.mem_filter.mpr ⟨List.mem_toFinset.mp ha, by simp [hai]⟩)
      (List.mem_filter.mpr ⟨List.mem_toFinset.mp hb, by simp [hbi]⟩) he
  ordered := by
    have hcopy : ∀ a ∈ Log.arcs (e :: es), ∀ b ∈ Log.arcs (e :: es),
        a.time = b.time → a.copy = b.copy := by
      intro a ha b hb ht
      rcases h.arc_cases ha with ha | ha <;> rcases h.arc_cases hb with hb | hb
      · exact h.grown.copy_unique ha hb ht
      · have hbt := congrArg Prod.snd (h.new_copy hb)
        have := (es.mem_arcs ha).2
        change b.time = es.length at hbt
        omega
      · have hat := congrArg Prod.snd (h.new_copy ha)
        have := (es.mem_arcs hb).2
        change a.time = es.length at hat
        omega
      · exact (h.new_copy ha).trans (h.new_copy hb).symm
    refine ⟨?_, ⟨Sum.elim (Log.birth (e :: es)) (fun c => 2 * c.2 + 1), ?_⟩⟩
    · intro c hc d hd ht
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hc)
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hd)
      exact hcopy a ha b hb ht
    · intro x y hxy
      rcases hxy with ⟨a, ha, rfl, rfl⟩ | ⟨c, hc, d, hd, ht, rfl, rfl⟩
      · have hr := h.rank_arc (List.mem_toFinset.mp ha)
        cases hi : a.incoming <;> simpa [Arc.source, Arc.target, hi, Arc.copy] using hr
      · dsimp only [Sum.elim]
        omega
  feasible a ha b hb hai hc := by
    have ha' := List.mem_toFinset.mp ha
    have hb' := List.mem_toFinset.mp hb
    rcases h.arc_cases ha' with ha | rfl | ⟨o, ho, rfl⟩
    · rcases h.arc_cases hb' with hb | hb
      · exact h.grown.feasible hf ha hb hai hc
      · have ht := congrArg Prod.snd (hc.trans (h.new_copy hb))
        have := (es.mem_arcs ha).2
        change a.time = es.length at ht
        omega
    · rcases h.arc_cases hb' with hb | rfl | ⟨o, ho, rfl⟩
      · have ht := congrArg Prod.snd hc
        have := (es.mem_arcs hb).2
        change es.length = b.time at ht
        omega
      · simpa using hf
      · exact ((mem_partners sem f _ _).mp (h.feasible o ho)).2.2
    · cases hai
  noShortcut a ha b hb hai hc ht := by
    have ha' := List.mem_toFinset.mp ha
    have hb' := List.mem_toFinset.mp hb
    rcases h.arc_cases ha' with ha | rfl | ⟨o, ho, rfl⟩
    · rcases h.arc_cases hb' with hb | rfl | ⟨o, ho, rfl⟩
      · exact h.grown.noShortcut hF ha hb hai hc ht
      · exact h.grown.not_partner_of_unused hF ha hai h.unused hc
      · exact h.grown.not_partner_of_unused hF ha hai (h.port_unused (Or.inr ho)) hc
    · have hbt := (Log.mem_arcs (e :: es) hb').2
      simp only [List.length_cons] at hbt
      change es.length < b.time at ht
      omega
    · cases hai

end Partial

/-- Lemma 34 during an actual scan, including every scanned prefix of the candidate list.
The scan may have continued or stopped at its first meeting. -/
theorem scan_isFDAG {sem : Rel → List Bool → Bool} {f : OccurrenceLabeling F Bool}
    (hF : EdgeInstance F) (hf : ValidLabeling sem f) {rs : List V} {es : Log F}
    (hg : Grown sem f rs es) {input : Occurrence F}
    (hv : es.Visited rs input.var) (hu : input ∉ es.used)
    (bs : List (Occurrence F)) (hb : bs ⊆ partners sem f input) :
    (Log.toDAG rs (⟨input, (scan rs es input [] bs).outputs⟩ :: es)).IsFDAG sem f := by
  obtain ⟨hfr, hn, hs⟩ := scan_outputs rs es input bs [] (by simp) (by simp)
  have hp : Partial sem f rs es ⟨input, (scan rs es input [] bs).outputs⟩ :=
    ⟨hg, hv, hu, hfr, hn, fun o ho => hb (hs ho)⟩
  exact hp.isFDAG hF hf

/-- Exact stopping conditions at the first meeting of an actual scan. -/
theorem scan_meeting_spec (rs : List V) (es : Log F) (input : Occurrence F)
    (bs os : List (Occurrence F)) {out : List (Occurrence F)} {b : Occurrence F}
    (hs : scan rs es input os bs = .meeting out b) :
    b ∈ bs ∧ Log.Visited rs (⟨input, out⟩ :: es) b.var ∧
      ¬ Log.SameParent (⟨input, out⟩ :: es) b.var input.1 := by
  induction bs generalizing os with
  | nil => cases hs
  | cons c bs ih =>
    simp only [scan] at hs
    split at hs
    · obtain ⟨hb, hv, hp⟩ := ih _ hs
      exact ⟨List.mem_cons_of_mem c hb, hv, hp⟩
    next hv =>
      split at hs
      · obtain ⟨hb, hv, hp⟩ := ih _ hs
        exact ⟨List.mem_cons_of_mem c hb, hv, hp⟩
      next hp =>
        cases hs
        exact ⟨List.mem_cons_self, of_not_not hv, hp⟩

namespace Meeting

/-- Local execution evidence for a terminal record. No graph invariant or event-correctness
conclusion is a field; these facts follow from the actual partner scan. -/
structure Trace (sem : Rel → List Bool → Bool) (f : OccurrenceLabeling F Bool)
    (m : Meeting F) : Prop where
  /-- The initial nodes are exactly the inconsistent roots. -/
  roots_eq : m.roots = Forest.roots f
  /-- Local insertion and frontier conditions of the partial expansion. -/
  expansion : Partial sem f m.roots m.older m.current
  /-- The meeting port passed the feasible-pair test. -/
  partner : m.output ∈ partners sem f m.current.input
  /-- The meeting variable is visited at scan termination. -/
  visited : Log.Visited m.roots (m.current :: m.older) m.output.var
  /-- Source step 4b did not apply. -/
  not_parent : ¬ Log.SameParent (m.current :: m.older) m.output.var m.current.input.1

variable {sem : Rel → List Bool → Bool} {f : OccurrenceLabeling F Bool} {m : Meeting F}

/-- A terminal partner cannot be a child just inserted at the current copy: its predecessor
would have this original constraint position, triggering source step 4b. -/
theorem Trace.old_visited (h : Trace sem f m) : m.older.Visited m.roots m.output.var := by
  rcases h.visited with hv | hv
  · exact Or.inl hv
  · rcases List.mem_append.mp hv with hv | hv
    · obtain ⟨o, ho, he⟩ := List.mem_map.mp hv
      have hp := Log.sameParent_of_mem_outgoing h.expansion.children_nodup
        (List.mem_append_left m.older.outgoing ho)
      have hc := ((mem_partners sem f _ _).mp (h.expansion.feasible o ho)).1
      exact False.elim (h.not_parent (by simpa only [he, ← hc] using hp))
    · exact Or.inr hv

/-- The second incoming port is fresh even if its variable was visited long ago. Old outgoing
ports trigger step 4b; old incoming ports contradict saturation and current-input freshness. -/
theorem Trace.output_unused (h : Trace sem f m) : m.output ∉ m.older.used := by
  intro hu
  obtain ⟨a, ha, he⟩ := (Log.exists_arc_iff _ _).mpr hu
  cases hi : a.incoming with
  | false =>
    have hm : m.output ∈ m.older.outgoing := he ▸ Log.mem_outgoing_of_arc ha hi
    have hp := Log.sameParent_of_mem_outgoing h.expansion.children_nodup
      (List.mem_append_right m.current.outputs hm)
    have hc := ((mem_partners sem f _ _).mp h.partner).1
    exact h.not_parent (by simpa only [← hc] using hp)
  | true =>
    have hp := (mem_partners sem f _ _).mp h.partner
    have hpartner : m.current.input ∈ partners sem f a.occurrence := by
      apply (mem_partners sem f _ _).mpr
      rw [he]
      exact ⟨hp.1.symm, Ne.symm hp.2.1, by rw [pairFlip_comm]; exact hp.2.2⟩
    obtain ⟨c, hc, he, _, _⟩ := h.expansion.grown.saturated ha hi hpartner
    exact h.expansion.unused (he ▸ (m.older.mem_arcs hc).1)

/-- After pruning, exactly the two incoming arcs remain at the terminal copy. All older
arcs survive, and the supported variables include the pruned, now isolated children. -/
theorem Trace.pruned_arcs (h : Trace sem f m) :
    m.prunedDAG.arcs = insert ⟨m.output, m.older.length, true⟩
      (insert ⟨m.current.input, m.older.length, true⟩ m.older.arcs.toFinset) := by
  ext a
  simp only [Meeting.prunedDAG, Finset.mem_insert]
  apply or_congr_right
  constructor
  · intro ha
    obtain ⟨ha, hp⟩ := Finset.mem_filter.mp ha
    rcases h.expansion.arc_cases (List.mem_toFinset.mp ha) with ha | rfl | ⟨o, ho, rfl⟩
    · exact Or.inr (List.mem_toFinset.mpr ha)
    · exact Or.inl rfl
    · have hc := h.expansion.new_copy (Or.inr ⟨o, ho, rfl⟩)
      exact False.elim (hp.elim (fun hn => hn hc) Bool.noConfusion)
  · rintro (rfl | ha)
    · apply Finset.mem_filter.mpr
      exact ⟨List.mem_toFinset.mpr List.mem_cons_self, Or.inr rfl⟩
    · have ha' := List.mem_toFinset.mp ha
      have hlt := (m.older.mem_arcs ha').2
      have hc : a.copy ≠ m.copy := by
        intro he
        have ht := congrArg Prod.snd he
        change a.time = m.older.length at ht
        omega
      exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr
        (List.mem_cons_of_mem _ (List.mem_append_right _ ha')), Or.inl hc⟩

/-- The terminal graph of Lemma 34's moreover clause is an f-DAG. This proves the
claim for the executable pruning operation, including its retained isolated child support. -/
theorem Trace.pruned_isFDAG (h : Trace sem f m) (hF : EdgeInstance F)
    (hf : ValidLabeling sem f) : m.prunedDAG.IsFDAG sem f := by
  have ht := h.expansion.isFDAG hF hf
  have hp := (mem_partners sem f _ _).mp h.partner
  have hin : m.current.input ≠ m.output := fun he => hp.2.1 (congrArg Occurrence.var he)
  have hcase : ∀ a ∈ m.prunedDAG.arcs,
      a ∈ m.older.arcs ∨ a = ⟨m.current.input, m.older.length, true⟩ ∨
        a = ⟨m.output, m.older.length, true⟩ := by
    intro a ha
    rw [h.pruned_arcs] at ha
    simpa only [Finset.mem_insert, List.mem_toFinset, or_comm, or_left_comm, or_assoc] using ha
  have hold : ∀ a ∈ m.older.arcs, a ∈ m.toDAG.arcs := by
    intro a ha
    exact List.mem_toFinset.mpr (List.mem_cons_of_mem _ (List.mem_append_right _ ha))
  have hic : (⟨m.current.input, m.older.length, true⟩ : Arc F) ∈ m.toDAG.arcs :=
    List.mem_toFinset.mpr List.mem_cons_self
  have hnewtime : ∀ a ∈ m.prunedDAG.arcs, a.time ≤ m.older.length := by
    intro a ha
    rcases hcase a ha with ha | rfl | rfl
    · exact Nat.le_of_lt (m.older.mem_arcs ha).2
    · exact Nat.le_refl _
    · exact Nat.le_refl _
  have hcopy : ∀ a ∈ m.prunedDAG.arcs,
      a ∈ m.older.arcs ∨ a.copy = m.copy := by
    intro a ha
    rcases hcase a ha with ha | rfl | rfl
    · exact Or.inl ha
    · exact Or.inr rfl
    · exact Or.inr (Prod.ext hp.1.symm rfl)
  refine ⟨hf, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    rcases hcase a ha with ha | rfl | rfl
    · exact ht.supported a (hold a ha)
    · exact ht.supported _ hic
    · refine ⟨?_, ?_⟩
      · exact Log.Visited.mem_vars (h.old_visited.imp_right
          (fun hv => List.mem_append_right _ hv))
      · change (m.output.1, m.older.length) ∈ m.toDAG.copies
        rw [← hp.1]
        exact (ht.supported _ hic).2
  · intro a ha b hb he
    rcases hcase a ha with ha | rfl | rfl <;> rcases hcase b hb with hb | rfl | rfl
    · exact h.expansion.grown.unique ha hb he
    · change a.occurrence = m.current.input at he
      exact False.elim (h.expansion.unused (he ▸ (m.older.mem_arcs ha).1))
    · change a.occurrence = m.output at he
      exact False.elim (h.output_unused (he ▸ (m.older.mem_arcs ha).1))
    · change m.current.input = b.occurrence at he
      exact False.elim (h.expansion.unused (he.symm ▸ (m.older.mem_arcs hb).1))
    · rfl
    · exact False.elim (hin he)
    · change m.output = b.occurrence at he
      exact False.elim (h.output_unused (he.symm ▸ (m.older.mem_arcs hb).1))
    · exact False.elim (hin he.symm)
    · rfl
  · intro a ha b hb hai hbi he
    rcases hcase a ha with ha | rfl | rfl <;> rcases hcase b hb with hb | rfl | rfl
    · exact h.expansion.grown.indegree ha hb hai hbi he
    all_goals contradiction
  · refine ⟨ht.ordered.1, ⟨Sum.elim (Log.birth (m.current :: m.older))
      (fun c => 2 * c.2 + 1), ?_⟩⟩
    intro x y hxy
    rcases hxy with ⟨a, ha, rfl, rfl⟩ | ⟨c, hc, d, hd, hcd, rfl, rfl⟩
    · rcases hcase a ha with ha | rfl | rfl
      · have hr := h.expansion.rank_arc (List.mem_cons_of_mem _ (List.mem_append_right _ ha))
        cases hi : a.incoming <;> simpa [Arc.source, Arc.target, hi, Arc.copy] using hr
      · have hr := h.expansion.rank_arc (List.mem_cons_self (a :=
          (⟨m.current.input, m.older.length, true⟩ : Arc F)))
        simpa [Arc.source, Arc.target, Arc.copy] using hr
      · have hn : m.output.var ∉ m.current.outputs.map Occurrence.var := by
          rintro hv
          obtain ⟨o, ho, he⟩ := List.mem_map.mp hv
          exact h.expansion.fresh o ho (he.symm ▸ h.old_visited)
        have hr := m.older.birth_le m.output.var
        simp only [Arc.source, Arc.target, Arc.copy, ↓reduceIte, Sum.elim_inl,
          Sum.elim_inr, Log.birth, hn]
        omega
    · dsimp only [Sum.elim]
      omega
  · intro a ha b hb hai hc
    rcases hcase a ha with ha | rfl | rfl <;> rcases hcase b hb with hb | rfl | rfl
    · exact h.expansion.grown.feasible hf ha hb hai hc
    · have := (m.older.mem_arcs ha).2
      have := congrArg Prod.snd hc
      change a.time = m.older.length at this
      omega
    · have := (m.older.mem_arcs ha).2
      have := congrArg Prod.snd hc
      change a.time = m.older.length at this
      omega
    · have := (m.older.mem_arcs hb).2
      have := congrArg Prod.snd hc
      change m.older.length = b.time at this
      omega
    · simpa using hf
    · exact hp.2.2
    · have := (m.older.mem_arcs hb).2
      have := congrArg Prod.snd hc
      change m.older.length = b.time at this
      omega
    · rw [pairFlip_comm]
      exact hp.2.2
    · simpa using hf
  · intro a ha b hb hai hc hlt
    rcases hcase a ha with ha | rfl | rfl
    · rcases hcase b hb with hb | rfl | rfl
      · exact h.expansion.grown.noShortcut hF ha hb hai hc hlt
      · exact h.expansion.grown.not_partner_of_unused hF ha hai h.expansion.unused hc
      · exact h.expansion.grown.not_partner_of_unused hF ha hai h.output_unused hc
    · have := hnewtime b hb
      change m.older.length < b.time at hlt
      omega
    · have := hnewtime b hb
      change m.older.length < b.time at hlt
      omega

end Meeting

/-- A property of every terminal event, vacuous for exhaustion. -/
@[expose] def Result.Events (P : Meeting F → Prop) : Result F → Prop
  | .exhausted _ => True
  | .augment m => P m
  | .blossom m => P m

/-- Execution derives terminal scan evidence, independently of graph and event correctness. -/
theorem run_trace (sem : Rel → List Bool → Bool) (f : OccurrenceLabeling F Bool)
    (hF : EdgeInstance F) (es : Log F) (remaining : List (Occurrence F))
    (hg : Grown sem f (roots f) es) (hu : ∀ o ∈ remaining, o ∉ es.used) :
    (run sem f (roots f) es remaining).Events (Meeting.Trace sem f) := by
  unfold run
  split
  · trivial
  next input hi =>
    have hv : es.Visited (roots f) input.var := by
      simpa only [decide_eq_true_eq] using List.find?_some hi
    have hui := hu input (List.mem_of_find?_eq_some hi)
    split
    next os o hs =>
      have hout := scan_outputs (roots f) es input (partners sem f input) []
        (by simp) (by simp)
      rw [hs] at hout
      obtain ⟨ho, hvo, hpo⟩ := scan_meeting_spec (roots f) es input _ [] hs
      have ht : Meeting.Trace sem f ⟨roots f, es, ⟨input, os⟩, o⟩ :=
        ⟨rfl, ⟨hg, hv, hui, hout.1, hout.2.1, fun p hp => hout.2.2 hp⟩, ho, hvo, hpo⟩
      dsimp only
      split <;> exact ht
    next os hs =>
      apply run_trace sem f hF _ _ (hg.of_scan hF hv hui hs)
      intro o ho
      exact of_decide_eq_true (List.mem_filter.mp ho).2
termination_by remaining.length
decreasing_by
  rename_i input hi _ _ os _ _
  have hm : input ∈ remaining := List.mem_of_find?_eq_some hi
  have hpos := List.length_pos_of_mem hm
  have he := List.length_erase_of_mem hm
  have hf := List.length_filter_le (fun a => decide
    (a ∉ Log.used ((⟨input, os⟩ : Expansion F) :: es))) (remaining.erase input)
  omega

/-- Every terminal event in a fresh run has evidence obtained from its real scans. -/
theorem search_trace (sem : Rel → List Bool → Bool) (f : OccurrenceLabeling F Bool)
    (hF : EdgeInstance F) : (search sem f).Events (Meeting.Trace sem f) :=
  run_trace sem f hF _ _ .nil (by simp [Log.used])

/-- Lemma 34 for both terminal graphs actually returned by a fresh search. No event or
forest-correctness premise and no even-delta-matroid hypothesis is required. -/
theorem search_terminal_isFDAG (sem : Rel → List Bool → Bool)
    (f : OccurrenceLabeling F Bool) (hF : EdgeInstance F) (hf : ValidLabeling sem f) :
    (search sem f).Events (fun m => m.toDAG.IsFDAG sem f ∧ m.prunedDAG.IsFDAG sem f) := by
  have hs := search_trace sem f hF
  cases hr : search sem f with
  | exhausted es => trivial
  | augment m =>
    rw [hr] at hs
    exact ⟨hs.expansion.isFDAG hF hf, hs.pruned_isFDAG hF hf⟩
  | blossom m =>
    rw [hr] at hs
    exact ⟨hs.expansion.isFDAG hF hf, hs.pruned_isFDAG hF hf⟩

end Cslib.Logic.PL.CSP.Forest
