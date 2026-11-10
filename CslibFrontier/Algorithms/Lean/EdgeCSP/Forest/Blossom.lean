/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.EdgeCSP.Forest.Events
public import CslibFrontier.Logics.Propositional.CSP.Edge.Walk.Visits
import CslibFrontier.Foundations.Data.Finset.SymmDiff

/-!
# Blossoms returned by chronological forest search

The two LCA cases of [KazdaKolmogorovRolinek2018], arXiv:1602.03124v6, Section 5.3,
printed pp. 11–12, and Definition 39/Lemma 41, printed pp. 19–20. The cycle, preparation,
pivot, timestamps and child ports are those computed by `Meeting.blossomData`.

## Main results

* `Meeting.Trace.blossom_correct`: both raw extractor branches satisfy Definition 39.
* `Meeting.Trace.variable_prepare_empty`: a variable LCA is an inconsistent root.
* `search_blossom_correct`: an actual fresh-run blossom result supplies valid preparation,
  a source-strength blossom, and unchanged defect count, from instance hypotheses alone.

The proof uses chronological prefix transfer as an alternative to the source's repeated
graph surgery, followed by its Lemma 37 rerooting at a constraint LCA. No contraction or
lifting algorithm, encoded runtime bound, or planar dichotomy is claimed here.
-/

public section

namespace Cslib.Logic.PL.CSP.Forest.Meeting

open DAG

variable {Rel V : Type*} {F : CSP Rel V} [DecidableEq V]
  {sem : Rel → List Bool → Bool} {f : OccurrenceLabeling F Bool} {m : Meeting F}

/-- The two actual ancestral suffixes and their incoming terminal meeting ports. Shared
root-side copies before step `k` are omitted. This is the graph used in Lemma 41's preparation. -/
@[expose] def forkDAG (m : Meeting F) (k : ℕ) : DAG F :=
  ((pathDAG (m.left.walk.drop k) m.older.stamp).union
    (pathDAG (m.right.walk.drop k) m.older.stamp)).union
      (terminalPair ⟨m.current.input, m.older.length, true⟩ ⟨m.output, m.older.length, true⟩)

/-- Every fork arc is an actual ancestral arc or one of the two incoming meeting ports. -/
@[simp] theorem mem_forkDAG_arcs (m : Meeting F) (k : ℕ) (a : Arc F) :
    a ∈ (m.forkDAG k).arcs ↔
      a ∈ pathArcs (m.left.walk.drop k) m.older.stamp ∨
      a ∈ pathArcs (m.right.walk.drop k) m.older.stamp ∨
      a = ⟨m.current.input, m.older.length, true⟩ ∨ a = ⟨m.output, m.older.length, true⟩ := by
  simp only [forkDAG, DAG.union, terminalPair, pathDAG, Finset.mem_union,
    Finset.mem_insert, Finset.mem_singleton]
  tauto

/-- The suffix fork is a supported subgraph of the actual terminal pruned forest. -/
theorem Trace.fork_subgraph (h : Trace sem f m) (hF : EdgeInstance F)
    (hf : ValidLabeling sem f) (k : ℕ) :
    (m.forkDAG k).Subgraph m.prunedDAG ∧ (m.forkDAG k).Supported := by
  have hT := h.pruned_isFDAG hF hf
  have hw := h.left_directed.drop hT.supported k
  have hz := h.right_directed.drop hT.supported k
  have ha : (⟨m.current.input, m.older.length, true⟩ : Arc F) ∈ m.prunedDAG.arcs := by
    rw [h.pruned_arcs]; simp
  have hb : (⟨m.output, m.older.length, true⟩ : Arc F) ∈ m.prunedDAG.arcs := by
    rw [h.pruned_arcs]; simp
  have hc : (⟨m.current.input, m.older.length, true⟩ : Arc F).copy =
      (⟨m.output, m.older.length, true⟩ : Arc F).copy :=
    Prod.ext ((mem_partners sem f _ _).mp h.partner).1 rfl
  let Q := terminalPair (⟨m.current.input, m.older.length, true⟩ : Arc F)
    ⟨m.output, m.older.length, true⟩
  have hqs : Q.Supported := by
    intro a ham
    rcases (show a = ⟨m.current.input, m.older.length, true⟩ ∨
        a = ⟨m.output, m.older.length, true⟩ by
      simpa only [Q, terminalPair, Finset.mem_insert, Finset.mem_singleton] using ham) with
      rfl | rfl
    · exact ⟨by simp [Q, terminalPair], Finset.mem_singleton_self _⟩
    · exact ⟨by simp [Q, terminalPair], Finset.mem_singleton.mpr hc.symm⟩
  have hq : Q.Subgraph m.prunedDAG := by
    refine ⟨?_, ?_, ?_⟩
    · intro v hv
      rcases (show v = m.current.input.var ∨ v = m.output.var by simpa [Q, terminalPair] using hv)
        with rfl | rfl
      · exact (hT.supported _ ha).1
      · exact (hT.supported _ hb).1
    · intro c hc'
      have he := Finset.mem_singleton.mp hc'
      exact he ▸ (hT.supported _ ha).2
    · intro a ham
      rcases (show a = ⟨m.current.input, m.older.length, true⟩ ∨
          a = ⟨m.output, m.older.length, true⟩ by
        simpa only [Q, terminalPair, Finset.mem_insert, Finset.mem_singleton] using ham) with
        rfl | rfl
      · exact ha
      · exact hb
  exact ⟨((hw.subgraph hT.supported).union (hz.subgraph hT.supported)).union hq,
    ((pathDAG_supported _ _).union (pathDAG_supported _ _)).union hqs⟩

/-- Flipping the shared root prefix preserves the full f-DAG invariant on the actual
remaining suffix fork. Unused earlier branches are discarded, and original constraints
may recur later at different timestamps. -/
theorem Trace.prepare_fork_isFDAG (h : Trace sem f m) (hF : EdgeInstance F)
    (hf : ValidLabeling sem f) (hM : EdgeInstance.EvenConstraints sem F)
    (k : ℕ) (hk : 2 * k + 1 ≤ m.commonNodes.length) :
    (m.forkDAG k).IsFDAG sem ((m.left.walk.take k).flip f) := by
  have hT := h.pruned_isFDAG hF hf
  obtain ⟨hsub, hsup⟩ := h.fork_subgraph hF hf k
  have hw := h.left_directed.drop hT.supported k
  have hz := h.right_directed.drop hT.supported k
  have hchron := (h.expansion.grown.ancestry_chronological m.current.input.var).sublist
    (List.take_sublist k _)
  apply (h.left_directed.take k).flip_later_subgraph hT hM hchron hsub hsup
  intro c hc s hs
  change c ∈ ((pathDAG _ _).copies ∪ (pathDAG _ _).copies) ∪ {_} at hc
  rcases Finset.mem_union.mp hc with hc | hc
  · rcases Finset.mem_union.mp hc with hc | hc
    · obtain ⟨t, ht, he⟩ := hw.mem_copies.mp hc
      have hpair : (m.left.walk.steps.take k ++ m.left.walk.steps.drop k).Pairwise
          (fun s t => m.older.stamp s.1 < m.older.stamp t.1) := by
        rw [List.take_append_drop]
        exact h.expansion.grown.ancestry_chronological _
      have hh := (List.pairwise_append.mp hpair).2.2 s hs t ht
      exact (congrArg Prod.snd he) ▸ hh
    · obtain ⟨t, ht, he⟩ := hz.mem_copies.mp hc
      have hh := h.prefix_time_lt_right_drop k hk hs ht
      exact (congrArg Prod.snd he) ▸ hh
  · have he := Finset.mem_singleton.mp hc
    rw [he]
    exact (m.older.mem_arcs
      (h.expansion.grown.ancestry_arcs _ (List.mem_of_mem_take hs)).1).2

/-- A constraint LCA ends the shared node prefix immediately before its two children. -/
theorem ancestor_constraint_length (m : Meeting F) {c : Copy F}
    (hc : m.ancestor? = some (.inr c)) :
    m.commonNodes.length = 2 * ((m.commonNodes.length - 1) / 2) + 2 := by
  have hpos : 0 < m.commonNodes.length := by
    cases he : m.commonNodes with
    | nil => simp [ancestor?, he] at hc
    | cons a as => simp
  have hstep := (m.ancestor_constraint_index_lt hc).1
  by_cases hm : (m.commonNodes.length - 1) % 2 = 1
  · omega
  · have hi : m.commonNodes.length - 1 = 2 * ((m.commonNodes.length - 1) / 2) := by omega
    have hh := (m.ancestor_at_common_index hc).1
    rw [hi, m.left.nodes_getElem?_even (m.older.ancestry_length _) _ (Nat.le_of_lt hstep)] at hh
    cases hh

/-- The two steps selected by the raw constraint-LCA branch use that actual copied node. -/
theorem Trace.constraint_first_copies (h : Trace sem f m) {c : Copy F}
    (hc : m.ancestor? = some (.inr c)) {s t : Occurrence F × Occurrence F}
    (hs : m.left.walk.steps[(m.commonNodes.length - 1) / 2]? = some s)
    (ht : m.right.walk.steps[(m.commonNodes.length - 1) / 2]? = some t) :
    (inArc m.older.stamp s).copy = c ∧ (inArc m.older.stamp t).copy = c := by
  let k := (m.commonNodes.length - 1) / 2
  have hlen : m.commonNodes.length = 2 * k + 2 := m.ancestor_constraint_length hc
  have hside : ∀ (p : Ancestry F) (u : V) (s : Occurrence F × Occurrence F),
      p = m.older.ancestry u → k < p.walk.steps.length →
      p.nodes[m.commonNodes.length - 1]? = some (.inr c) → p.walk.steps[k]? = some s →
      (inArc m.older.stamp s).copy = c := by
    intro p u s hp hk hn hs
    have hpl : p.times.length = p.walk.steps.length := by
      rw [hp]
      exact m.older.ancestry_length _
    have hs' : p.walk.steps[k] = s := by
      simpa only [List.getElem?_eq_getElem hk, Option.some.injEq] using hs
    have htime : p.times[k]'(by omega) =
        m.older.stamp (p.walk.steps[k]).1 := by
      have hh := h.expansion.grown.ancestry_times_eq_stamp u
      rw [← hp] at hh
      simp only [hh, List.getElem_map]
    have hi : m.commonNodes.length - 1 = 2 * k + 1 := by omega
    rw [hi, p.nodes_getElem?_odd hpl k hk] at hn
    have hh := Sum.inr.inj (Option.some.inj hn)
    simpa only [htime, hs', inArc, Arc.copy] using hh
  exact ⟨hside _ _ s rfl (m.ancestor_constraint_index_lt hc).1
      (m.ancestor_at_common_index hc).1 hs,
    hside _ _ t rfl (m.ancestor_constraint_index_lt hc).2
      (m.ancestor_at_common_index hc).2 ht⟩

/-- The child ports at a constraint LCA name distinct variables. Otherwise their common
child would extend the computed common-node prefix, contradicting maximality. -/
theorem Trace.constraint_children_ne (h : Trace sem f m) {c : Copy F}
    (hc : m.ancestor? = some (.inr c)) {s t : Occurrence F × Occurrence F}
    (hs : m.left.walk.steps[(m.commonNodes.length - 1) / 2]? = some s)
    (ht : m.right.walk.steps[(m.commonNodes.length - 1) / 2]? = some t) :
    s.2.var ≠ t.2.var := by
  let k := (m.commonNodes.length - 1) / 2
  have hkl : k < m.left.walk.steps.length := (m.ancestor_constraint_index_lt hc).1
  have hkr : k < m.right.walk.steps.length := (m.ancestor_constraint_index_lt hc).2
  change m.left.walk.steps[k]? = some s at hs
  change m.right.walk.steps[k]? = some t at ht
  have hsval : m.left.walk.steps[k] = s := by
    simpa only [List.getElem?_eq_getElem hkl, Option.some.injEq] using hs
  have htval : m.right.walk.steps[k] = t := by
    simpa only [List.getElem?_eq_getElem hkr, Option.some.injEq] using ht
  have hsd : s ∈ m.left.walk.steps.drop k := by
    rw [List.drop_eq_getElem_cons hkl, hsval]
    exact List.mem_cons_self
  have htd : t ∈ m.right.walk.steps.drop k := by
    rw [List.drop_eq_getElem_cons hkr, htval]
    exact List.mem_cons_self
  have hsl := List.mem_of_mem_drop hsd
  have htr := List.mem_of_mem_drop htd
  have hcopies := h.constraint_first_copies hc hs ht
  have hinput := Log.incoming_time_unique
    (h.expansion.grown.ancestry_arcs _ hsl).1 (h.expansion.grown.ancestry_arcs _ htr).1
    rfl rfl (congrArg Prod.snd (hcopies.1.trans hcopies.2.symm))
  intro hv
  have houtput := h.expansion.grown.indegree
    (h.expansion.grown.ancestry_arcs _ hsl).2 (h.expansion.grown.ancestry_arcs _ htr).2
    rfl rfl hv
  have he : s = t := Prod.ext (congrArg Arc.occurrence hinput) (congrArg Arc.occurrence houtput)
  cases he
  have hl := h.expansion.grown.ancestry_step_full_nodes_prefix hsl
  have hr := h.expansion.grown.ancestry_step_full_nodes_prefix htr
  have hb := m.commonNodes_maximal _ hl hr
  have hnodes := (m.older.ancestry s.1.var).nodes_length (m.older.ancestry_length _)
  simp only [List.length_append, List.length_cons, List.length_nil, hnodes] at hb
  have hindex := h.expansion.grown.ancestry_step_prefix_length hsd
  have hlength : m.commonNodes.length = 2 * k + 2 := m.ancestor_constraint_length hc
  omega

/-- The copied constraint selected as the LCA is the earliest copy of the remaining fork. -/
theorem Trace.constraint_fork_earliest (h : Trace sem f m) {c : Copy F}
    (hc : m.ancestor? = some (.inr c)) {s t : Occurrence F × Occurrence F}
    (hs : m.left.walk.steps[(m.commonNodes.length - 1) / 2]? = some s)
    (ht : m.right.walk.steps[(m.commonNodes.length - 1) / 2]? = some t) :
    (m.forkDAG ((m.commonNodes.length - 1) / 2)).Earliest c := by
  let k := (m.commonNodes.length - 1) / 2
  have hkl : k < m.left.walk.steps.length := (m.ancestor_constraint_index_lt hc).1
  have hkr : k < m.right.walk.steps.length := (m.ancestor_constraint_index_lt hc).2
  change m.left.walk.steps[k]? = some s at hs
  change m.right.walk.steps[k]? = some t at ht
  have hsval : m.left.walk.steps[k] = s := by
    simpa only [List.getElem?_eq_getElem hkl, Option.some.injEq] using hs
  have htval : m.right.walk.steps[k] = t := by
    simpa only [List.getElem?_eq_getElem hkr, Option.some.injEq] using ht
  have hdl : m.left.walk.steps.drop k = s :: m.left.walk.steps.drop (k + 1) := by
    rw [List.drop_eq_getElem_cons hkl, hsval]
  have hdr : m.right.walk.steps.drop k = t :: m.right.walk.steps.drop (k + 1) := by
    rw [List.drop_eq_getElem_cons hkr, htval]
  have hw := (h.expansion.grown.ancestry_directed h.expansion.visited).drop
    (m.older.toDAG_supported m.roots) k
  have hz := (h.expansion.grown.ancestry_directed h.old_visited).drop
    (m.older.toDAG_supported m.roots) k
  have hcs := h.constraint_first_copies hc hs ht
  have hsm : s ∈ (m.left.walk.drop k).steps := by
    change s ∈ m.left.walk.steps.drop k
    rw [hdl]
    exact List.mem_cons_self
  have hmin : ∀ (p : Walk F) (s : Occurrence F × Occurrence F) (tail),
      DirectedPath (m.older.toDAG m.roots) p m.older.stamp → p.steps = s :: tail →
      p.steps.Pairwise (fun s t => m.older.stamp s.1 < m.older.stamp t.1) →
      (inArc m.older.stamp s).copy = c →
      ∀ d ∈ (pathDAG p m.older.stamp).copies, c.2 ≤ d.2 := by
    intro p s tail hp he ho hs d hd
    obtain ⟨u, hu, heq⟩ := hp.mem_copies.mp hd
    rw [he] at hu ho
    have hst := congrArg Prod.snd hs
    have hut := congrArg Prod.snd heq
    change m.older.stamp s.1 = c.2 at hst
    change m.older.stamp u.1 = d.2 at hut
    rcases List.mem_cons.mp hu with rfl | hu
    · omega
    · have hh := (List.pairwise_cons.mp ho).1 u hu
      omega
  refine ⟨?_, ?_⟩
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ (hw.mem_copies.mpr ⟨s, hsm, hcs.1⟩))
  · intro d hd
    change d ∈ ((pathDAG _ _).copies ∪ (pathDAG _ _).copies) ∪ {_} at hd
    rcases Finset.mem_union.mp hd with hd | hd
    · rcases Finset.mem_union.mp hd with hd | hd
      · exact hmin _ s _ hw hdl ((h.expansion.grown.ancestry_chronological _).sublist
          (List.drop_sublist k _)) hcs.1 d hd
      · exact hmin _ t _ hz hdr ((h.expansion.grown.ancestry_chronological _).sublist
          (List.drop_sublist k _)) hcs.2 d hd
    · have he := Finset.mem_singleton.mp hd
      rw [he]
      have ha := (h.expansion.grown.ancestry_arcs _ (List.mem_of_mem_drop hsm)).1
      have hh := (m.older.mem_arcs ha).2
      have hct := congrArg Prod.snd hcs.1
      change m.older.stamp s.1 = c.2 at hct
      exact Nat.le_of_lt (hct ▸ hh)

/-- The root-side input at a constraint LCA is a leaf of the selected suffix fork. -/
theorem Trace.constraint_fork_leaf (h : Trace sem f m) (hF : EdgeInstance F)
    (hf : ValidLabeling sem f) {c : Copy F} (hc : m.ancestor? = some (.inr c))
    {s t : Occurrence F × Occurrence F}
    (hs : m.left.walk.steps[(m.commonNodes.length - 1) / 2]? = some s)
    (ht : m.right.walk.steps[(m.commonNodes.length - 1) / 2]? = some t) :
    ∀ a ∈ (m.forkDAG ((m.commonNodes.length - 1) / 2)).arcs,
      a.occurrence.var = s.1.var → a = inArc m.older.stamp s := by
  let k := (m.commonNodes.length - 1) / 2
  have hT := h.pruned_isFDAG hF hf
  have hkl : k < m.left.walk.steps.length := (m.ancestor_constraint_index_lt hc).1
  have hkr : k < m.right.walk.steps.length := (m.ancestor_constraint_index_lt hc).2
  change m.left.walk.steps[k]? = some s at hs
  change m.right.walk.steps[k]? = some t at ht
  have hsval : m.left.walk.steps[k] = s := by
    simpa only [List.getElem?_eq_getElem hkl, Option.some.injEq] using hs
  have htval : m.right.walk.steps[k] = t := by
    simpa only [List.getElem?_eq_getElem hkr, Option.some.injEq] using ht
  have hdl : (m.left.walk.drop k).steps = s :: m.left.walk.steps.drop (k + 1) := by
    change m.left.walk.steps.drop k = _
    rw [List.drop_eq_getElem_cons hkl, hsval]
  have hdr : (m.right.walk.drop k).steps = t :: m.right.walk.steps.drop (k + 1) := by
    change m.right.walk.steps.drop k = _
    rw [List.drop_eq_getElem_cons hkr, htval]
  have hw := h.left_directed.drop hT.supported k
  have hz := h.right_directed.drop hT.supported k
  have hcs := h.constraint_first_copies hc hs ht
  have hsl : s ∈ m.left.walk.steps := List.mem_of_mem_drop (hdl ▸ List.mem_cons_self)
  have htr : t ∈ m.right.walk.steps := List.mem_of_mem_drop (hdr ▸ List.mem_cons_self)
  have haeq := Log.incoming_time_unique (h.expansion.grown.ancestry_arcs _ hsl).1
    (h.expansion.grown.ancestry_arcs _ htr).1 rfl rfl
    (congrArg Prod.snd (hcs.1.trans hcs.2.symm))
  have hin : s.1 = t.1 := congrArg Arc.occurrence haeq
  have hls : s.1.var = (m.left.walk.drop k).start := by
    have hh := hw.walk.1; rw [hdl] at hh; exact hh.1
  have hrs : t.1.var = (m.right.walk.drop k).start := by
    have hh := hz.walk.1; rw [hdr] at hh; exact hh.1
  have hneL := hw.finish_ne_start hT (by rw [hdl]; simp)
  have hneR := hz.finish_ne_start hT (by rw [hdr]; simp)
  simp only [Walk.finish_drop, Meeting.left, Meeting.right, Log.ancestry_finish] at hneL hneR
  intro a ha hv
  rcases (mem_forkDAG_arcs _ _ _).mp ha with ha | ha | rfl | rfl
  · exact hw.start_arc_eq hT hdl ha (hv.trans hls)
  · exact (hz.start_arc_eq hT hdr ha (hv.trans ((congrArg Occurrence.var hin).trans hrs))).trans
      haeq.symm
  · exact False.elim (hneL (hv.trans hls))
  · exact False.elim (hneR (hv.trans ((congrArg Occurrence.var hin).trans hrs)))

/-- At the LCA copy, the selected forest fork has precisely its original single incoming
port. The second incoming meeting port is at the strictly later terminal copy. -/
theorem Trace.constraint_fork_incoming_eq (h : Trace sem f m) (hF : EdgeInstance F)
    (hf : ValidLabeling sem f) {c : Copy F} (hc : m.ancestor? = some (.inr c))
    {s : Occurrence F × Occurrence F}
    (hs : m.left.walk.steps[(m.commonNodes.length - 1) / 2]? = some s) :
    ∀ a ∈ (m.forkDAG ((m.commonNodes.length - 1) / 2)).arcs,
      a.incoming = true → a.copy = (inArc m.older.stamp s).copy →
      a = inArc m.older.stamp s := by
  let k := (m.commonNodes.length - 1) / 2
  have hkl : k < m.left.walk.steps.length := (m.ancestor_constraint_index_lt hc).1
  change m.left.walk.steps[k]? = some s at hs
  have hsval : m.left.walk.steps[k] = s := by
    simpa only [List.getElem?_eq_getElem hkl, Option.some.injEq] using hs
  have hsd : s ∈ m.left.walk.steps.drop k := by
    rw [List.drop_eq_getElem_cons hkl, hsval]
    exact List.mem_cons_self
  have hA := (h.expansion.grown.ancestry_arcs _ (List.mem_of_mem_drop hsd)).1
  have hbound := (m.older.mem_arcs hA).2
  change m.older.stamp s.1 < m.older.length at hbound
  have hsub := (h.fork_subgraph hF hf k).1
  intro a ha hi hac
  have haT := hsub.2.2 ha
  rw [h.pruned_arcs] at haT
  rcases Finset.mem_insert.mp haT with rfl | haT
  · have hh := congrArg Prod.snd hac
    change m.older.length = m.older.stamp s.1 at hh
    omega
  · rcases Finset.mem_insert.mp haT with rfl | haT
    · have hh := congrArg Prod.snd hac
      change m.older.length = m.older.stamp s.1 at hh
      omega
    · exact Log.incoming_time_unique (List.mem_toFinset.mp haT) hA hi rfl
        (congrArg Prod.snd hac)

/-- Source Lemma 41's constraint-LCA surgery: flip the actual root-to-left-child path,
remove its root-side input, and reverse that child's LCA incidence. The full remaining
fork is an f-DAG for the prepared labeling. -/
theorem Trace.reroot_constraint_fork (h : Trace sem f m) (hF : EdgeInstance F)
    (hf : ValidLabeling sem f) (hM : EdgeInstance.EvenConstraints sem F)
    {c : Copy F} (hc : m.ancestor? = some (.inr c))
    {s t : Occurrence F × Occurrence F}
    (hs : m.left.walk.steps[(m.commonNodes.length - 1) / 2]? = some s)
    (ht : m.right.walk.steps[(m.commonNodes.length - 1) / 2]? = some t) :
    ((m.forkDAG ((m.commonNodes.length - 1) / 2)).reroot
      (inArc m.older.stamp s) (outArc m.older.stamp s)).IsFDAG sem
      ((m.left.walk.take ((m.commonNodes.length - 1) / 2 + 1)).flip f) := by
  let k := (m.commonNodes.length - 1) / 2
  have hkl : k < m.left.walk.steps.length := (m.ancestor_constraint_index_lt hc).1
  change m.left.walk.steps[k]? = some s at hs
  have hsval : m.left.walk.steps[k] = s := by
    simpa only [List.getElem?_eq_getElem hkl, Option.some.injEq] using hs
  have hdl : (m.left.walk.drop k).steps = s :: m.left.walk.steps.drop (k + 1) := by
    change m.left.walk.steps.drop k = _
    rw [List.drop_eq_getElem_cons hkl, hsval]
  have hsm : s ∈ (m.left.walk.drop k).steps := by rw [hdl]; exact List.mem_cons_self
  have hp := h.left_directed.walk.drop k
  have hlink := hp.1
  rw [hdl] at hlink
  have hcopy : (inArc m.older.stamp s).copy = (outArc m.older.stamp s).copy :=
    Prod.ext hlink.2.1 rfl
  have hA : inArc m.older.stamp s ∈ (m.forkDAG k).arcs := by
    apply (mem_forkDAG_arcs _ _ _).mpr
    exact Or.inl (Finset.mem_biUnion.mpr ⟨s, List.mem_toFinset.mpr hsm, by simp⟩)
  have hB : outArc m.older.stamp s ∈ (m.forkDAG k).arcs := by
    apply (mem_forkDAG_arcs _ _ _).mpr
    exact Or.inl (Finset.mem_biUnion.mpr ⟨s, List.mem_toFinset.mpr hsm, by simp⟩)
  have hlen : m.commonNodes.length = 2 * k + 2 := m.ancestor_constraint_length hc
  have hY := h.prepare_fork_isFDAG hF hf hM k (by omega)
  have hfirst : (m.forkDAG k).Earliest (inArc m.older.stamp s).copy := by
    rw [(h.constraint_first_copies hc hs ht).1]
    exact h.constraint_fork_earliest hc hs ht
  have hR := hY.reroot_earliest hM hA hB rfl rfl hcopy hfirst
    (h.constraint_fork_leaf hF hf hc hs ht) (h.constraint_fork_incoming_eq hF hf hc hs)
  have hflip : (m.left.walk.take (k + 1)).flip f =
      pairFlip ((m.left.walk.take k).flip f) s.1 s.2 := by
    simpa only [hsval] using h.left_directed.walk.flip_take_succ f hkl
  change ((m.forkDAG k).reroot (inArc m.older.stamp s) (outArc m.older.stamp s)).IsFDAG sem
    (pairFlip ((m.left.walk.take k).flip f) s.1 s.2) at hR
  rwa [← hflip] at hR

/-- The constraint-LCA cycle, with its actual terminal and LCA timestamps, embeds into
the prepared rerooted fork. This proves the complete Definition 39 graph condition. -/
theorem Trace.constraint_cycle_isFDAG (h : Trace sem f m) (hF : EdgeInstance F)
    (hf : ValidLabeling sem f) (hM : EdgeInstance.EvenConstraints sem F)
    {c : Copy F} (hc : m.ancestor? = some (.inr c))
    {s t : Occurrence F × Occurrence F}
    (hs : m.left.walk.steps[(m.commonNodes.length - 1) / 2]? = some s)
    (ht : m.right.walk.steps[(m.commonNodes.length - 1) / 2]? = some t) :
    let k := (m.commonNodes.length - 1) / 2
    let w := m.left.walk.drop (k + 1)
    let z := m.right.walk.drop (k + 1)
    (blossomDAG (((w.snoc m.current.input m.output).append z.reverse).snoc t.2 s.2)
      (w.steps.map (fun u => m.older.stamp u.1) ++ [m.older.length] ++
        (z.steps.map fun u => m.older.stamp u.1).reverse ++ [c.2]) (w.steps.length + 1)).IsFDAG
      sem ((m.left.walk.take (k + 1)).flip f) := by
  let k := (m.commonNodes.length - 1) / 2
  let w := m.left.walk.drop (k + 1)
  let z := m.right.walk.drop (k + 1)
  let R := (m.forkDAG k).reroot (inArc m.older.stamp s) (outArc m.older.stamp s)
  have hR : R.IsFDAG sem ((m.left.walk.take (k + 1)).flip f) :=
    h.reroot_constraint_fork hF hf hM hc hs ht
  have hkl : k < m.left.walk.steps.length := (m.ancestor_constraint_index_lt hc).1
  have hkr : k < m.right.walk.steps.length := (m.ancestor_constraint_index_lt hc).2
  change m.left.walk.steps[k]? = some s at hs
  change m.right.walk.steps[k]? = some t at ht
  have hsval : m.left.walk.steps[k] = s := by
    simpa only [List.getElem?_eq_getElem hkl, Option.some.injEq] using hs
  have htval : m.right.walk.steps[k] = t := by
    simpa only [List.getElem?_eq_getElem hkr, Option.some.injEq] using ht
  have hdl : (m.left.walk.drop k).steps = s :: w.steps := by
    change m.left.walk.steps.drop k = _
    rw [List.drop_eq_getElem_cons hkl, hsval]
    rfl
  have hdr : (m.right.walk.drop k).steps = t :: z.steps := by
    change m.right.walk.steps.drop k = _
    rw [List.drop_eq_getElem_cons hkr, htval]
    rfl
  have hcs := h.constraint_first_copies hc hs ht
  have hst : m.older.stamp s.1 = c.2 := congrArg Prod.snd hcs.1
  have htt : m.older.stamp t.1 = c.2 := congrArg Prod.snd hcs.2
  have hwstart : w.start = s.2.var := by
    change (m.left.walk.take (k + 1)).finish = _
    simpa only [hsval] using Walk.finish_take_succ m.left.walk hkl
  have hnew : (outArc m.older.stamp s).reverse ∈ R.arcs :=
    mem_reroot_arcs.mpr (Or.inl rfl)
  have hbase : s.2.var ∈ R.vars := (hR.supported _ hnew).1
  have hwlt : ∀ u ∈ w.steps, c.2 < m.older.stamp u.1 := by
    have hp := (h.expansion.grown.ancestry_chronological m.current.input.var).sublist
      (List.drop_sublist k _)
    change ((m.left.walk.drop k).steps).Pairwise _ at hp
    rw [hdl] at hp
    intro u hu
    exact hst ▸ (List.pairwise_cons.mp hp).1 u hu
  have hzlt : ∀ u ∈ z.steps, c.2 < m.older.stamp u.1 := by
    have hp := (h.expansion.grown.ancestry_chronological m.output.var).sublist
      (List.drop_sublist k _)
    change ((m.right.walk.drop k).steps).Pairwise _ at hp
    rw [hdr] at hp
    intro u hu
    exact htt ▸ (List.pairwise_cons.mp hp).1 u hu
  have hsm : s ∈ m.left.walk.steps := by
    have hh : s ∈ (m.left.walk.drop k).steps := by rw [hdl]; exact List.mem_cons_self
    exact List.mem_of_mem_drop hh
  have hlate : c.2 < m.older.length := by
    have hh := (m.older.mem_arcs (h.expansion.grown.ancestry_arcs _ hsm).1).2
    change m.older.stamp s.1 < m.older.length at hh
    exact hst ▸ hh
  have hsurvive : ∀ a ∈ (m.forkDAG k).arcs, c.2 < a.time → a ∈ R.arcs := by
    intro a ha hl
    apply mem_reroot_arcs.mpr
    refine Or.inr ⟨ha, ?_, ?_⟩
    · intro he
      have hh := congrArg Arc.time he
      change a.time = m.older.stamp s.1 at hh
      omega
    · intro he
      have hh := congrArg Arc.time he
      change a.time = m.older.stamp s.1 at hh
      omega
  have hleftU : ∀ u ∈ w.steps,
      inArc m.older.stamp u ∈ (m.forkDAG k).arcs ∧
      outArc m.older.stamp u ∈ (m.forkDAG k).arcs := by
    intro u hu
    have hm : u ∈ (m.left.walk.drop k).steps := by rw [hdl]; exact List.mem_cons_of_mem s hu
    constructor <;> apply (mem_forkDAG_arcs _ _ _).mpr <;>
      exact Or.inl (Finset.mem_biUnion.mpr ⟨u, List.mem_toFinset.mpr hm, by simp⟩)
  have hrightU : ∀ u ∈ z.steps,
      inArc m.older.stamp u ∈ (m.forkDAG k).arcs ∧
      outArc m.older.stamp u ∈ (m.forkDAG k).arcs := by
    intro u hu
    have hm : u ∈ (m.right.walk.drop k).steps := by rw [hdr]; exact List.mem_cons_of_mem t hu
    constructor <;> apply (mem_forkDAG_arcs _ _ _).mpr <;>
      exact Or.inr (Or.inl (Finset.mem_biUnion.mpr ⟨u, List.mem_toFinset.mpr hm, by simp⟩))
  have hrightPort : outArc m.older.stamp t ∈ R.arcs := by
    apply mem_reroot_arcs.mpr
    refine Or.inr ⟨?_, ?_, ?_⟩
    · apply (mem_forkDAG_arcs _ _ _).mpr
      exact Or.inr (Or.inl (Finset.mem_biUnion.mpr ⟨t,
        List.mem_toFinset.mpr (by rw [hdr]; exact List.mem_cons_self), by simp⟩))
    · intro he
      have hh := congrArg Arc.incoming he
      cases hh
    · intro he
      exact h.constraint_children_ne hc hs ht (congrArg (fun a : Arc F => a.occurrence.var) he).symm
  apply hR.subgraph (S := blossomDAG _ _ _) ?_ (blossomDAG_supported _ _ _)
  apply blossomDAG_subgraph_of_arcs _ _ _ (by change w.start ∈ R.vars; rwa [hwstart]) hR.supported
  intro a ham
  have hlen :
      (w.steps.map (fun u => m.older.stamp u.1) ++ [m.older.length] ++
        (z.steps.map fun u => m.older.stamp u.1).reverse).length =
      ((w.snoc m.current.input m.output).append z.reverse).steps.length := by
    simp only [Walk.append, Walk.snoc, Walk.reverse, List.length_append, List.length_map,
      List.length_reverse, List.length_singleton]
  have hpivot : w.steps.length + 1 ≤
      ((w.snoc m.current.input m.output).append z.reverse).steps.length := by
    simp only [Walk.append, Walk.snoc, Walk.reverse, List.length_append, List.length_map,
      List.length_reverse, List.length_singleton]
    omega
  change a ∈ blossomArcs
    (((w.snoc m.current.input m.output).append z.reverse).steps ++ [(t.2, s.2)])
    ((w.steps.map (fun u => m.older.stamp u.1) ++ [m.older.length] ++
      (z.steps.map fun u => m.older.stamp u.1).reverse) ++ [c.2]) (w.steps.length + 1) at ham
  rw [blossomArcs_append_after _ _ _ hlen hpivot] at ham
  rcases List.mem_append.mp ham with ham | ham
  · have hclass := blossomArcs_meeting_mem m.older.stamp m.older.stamp w.steps z.steps
      m.current.input m.output m.older.length (by
        simpa only [Walk.append, Walk.snoc, Walk.reverse, List.append_assoc, List.singleton_append]
          using ham)
    rcases hclass with ⟨u, hu, rfl | rfl⟩ | rfl | rfl | ⟨u, hu, rfl | rfl⟩
    · exact hsurvive _ (hleftU u hu).1 (hwlt u hu)
    · exact hsurvive _ (hleftU u hu).2 (hwlt u hu)
    · exact hsurvive _ ((mem_forkDAG_arcs _ _ _).mpr (Or.inr (Or.inr (Or.inl rfl)))) hlate
    · exact hsurvive _ ((mem_forkDAG_arcs _ _ _).mpr (Or.inr (Or.inr (Or.inr rfl)))) hlate
    · exact hsurvive _ (hrightU u hu).1 (hzlt u hu)
    · exact hsurvive _ (hrightU u hu).2 (hzlt u hu)
  · rcases (show a = ⟨t.2, c.2, false⟩ ∨ a = ⟨s.2, c.2, true⟩ by simpa using ham) with rfl | rfl
    · simpa only [outArc, htt] using hrightPort
    · simpa only [Arc.reverse, outArc, hst, Bool.not_false] using hnew

/-- Past the common prefix, joining the two actual ancestral suffixes at the terminal
pair gives an incidence trail. This applies to both LCA branches. -/
theorem Trace.drop_join_isWalk (h : Trace sem f m) (hF : EdgeInstance F)
    (hf : ValidLabeling sem f) (k : ℕ) (hk : m.commonNodes.length < 2 * k + 2) :
    (((m.left.walk.drop k).snoc m.current.input m.output).append
      (m.right.walk.drop k).reverse).IsWalk := by
  have hT := h.pruned_isFDAG hF hf
  have hw := h.left_directed.drop hT.supported k
  have hz := h.right_directed.drop hT.supported k
  have hsub : (pathDAG (m.right.walk.drop k) m.older.stamp).copies ⊆
      (pathDAG m.right.walk m.older.stamp).copies := by
    intro c hc
    obtain ⟨s, hs, he⟩ := hz.mem_copies.mp hc
    exact h.right_directed.mem_copies.mpr ⟨s, List.mem_of_mem_drop hs, he⟩
  have hd := (h.left_drop_disjoint_right k hk).mono_right hsub
  have hpair := (mem_partners sem f _ _).mp h.partner
  have hused : ∀ v n o, o ∈ ((m.older.ancestry v).walk.drop n).edges → o ∈ m.older.used := by
    intro v n o ho
    exact m.older.ancestry_edges_subset v
      (((List.drop_sublist n (m.older.ancestry v).walk.steps).flatMap
        (fun s => [s.1, s.2])).subset ho)
  apply hw.walk.join_meeting hz.walk
    (by simp only [Walk.finish_drop, Meeting.left, Log.ancestry_finish])
    (by simp only [Walk.finish_drop, Meeting.right, Log.ancestry_finish]) hpair.1
    (fun he => hpair.2.1 (congrArg Occurrence.var he)) (hw.disjoint_edges hz hT hd)
  · exact fun ho => h.expansion.unused (hused _ _ _ ho)
  · exact fun ho => h.output_unused (hused _ _ _ ho)
  · exact fun ho => h.expansion.unused (hused _ _ _ ho)
  · exact fun ho => h.output_unused (hused _ _ _ ho)

/-- The constraint-LCA branch closes its joined suffixes through the two distinct,
fresh LCA child incidences. No incidence is repeated by the resulting closed trail. -/
theorem Trace.constraint_cycle_isWalk (h : Trace sem f m) (hF : EdgeInstance F)
    (hf : ValidLabeling sem f) {c : Copy F} (hc : m.ancestor? = some (.inr c))
    {s t : Occurrence F × Occurrence F}
    (hs : m.left.walk.steps[(m.commonNodes.length - 1) / 2]? = some s)
    (ht : m.right.walk.steps[(m.commonNodes.length - 1) / 2]? = some t) :
    let k := (m.commonNodes.length - 1) / 2
    ((((m.left.walk.drop (k + 1)).snoc m.current.input m.output).append
      (m.right.walk.drop (k + 1)).reverse).snoc t.2 s.2).IsWalk := by
  let k := (m.commonNodes.length - 1) / 2
  let w := m.left.walk.drop (k + 1)
  let z := m.right.walk.drop (k + 1)
  have hkl : k < m.left.walk.steps.length := (m.ancestor_constraint_index_lt hc).1
  have hkr : k < m.right.walk.steps.length := (m.ancestor_constraint_index_lt hc).2
  change m.left.walk.steps[k]? = some s at hs
  change m.right.walk.steps[k]? = some t at ht
  have hsval : m.left.walk.steps[k] = s := by
    simpa only [List.getElem?_eq_getElem hkl, Option.some.injEq] using hs
  have htval : m.right.walk.steps[k] = t := by
    simpa only [List.getElem?_eq_getElem hkr, Option.some.injEq] using ht
  have hcs := h.constraint_first_copies hc hs ht
  have hsm : s ∈ m.left.walk.steps := hsval ▸ List.getElem_mem hkl
  have htm : t ∈ m.right.walk.steps := htval ▸ List.getElem_mem hkr
  have hT := h.pruned_isFDAG hF hf
  have hw := h.left_directed.drop hT.supported (k + 1)
  have hz := h.right_directed.drop hT.supported (k + 1)
  have hbound : m.commonNodes.length < 2 * (k + 1) + 2 := by
    have hl := m.ancestor_constraint_length hc
    change m.commonNodes.length = 2 * k + 2 at hl
    omega
  have hj : ((w.snoc m.current.input m.output).append z.reverse).IsWalk :=
    h.drop_join_isWalk hF hf (k + 1) hbound
  have hleftlate : ∀ u ∈ w.steps, c.2 < m.older.stamp u.1 := by
    have hp := (h.expansion.grown.ancestry_chronological m.current.input.var).sublist
      (List.drop_sublist k _)
    have hd : m.left.walk.steps.drop k = s :: w.steps := by
      rw [List.drop_eq_getElem_cons hkl, hsval]
      rfl
    change (m.left.walk.steps.drop k).Pairwise _ at hp
    rw [hd] at hp
    exact fun u hu => congrArg Prod.snd hcs.1 ▸ (List.pairwise_cons.mp hp).1 u hu
  have hrightlate : ∀ u ∈ z.steps, c.2 < m.older.stamp u.1 := by
    have hp := (h.expansion.grown.ancestry_chronological m.output.var).sublist
      (List.drop_sublist k _)
    have hd : m.right.walk.steps.drop k = t :: z.steps := by
      rw [List.drop_eq_getElem_cons hkr, htval]
      rfl
    change (m.right.walk.steps.drop k).Pairwise _ at hp
    rw [hd] at hp
    exact fun u hu => congrArg Prod.snd hcs.2 ▸ (List.pairwise_cons.mp hp).1 u hu
  have hsa := h.left_directed.outgoing s hsm
  have hta := h.right_directed.outgoing t htm
  have hsused : s.2 ∈ m.older.used :=
    m.older.ancestry_edges_subset _ (List.mem_flatMap.mpr ⟨s, hsm, by simp⟩)
  have htused : t.2 ∈ m.older.used :=
    m.older.ancestry_edges_subset _ (List.mem_flatMap.mpr ⟨t, htm, by simp⟩)
  have hnot : ∀ a ∈ m.prunedDAG.arcs, a.time = c.2 → a.occurrence ∈ m.older.used →
      a.occurrence ∉ ((w.snoc m.current.input m.output).append z.reverse).edges := by
    intro a ha hat hau ho
    rw [Walk.edges_append, Walk.edges_reverse] at ho
    have haw := hw.occurrence_not_mem_of_earlier hT ha (by simpa only [hat] using hleftlate)
    have haz := hz.occurrence_not_mem_of_earlier hT ha (by simpa only [hat] using hrightlate)
    rcases List.mem_append.mp ho with ho | ho
    · change a.occurrence ∈ Walk.edgesOf (w.steps ++ [(m.current.input, m.output)]) at ho
      rw [Walk.edgesOf_append] at ho
      rcases List.mem_append.mp ho with ho | ho
      · exact haw ho
      · rcases (show a.occurrence = m.current.input ∨ a.occurrence = m.output by
          simpa [Walk.edgesOf] using ho) with he | he
        · exact h.expansion.unused (he ▸ hau)
        · exact h.output_unused (he ▸ hau)
    · exact haz (List.mem_reverse.mp ho)
  apply hj.snoc
  · rw [Walk.finish_join_meeting _ _ _ _ hz.walk.1
      (by simp only [Walk.finish_drop, Meeting.right, Log.ancestry_finish])]
    change t.2.var = (m.right.walk.take (k + 1)).finish
    rw [Walk.finish_take_succ _ hkr, htval]
  · have hl := h.left_directed.walk.1
    have hr := h.right_directed.walk.1
    obtain ⟨pre, post, he⟩ := List.mem_iff_append.mp hsm
    rw [he, Walk.linked_append_iff] at hl
    obtain ⟨pre', post', he'⟩ := List.mem_iff_append.mp htm
    rw [he', Walk.linked_append_iff] at hr
    exact hr.2.2.1.symm.trans ((congrArg Prod.fst hcs.2).trans
      ((congrArg Prod.fst hcs.1).symm.trans hl.2.2.1))
  · exact fun he => h.constraint_children_ne hc hs ht (congrArg Occurrence.var he).symm
  · exact hnot (outArc m.older.stamp t) hta (congrArg Prod.snd hcs.2) htused
  · exact hnot (outArc m.older.stamp s) hsa (congrArg Prod.snd hcs.1) hsused

/-- The raw constraint-LCA extractor supplies precisely the rerooted cycle just proved
to be an f-DAG, with its actual timestamps and child incidences. -/
theorem Trace.constraint_blossom_isFDAG (h : Trace sem f m) (hF : EdgeInstance F)
    (hf : ValidLabeling sem f) (hM : EdgeInstance.EvenConstraints sem F)
    {c : Copy F} (hc : m.ancestor? = some (.inr c)) {b : BlossomData F}
    (hb : m.blossomData = some b) :
    (blossomDAG b.cycle b.times b.pivot).IsFDAG sem (b.prepare.flip f) := by
  simp only [blossomData, hc] at hb
  split at hb
  next ain lp bin rp hs ht =>
    cases hb
    let k := (m.commonNodes.length - 1) / 2
    have hkl := (m.ancestor_constraint_index_lt hc).1
    have hkr := (m.ancestor_constraint_index_lt hc).2
    have hsl : m.left.walk.steps[k] = (ain, lp) := by
      simpa only [List.getElem?_eq_getElem hkl, Option.some.injEq] using hs
    have hsr : m.right.walk.steps[k] = (bin, rp) := by
      simpa only [List.getElem?_eq_getElem hkr, Option.some.injEq] using ht
    have hleft : (⟨lp.var, m.left.walk.steps.drop (k + 1)⟩ : Walk F) =
        m.left.walk.drop (k + 1) := by
      unfold Walk.drop
      rw [Walk.finish_take_succ _ hkl, hsl]
    have hright : (⟨rp.var, m.right.walk.steps.drop (k + 1)⟩ : Walk F) =
        m.right.walk.drop (k + 1) := by
      unfold Walk.drop
      rw [Walk.finish_take_succ _ hkr, hsr]
    have htl : m.left.times.drop (k + 1) = (m.left.walk.drop (k + 1)).steps.map
        (fun s => m.older.stamp s.1) := by
      simpa only [Meeting.left, Walk.drop, List.map_drop] using congrArg (List.drop (k + 1))
        (h.expansion.grown.ancestry_times_eq_stamp m.current.input.var)
    have htr : m.right.times.drop (k + 1) = (m.right.walk.drop (k + 1)).steps.map
        (fun s => m.older.stamp s.1) := by
      simpa only [Meeting.right, Walk.drop, List.map_drop] using congrArg (List.drop (k + 1))
        (h.expansion.grown.ancestry_times_eq_stamp m.output.var)
    dsimp only
    rw [hleft, hright, htl, htr]
    simpa only [Walk.drop] using
      h.constraint_cycle_isFDAG hF hf hM hc (s := (ain, lp)) (t := (bin, rp)) hs ht
  · cases hb

/-- Both LCA branches return the full timestamped f-DAG required in Definition 39,
under the labeling obtained by their actual preparatory root-path flip. -/
theorem Trace.blossom_isFDAG (h : Trace sem f m) (hF : EdgeInstance F)
    (hf : ValidLabeling sem f) (hM : EdgeInstance.EvenConstraints sem F)
    {b : BlossomData F} (hb : m.blossomData = some b) :
    (blossomDAG b.cycle b.times b.pivot).IsFDAG sem (b.prepare.flip f) := by
  cases ha : m.ancestor? with
  | none => simp [blossomData, ha] at hb
  | some a =>
    cases a with
    | inl v => exact h.variable_blossom_isFDAG hF hf hM ha hb
    | inr c => exact h.constraint_blossom_isFDAG hF hf hM ha hb

/-- Joining suffixes of actual ancestries preserves original internal consistency.
Reversal is used here only for internal consistency, not for f-walk prefix validity. -/
theorem Trace.drop_join_consistent (h : Trace sem f m) (k : ℕ) :
    Walk.InternallyConsistent f
      (((m.left.walk.drop k).snoc m.current.input m.output).append
        (m.right.walk.drop k).reverse).steps := by
  have hg : Grown sem f (Forest.roots f) m.older := h.roots_eq ▸ h.expansion.grown
  have hrc : Walk.InternallyConsistent f (m.right.walk.drop k).steps := by
    change Walk.InternallyConsistent f (m.right.walk.steps.drop k)
    simpa only [List.append_nil, Meeting.right] using Walk.InternallyConsistent.append_of_outputs
      (ts := []) (fun s hs => hg.ancestry_output_consistent _ (List.mem_of_mem_drop hs)) trivial
  have htail : Walk.InternallyConsistent f
      ((m.current.input, m.output) :: (m.right.walk.drop k).reverse.steps) := by
    refine ⟨?_, hrc.reverse (h.right_directed.walk.drop k).1⟩
    by_cases hz : (m.right.walk.drop k).steps = []
    · exact Or.inl (by simp [Walk.reverse, hz])
    · have hn : m.right.walk.steps ≠ [] := by
        intro he
        exact hz (by simp [Walk.drop, he])
      exact Or.inr (hg.ancestry_finish_consistent hn)
  change Walk.InternallyConsistent f
    (((m.left.walk.drop k).steps ++ [(m.current.input, m.output)]) ++
      (m.right.walk.drop k).reverse.steps)
  rw [List.append_assoc]
  exact Walk.InternallyConsistent.append_of_outputs
    (fun s hs => hg.ancestry_output_consistent _ (List.mem_of_mem_drop hs)) htail

/-- The actual cycle in either branch is internally consistent under the original
labeling. Only its base can be inconsistent after preparation. -/
theorem Trace.blossom_original_consistent (h : Trace sem f m) {b : BlossomData F}
    (hb : m.blossomData = some b) : Walk.InternallyConsistent f b.cycle.steps := by
  unfold blossomData at hb
  split at hb
  · cases hb
  next a ha =>
    cases a with
    | inl v => cases hb; exact h.drop_join_consistent _
    | inr c =>
      dsimp only at hb
      split at hb
      next ain lp bin rp hs ht =>
        cases hb
        let k := (m.commonNodes.length - 1) / 2
        have hkr := (m.ancestor_constraint_index_lt ha).2
        have htr : m.right.walk.steps[k] = (bin, rp) := by
          simpa only [List.getElem?_eq_getElem hkr, Option.some.injEq] using ht
        have htm : (bin, rp) ∈ m.right.walk.steps := htr ▸ List.getElem_mem hkr
        have hg : Grown sem f (Forest.roots f) m.older := h.roots_eq ▸ h.expansion.grown
        have hcons : ¬ Inconsistent f rp.var := hg.ancestry_output_consistent _ htm
        have hzstart : (m.right.walk.drop (k + 1)).start = rp.var := by
          change (m.right.walk.take (k + 1)).finish = _
          rw [Walk.finish_take_succ _ hkr]
          exact congrArg (fun s => s.2.var) htr
        have hj := h.drop_join_consistent (k + 1)
        apply hj.snoc ((m.left.walk.drop (k + 1)).start) rp lp (Or.inr ?_)
        change ¬ Inconsistent f
          (((m.left.walk.drop (k + 1)).snoc m.current.input m.output).append
            (m.right.walk.drop (k + 1)).reverse).finish
        rw [Walk.finish_join_meeting _ _ _ _ (h.right_directed.walk.drop (k + 1)).1
          (by simp only [Walk.finish_drop, Meeting.right, Log.ancestry_finish]), hzstart]
        exact hcons
      · cases hb

/-- Both actual LCA cycles are closed incidence trails, including the final pair of
fresh LCA child ports in the copied-constraint branch. -/
theorem Trace.blossom_cycle_isWalk (h : Trace sem f m) (hF : EdgeInstance F)
    (hf : ValidLabeling sem f) {b : BlossomData F} (hb : m.blossomData = some b) :
    b.cycle.IsWalk := by
  unfold blossomData at hb
  split at hb
  · cases hb
  next a ha =>
    cases a with
    | inl v =>
      cases hb
      let k := (m.commonNodes.length - 1) / 2
      have hp := m.ancestor_variable_prefix ha
      have hl : (⟨v, m.left.walk.steps.drop k⟩ : Walk F) = m.left.walk.drop k := by
        unfold Walk.drop
        rw [hp.1]
      have hr : (⟨v, m.right.walk.steps.drop k⟩ : Walk F) = m.right.walk.drop k := by
        unfold Walk.drop
        rw [hp.2]
      dsimp only
      rw [hl, hr]
      apply h.drop_join_isWalk hF hf
      have hh := m.ancestor_variable_length ha
      change m.commonNodes.length = 2 * k + 1 at hh
      omega
    | inr c =>
      dsimp only at hb
      split at hb
      next ain lp bin rp hs ht =>
        cases hb
        let k := (m.commonNodes.length - 1) / 2
        have hkl := (m.ancestor_constraint_index_lt ha).1
        have hkr := (m.ancestor_constraint_index_lt ha).2
        have hsl : m.left.walk.steps[k] = (ain, lp) := by
          simpa only [List.getElem?_eq_getElem hkl, Option.some.injEq] using hs
        have hsr : m.right.walk.steps[k] = (bin, rp) := by
          simpa only [List.getElem?_eq_getElem hkr, Option.some.injEq] using ht
        have hl : (⟨lp.var, m.left.walk.steps.drop (k + 1)⟩ : Walk F) =
            m.left.walk.drop (k + 1) := by
          unfold Walk.drop
          rw [Walk.finish_take_succ _ hkl, hsl]
        have hr : (⟨rp.var, m.right.walk.steps.drop (k + 1)⟩ : Walk F) =
            m.right.walk.drop (k + 1) := by
          unfold Walk.drop
          rw [Walk.finish_take_succ _ hkr, hsr]
        dsimp only
        rw [hl, hr]
        exact h.constraint_cycle_isWalk hF hf ha hs ht
      · cases hb

/-- Every returned preparatory walk is an actual prefix of the left root ancestry. -/
theorem blossom_prepare_prefix {b : BlossomData F} (hb : m.blossomData = some b) :
    ∃ n, b.prepare = m.left.walk.take n := by
  unfold blossomData at hb
  split at hb
  · cases hb
  next a ha =>
    cases a with
    | inl v => cases hb; exact ⟨_, rfl⟩
    | inr c =>
      dsimp only at hb
      split at hb
      · cases hb; exact ⟨_, rfl⟩
      · cases hb

/-- The preparatory root path ends at the base of the actual returned cycle. -/
theorem blossom_prepare_finish {b : BlossomData F} (hb : m.blossomData = some b) :
    b.prepare.finish = b.cycle.start := by
  unfold blossomData at hb
  split at hb
  · cases hb
  next a ha =>
    cases a with
    | inl v =>
      cases hb
      exact (m.ancestor_variable_prefix ha).1
    | inr c =>
      dsimp only at hb
      split at hb
      next ain lp bin rp hs ht =>
        cases hb
        have hk := (m.ancestor_constraint_index_lt ha).1
        have he : m.left.walk.steps[(m.commonNodes.length - 1) / 2] = (ain, lp) := by
          simpa only [List.getElem?_eq_getElem hk, Option.some.injEq] using hs
        change (m.left.walk.take ((m.commonNodes.length - 1) / 2 + 1)).finish = lp.var
        simpa only [he] using Walk.finish_take_succ m.left.walk hk
      · cases hb

/-- Timestamp and pivot metadata from either extractor branch have exactly the lengths
needed for its two-arm cycle, and the terminal meeting step is present. -/
theorem blossom_metadata {b : BlossomData F} (hb : m.blossomData = some b) :
    b.times.length = b.cycle.steps.length ∧ 0 < b.pivot ∧ b.pivot ≤ b.cycle.steps.length := by
  have hl := m.older.ancestry_length m.current.input.var
  have hr := m.older.ancestry_length m.output.var
  change m.left.times.length = m.left.walk.steps.length at hl
  change m.right.times.length = m.right.walk.steps.length at hr
  unfold blossomData at hb
  split at hb
  · cases hb
  next a ha =>
    cases a with
    | inl v =>
      cases hb
      simp only [Walk.append, Walk.snoc, Walk.reverse, List.length_append, List.length_map,
        List.length_reverse, List.length_singleton, List.length_drop]
      omega
    | inr c =>
      dsimp only at hb
      split at hb
      · cases hb
        simp only [Walk.append, Walk.snoc, Walk.reverse, List.length_append, List.length_map,
          List.length_reverse, List.length_singleton, List.length_drop]
        omega
      · cases hb

private theorem Trace.join_times_nodup (h : Trace sem f m) (k : ℕ)
    (hk : m.commonNodes.length < 2 * k + 2) :
    (m.left.times.drop k ++ [m.older.length] ++ (m.right.times.drop k).reverse).Nodup := by
  have hleft : (m.left.times.drop k).Nodup :=
    ((m.older.ancestry_times_pairwise m.current.input.var).imp
      (fun hlt he => by rw [he] at hlt; exact Nat.lt_irrefl _ hlt)).sublist (List.drop_sublist _ _)
  have hright : (m.right.times.drop k).Nodup :=
    ((m.older.ancestry_times_pairwise m.output.var).imp
      (fun hlt he => by rw [he] at hlt; exact Nat.lt_irrefl _ hlt)).sublist (List.drop_sublist _ _)
  have hfreshL : ∀ t ∈ m.left.times.drop k, t < m.older.length :=
    fun t ht => m.older.ancestry_time_lt _ (List.mem_of_mem_drop ht)
  have hfreshR : ∀ t ∈ m.right.times.drop k, t < m.older.length :=
    fun t ht => m.older.ancestry_time_lt _ (List.mem_of_mem_drop ht)
  have hcross : ∀ t ∈ m.left.times.drop k, ∀ u ∈ m.right.times.drop k, t ≠ u := by
    intro t ht u hu he
    have htl : m.left.times.drop k = (m.left.walk.drop k).steps.map
        (fun s => m.older.stamp s.1) := by
      simpa only [Meeting.left, Walk.drop, List.map_drop] using congrArg (List.drop k)
        (h.expansion.grown.ancestry_times_eq_stamp m.current.input.var)
    have htr : m.right.times.drop k = (m.right.walk.drop k).steps.map
        (fun s => m.older.stamp s.1) := by
      simpa only [Meeting.right, Walk.drop, List.map_drop] using congrArg (List.drop k)
        (h.expansion.grown.ancestry_times_eq_stamp m.output.var)
    rw [htl] at ht
    rw [htr] at hu
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hu
    have hsfull := List.mem_of_mem_drop hs
    have hzfull := List.mem_of_mem_drop hz
    have ha := (h.expansion.grown.ancestry_arcs _ hsfull).1
    have hb := (h.expansion.grown.ancestry_arcs _ hzfull).1
    have hc := congrArg Arc.copy (Log.incoming_time_unique ha hb rfl rfl he)
    have hd := h.left_drop_disjoint_right k hk
    have hw := (h.expansion.grown.ancestry_directed h.expansion.visited).drop
      (m.older.toDAG_supported m.roots) k
    exact Finset.disjoint_left.mp hd (hw.mem_copies.mpr ⟨s, hs, rfl⟩)
      (h.right_directed.mem_copies.mpr ⟨z, hzfull, hc.symm⟩)
  rw [List.nodup_append, List.nodup_append]
  refine ⟨⟨hleft, by simp, ?_⟩, List.nodup_reverse.mpr hright, ?_⟩
  · intro t ht u hu he
    have hu' := List.mem_singleton.mp hu
    exact Nat.ne_of_lt (hfreshL t ht) (he.trans hu')
  · intro t ht u hu he
    have hum := List.mem_reverse.mp hu
    rcases List.mem_append.mp ht with ht | ht
    · exact hcross t ht u hum he
    · have ht' := List.mem_singleton.mp ht
      exact Nat.ne_of_lt (hfreshR u hum) (he.symm.trans ht')

/-- Actual extractor timestamps distinguish every copied cycle step in both LCA branches.
The cross-arm distinction follows from the ancestry common-prefix theorem. Original
constraints may still occur repeatedly, at different timestamps. -/
theorem Trace.blossom_times_nodup (h : Trace sem f m) {b : BlossomData F}
    (hb : m.blossomData = some b) : b.times.Nodup := by
  unfold blossomData at hb
  split at hb
  · cases hb
  next a ha =>
    cases a with
    | inl v =>
      cases hb
      apply h.join_times_nodup
      have hl := m.ancestor_variable_length ha
      omega
    | inr c =>
      dsimp only at hb
      split at hb
      next ain lp bin rp hs ht =>
        cases hb
        let k := (m.commonNodes.length - 1) / 2
        have hkl := (m.ancestor_constraint_index_lt ha).1
        have hkr := (m.ancestor_constraint_index_lt ha).2
        have hcs := h.constraint_first_copies ha hs ht
        have hsl : m.left.walk.steps[k] = (ain, lp) := by
          simpa only [List.getElem?_eq_getElem hkl, Option.some.injEq] using hs
        have hsr : m.right.walk.steps[k] = (bin, rp) := by
          simpa only [List.getElem?_eq_getElem hkr, Option.some.injEq] using ht
        have hkl' : k < m.left.times.length := by
          have hl := m.older.ancestry_length m.current.input.var
          change m.left.times.length = m.left.walk.steps.length at hl
          omega
        have hkr' : k < m.right.times.length := by
          have hl := m.older.ancestry_length m.output.var
          change m.right.times.length = m.right.walk.steps.length at hl
          omega
        have hlt : m.left.times[k] = c.2 := by
          have he := h.expansion.grown.ancestry_times_eq_stamp m.current.input.var
          change m.left.times = m.left.walk.steps.map (fun s => m.older.stamp s.1) at he
          simp only [he, List.getElem_map, hsl]
          exact congrArg Prod.snd hcs.1
        have hrt : m.right.times[k] = c.2 := by
          have he := h.expansion.grown.ancestry_times_eq_stamp m.output.var
          change m.right.times = m.right.walk.steps.map (fun s => m.older.stamp s.1) at he
          simp only [he, List.getElem_map, hsr]
          exact congrArg Prod.snd hcs.2
        have hlateL : ∀ t ∈ m.left.times.drop (k + 1), c.2 < t := by
          have hp := (m.older.ancestry_times_pairwise m.current.input.var).sublist
            (List.drop_sublist k _)
          change (m.left.times.drop k).Pairwise (· < ·) at hp
          rw [List.drop_eq_getElem_cons hkl', hlt] at hp
          exact (List.pairwise_cons.mp hp).1
        have hlateR : ∀ t ∈ m.right.times.drop (k + 1), c.2 < t := by
          have hp := (m.older.ancestry_times_pairwise m.output.var).sublist
            (List.drop_sublist k _)
          change (m.right.times.drop k).Pairwise (· < ·) at hp
          rw [List.drop_eq_getElem_cons hkr', hrt] at hp
          exact (List.pairwise_cons.mp hp).1
        have hlast : c.2 < m.older.length := hlt ▸
          m.older.ancestry_time_lt _ (List.getElem_mem hkl')
        have hbound : m.commonNodes.length < 2 * (k + 1) + 2 := by
          have hl := m.ancestor_constraint_length ha
          change m.commonNodes.length = 2 * k + 2 at hl
          omega
        dsimp only
        apply List.nodup_append.mpr
        refine ⟨h.join_times_nodup (k + 1) hbound, by simp, ?_⟩
        intro t ht u hu he
        have hu' := List.mem_singleton.mp hu
        have hgt : c.2 < t := by
          rcases List.mem_append.mp ht with ht | ht
          · rcases List.mem_append.mp ht with ht | ht
            · exact hlateL t ht
            · exact (List.mem_singleton.mp ht) ▸ hlast
          · exact hlateR t (List.mem_reverse.mp ht)
        exact Nat.ne_of_lt hgt (hu' ▸ he.symm)
      · cases hb

/-- The returned preparatory path is a trail from an originally inconsistent root. -/
theorem Trace.blossom_prepare_isWalk (h : Trace sem f m) {b : BlossomData F}
    (hb : m.blossomData = some b) : b.prepare.IsWalk ∧ Inconsistent f b.prepare.start := by
  obtain ⟨n, hp⟩ := blossom_prepare_prefix hb
  rw [hp]
  refine ⟨h.left_directed.walk.take n, ?_⟩
  apply (mem_roots f _).mp
  rw [← h.roots_eq]
  exact h.expansion.grown.ancestry_start_root h.expansion.visited

/-- A variable LCA of an actual terminal event is a root. Its returned preparatory
path is therefore empty, as specified in source Section 5.3. -/
theorem Trace.variable_prepare_empty (h : Trace sem f m) (hF : EdgeInstance F)
    (hf : ValidLabeling sem f) {v : V} (ha : m.ancestor? = some (.inl v)) :
    (m.left.walk.take ((m.commonNodes.length - 1) / 2)).steps = [] := by
  let k := (m.commonNodes.length - 1) / 2
  let w := m.left.walk.drop k
  let z := m.right.walk.drop k
  have hT := h.pruned_isFDAG hF hf
  have hw := h.left_directed.drop hT.supported k
  have hz := h.right_directed.drop hT.supported k
  have hbase := m.ancestor_variable_prefix ha
  have hbound : m.commonNodes.length < 2 * k + 2 := by
    have hh := m.ancestor_variable_length ha
    change m.commonNodes.length = 2 * k + 1 at hh
    omega
  have hsub : (pathDAG z m.older.stamp).copies ⊆ (pathDAG m.right.walk m.older.stamp).copies := by
    intro c hc
    obtain ⟨s, hs, he⟩ := hz.mem_copies.mp hc
    exact h.right_directed.mem_copies.mpr ⟨s, List.mem_of_mem_drop hs, he⟩
  have hd := (h.left_drop_disjoint_right k hbound).mono_right hsub
  have hab := (mem_partners sem f _ _).mp h.partner
  let a : Arc F := ⟨m.current.input, m.older.length, true⟩
  let b : Arc F := ⟨m.output, m.older.length, true⟩
  have hac : a.copy = m.copy := rfl
  have hbc : b.copy = m.copy := Prod.ext hab.1.symm rfl
  have ham : a ∈ m.prunedDAG.arcs := by rw [h.pruned_arcs]; simp [a]
  have hbm : b ∈ m.prunedDAG.arcs := by rw [h.pruned_arcs]; simp [b]
  have hfirst : ∀ (q : Walk F), DirectedPath m.prunedDAG q m.older.stamp →
      ∀ d ∈ m.prunedDAG.arcs, d.incoming = true → d.occurrence.var = q.finish →
      ∃ e ∈ m.prunedDAG.arcs, e.incoming = true ∧ e.occurrence.var = q.start ∧
        ((e.copy ∈ (pathDAG q m.older.stamp).copies) ∨ e = d) := by
    intro q hq d hdm hdi hdv
    cases he : q.steps with
    | nil =>
      refine ⟨d, hdm, hdi, ?_, Or.inr rfl⟩
      simpa only [Walk.finish, he, Walk.finishFrom] using hdv
    | cons s ss =>
      have hsm : s ∈ q.steps := by rw [he]; exact List.mem_cons_self
      have hlink := hq.walk.1
      rw [he] at hlink
      exact ⟨inArc m.older.stamp s, hq.incoming s hsm, rfl, hlink.1,
        Or.inl (hq.mem_copies.mpr ⟨s, hsm, rfl⟩)⟩
  obtain ⟨x, hxm, hxi, hxv, hxc⟩ := hfirst w hw a ham rfl
    (by change m.current.input.var = (m.left.walk.drop k).finish
        simp only [Walk.finish_drop, Meeting.left, Log.ancestry_finish])
  obtain ⟨y, hym, hyi, hyv, hyc⟩ := hfirst z hz b hbm rfl
    (by change m.output.var = (m.right.walk.drop k).finish
        simp only [Walk.finish_drop, Meeting.right, Log.ancestry_finish])
  have hxbase : x.occurrence.var = v := hxv.trans hbase.1
  have hybase : y.occurrence.var = v := hyv.trans hbase.2
  have hxy : x ≠ y := by
    intro he
    rcases hxc with hxc | rfl <;> rcases hyc with hyc | rfl
    · exact Finset.disjoint_left.mp hd hxc (he.symm ▸ hyc)
    · exact h.copy_fresh h.expansion.visited (by
        obtain ⟨s, hs, hsx⟩ := hw.mem_copies.mp hxc
        exact h.left_directed.mem_copies.mpr
          ⟨s, List.mem_of_mem_drop hs, hsx.trans ((congrArg Arc.copy he).trans hbc)⟩)
    · exact h.copy_fresh h.old_visited (by
        obtain ⟨s, hs, hsy⟩ := hz.mem_copies.mp hyc
        exact h.right_directed.mem_copies.mpr
          ⟨s, List.mem_of_mem_drop hs, hsy.trans ((congrArg Arc.copy he).symm.trans hac)⟩)
    · exact hab.2.1 (congrArg (fun e : Arc F => e.occurrence.var) he)
  by_contra hn
  obtain ⟨s, hs, hsf⟩ := Walk.finish_step (m.left.walk.take k) hn
  have hsm : s ∈ m.left.walk.steps := List.mem_of_mem_take hs
  have hparent := h.left_directed.outgoing s hsm
  have hpv : (outArc m.older.stamp s).occurrence.var = v := hsf.trans hbase.1
  exact hxy (hT.incoming_eq_of_parent hF hparent hxm hym rfl hxi hyi
    (hxbase.trans hpv.symm) (hybase.trans hpv.symm))

/-- A nonempty preparatory path ends at an originally consistent discovered variable. -/
theorem Trace.blossom_prepare_finish_consistent (h : Trace sem f m) {b : BlossomData F}
    (hb : m.blossomData = some b) (hn : b.prepare.steps ≠ []) :
    ¬ Inconsistent f b.prepare.finish := by
  obtain ⟨s, hs, he⟩ := Walk.finish_step b.prepare hn
  obtain ⟨n, hp⟩ := blossom_prepare_prefix hb
  rw [hp] at hs
  have hg : Grown sem f (Forest.roots f) m.older := h.roots_eq ▸ h.expansion.grown
  rw [← he]
  exact hg.ancestry_output_consistent _ (List.mem_of_mem_take hs)

open scoped symmDiff in
/-- Preparation moves the original root defect to the actual cycle base. -/
theorem Trace.blossom_base_inconsistent (h : Trace sem f m) (hF : EdgeInstance F)
    {b : BlossomData F} (hb : m.blossomData = some b) :
    Inconsistent (b.prepare.flip f) b.cycle.start := by
  obtain ⟨hw, hr⟩ := h.blossom_prepare_isWalk hb
  rw [← blossom_prepare_finish hb, ← mem_defects, hw.defects_flip hF]
  by_cases hn : b.prepare.steps = []
  · have he : b.prepare.finish = b.prepare.start := by simp [Walk.finish, hn, Walk.finishFrom]
    simp [he, mem_defects, hr]
  · have hc := h.blossom_prepare_finish_consistent hb hn
    have he : b.prepare.finish ≠ b.prepare.start := fun he => hc (he.symm ▸ hr)
    simp [Finset.mem_symmDiff, mem_defects, hc, he]

open scoped symmDiff in
/-- Preparatory root-path flipping preserves the number of defects. This is the
counting interface needed before contracting the returned blossom. -/
theorem Trace.blossom_prepare_card_defects (h : Trace sem f m) (hF : EdgeInstance F)
    {b : BlossomData F} (hb : m.blossomData = some b) :
    (defects (b.prepare.flip f)).card = (defects f).card := by
  obtain ⟨hw, hr⟩ := h.blossom_prepare_isWalk hb
  rw [hw.defects_flip hF]
  by_cases hn : b.prepare.steps = []
  · have he : b.prepare.finish = b.prepare.start := by simp [Walk.finish, hn, Walk.finishFrom]
    simp [he]
  · have hc := h.blossom_prepare_finish_consistent hb hn
    have hrm := mem_defects.mpr hr
    have hcm := mem_defects.not.mpr hc
    rw [Finset.symmDiff_singleton_eq (defects f) b.prepare.start, ite_eq_left hrm]
    have he : b.prepare.finish ∉ (defects f).erase b.prepare.start :=
      fun hm => hcm (Finset.mem_of_mem_erase hm)
    rw [Finset.symmDiff_singleton_eq, ite_eq_right he, Finset.card_insert_of_notMem he]
    exact Finset.card_erase_add_one hrm

/-- Source Lemma 41, arXiv:1602.03124v6, printed pp. 19–20: the actual returned cycle
is a Definition 39 blossom after the actual preparatory path is flipped. The alternative
proof transfers the later fork through chronological prefix flips, then uses Lemma 37
rerooting at a constraint LCA. No correctness premise is added to the raw extractor. -/
theorem Trace.blossom_correct (h : Trace sem f m) (hF : EdgeInstance F)
    (hf : ValidLabeling sem f) (hM : EdgeInstance.EvenConstraints sem F)
    {b : BlossomData F} (hb : m.blossomData = some b) :
    b.cycle.IsBlossom sem (b.prepare.flip f) := by
  have hw := h.blossom_cycle_isWalk hF hf hb
  have hm := blossom_metadata hb
  refine ⟨hw, h.blossom_cycle_closed hb, ?_, h.blossom_base_inconsistent hF hb, ?_,
    b.times, b.pivot, b.cycle.distinctCopies_of_nodup_times hm.1
      (h.blossom_times_nodup hb), hm.2.1, hm.2.2, ?_⟩
  · intro he
    have hh := hm.2.2
    rw [he, List.length_nil] at hh
    omega
  · exact hw.internallyConsistent_flip hF (h.blossom_prepare_isWalk hb).1 f
      (blossom_prepare_finish hb) (h.blossom_prepare_isWalk hb).2
      (h.blossom_original_consistent hb)
  · have he : (inferInstance : DecidableEq V) = Classical.decEq V := Subsingleton.elim _ _
    rw [← he]
    exact h.blossom_isFDAG hF hf hM hb

end Cslib.Logic.PL.CSP.Forest.Meeting

namespace Cslib.Logic.PL.CSP.Forest

variable {Rel V : Type*} {F : CSP Rel V} [DecidableEq V]

/-- Fresh-run blossom correctness, including source-strength cycle validity, validity of
the preparatory labeling, and preservation of its defect count. The only search premise
is the actual result equation; all forest and event invariants are derived from the run. -/
theorem search_blossom_correct (sem : Rel → List Bool → Bool)
    (f : OccurrenceLabeling F Bool) (hF : EdgeInstance F) (hf : ValidLabeling sem f)
    (hM : EdgeInstance.EvenConstraints sem F) {m : Meeting F}
    (hr : search sem f = .blossom m) :
    ∃ b, m.blossomData = some b ∧ b.cycle.IsBlossom sem (b.prepare.flip f) ∧
      ValidLabeling sem (b.prepare.flip f) ∧
      (defects (b.prepare.flip f)).card = (defects f).card := by
  have ht := search_trace sem f hF
  rw [hr] at ht
  have he := run_event_roots sem f (Forest.roots f) [] (incidenceList F)
  change (search sem f).Classified at he
  rw [hr] at he
  have hs := m.blossomData_isSome he
  cases hb : m.blossomData with
  | none => simp [hb] at hs
  | some b =>
    exact ⟨b, rfl, ht.blossom_correct hF hf hM hb, ht.blossom_prepare_valid hF hf hM hb,
      ht.blossom_prepare_card_defects hF hb⟩

end Cslib.Logic.PL.CSP.Forest
