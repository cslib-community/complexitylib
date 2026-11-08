/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CSP.Edge.DAGSurgery

/-!
# Directed f-DAG paths and positional walks

Corollary 36 of [KazdaKolmogorovRolinek2018], arXiv v6, printed p. 17, is connected
to the existing `Walk` representation. A directed path certificate supplies actual indexed
arcs and excludes repeated *copied* constraint nodes. Original constraint positions may recur
at different timestamps. Its proper prefixes inherit the same graph certificate, so all
variable-ended prefix flips are proved valid. Endpoint inequality and internal consistency
are explicit additional hypotheses for `Walk.IsFWalk`; neither is part of Definition 32.

For the two meeting paths in part (1), take their variable-ended portions as `w,z` and their
final incoming arcs as `a,b`. `valid_flip_meeting` proves validity of the union incidence flip.
Its graph argument is stronger: only disjointness of copied constraint supports and freshness
of the terminal copy are needed, with at least one incoming terminal arc. No claim about
prefix validity under arbitrary path reversal is made.

## Main results

* `DirectedPath.valid_flip`, `DirectedPath.valid_take`: path and prefix flip validity.
* `DirectedPath.isFWalk`: the bridge with endpoint and internal-consistency hypotheses explicit.
* `DirectedPath.valid_flip_meeting`: the two-path incidence flip of Corollary 36(1).
-/

public section

namespace Cslib.Logic.PL.CSP.DAG

open BitString Finset

variable {Rel V : Type*} {F : CSP Rel V}

/-- Stamp the incoming incidence of one positional walk step. -/
@[expose] def inArc (time : Occurrence F → ℕ) (s : Occurrence F × Occurrence F) : Arc F :=
  ⟨s.1, time s.1, true⟩

/-- Stamp the outgoing incidence at the same copied constraint as the step's incoming port. -/
@[expose] def outArc (time : Occurrence F → ℕ) (s : Occurrence F × Occurrence F) : Arc F :=
  ⟨s.2, time s.1, false⟩

/-- The directed arcs traversed by a stamped positional walk. -/
@[expose] def pathArcs (w : Walk F) (time : Occurrence F → ℕ) : Finset (Arc F) :=
  w.steps.toFinset.biUnion fun s => {inArc time s, outArc time s}

section

variable [DecidableEq V]

/-- The finite incidence graph of a stamped path, retaining its length-zero starting root. -/
@[expose] def pathDAG (w : Walk F) (time : Occurrence F → ℕ) : DAG F where
  vars := insert w.start ((pathArcs w time).image fun e => e.occurrence.var)
  copies := (pathArcs w time).image Arc.copy
  arcs := pathArcs w time

/-- A directed incidence path certificate. Copied nodes do not recur; original constraints can.
No validity or surgery conclusion is assumed. The path's existing `IsWalk` records positional
adjacency and nonreuse of original incidences. -/
structure DirectedPath (T : DAG F) (w : Walk F) (time : Occurrence F → ℕ) : Prop where
  /-- The underlying sequence is a linked incidence trail. -/
  walk : w.IsWalk
  /-- The initial variable belongs to the graph, also when the path has length zero. -/
  start_mem : w.start ∈ T.vars
  /-- Each step's first port is an incoming graph arc. -/
  incoming : ∀ s ∈ w.steps, inArc time s ∈ T.arcs
  /-- Each step's second port is an outgoing graph arc at the same timestamp. -/
  outgoing : ∀ s ∈ w.steps, outArc time s ∈ T.arcs
  /-- A copied constraint node occurs in only one step. -/
  copies_injective : ∀ s ∈ w.steps, ∀ t ∈ w.steps,
    (inArc time s).copy = (inArc time t).copy → s = t

omit [DecidableEq V] in
private theorem linked_constraint {v : V} {ss : List (Occurrence F × Occurrence F)}
    (h : Walk.Linked v ss) {s : Occurrence F × Occurrence F} (hs : s ∈ ss) : s.1.1 = s.2.1 := by
  induction ss generalizing v with
  | nil => simp at hs
  | cons t ss ih =>
    simp only [List.mem_cons] at hs
    rcases hs with rfl | hs
    · exact h.2.1
    · exact ih h.2.2 hs

/-- A path graph retains exactly its actual supported incidences and copied nodes. -/
theorem pathDAG_supported (w : Walk F) (time : Occurrence F → ℕ) :
    (pathDAG w time).Supported := by
  intro e he
  exact ⟨mem_insert_of_mem (mem_image.mpr ⟨e, he, rfl⟩), mem_image.mpr ⟨e, he, rfl⟩⟩

/-- A stamped directed path determines a supported subgraph of its ambient DAG. -/
theorem DirectedPath.subgraph {T : DAG F} {w : Walk F} {time : Occurrence F → ℕ}
    (hp : DirectedPath T w time) (hs : T.Supported) : (pathDAG w time).Subgraph T := by
  have harcs : pathArcs w time ⊆ T.arcs := by
    intro e hem
    obtain ⟨s, hsm, he⟩ := mem_biUnion.mp hem
    have hsm' := List.mem_toFinset.mp hsm
    rcases (show e = inArc time s ∨ e = outArc time s from by
      simpa only [mem_insert, mem_singleton] using he) with rfl | rfl
    · exact hp.incoming s hsm'
    · exact hp.outgoing s hsm'
  refine ⟨?_, ?_, harcs⟩
  · intro v hv
    rcases mem_insert.mp hv with rfl | hv
    · exact hp.start_mem
    · obtain ⟨e, he, rfl⟩ := mem_image.mp hv
      exact (hs e (harcs he)).1
  · intro c hc
    obtain ⟨e, he, rfl⟩ := mem_image.mp hc
    exact (hs e (harcs he)).2

/-- Every copied constraint of a directed path has precisely its incoming and outgoing arc. -/
theorem DirectedPath.pairedCopies {T : DAG F} {w : Walk F} {time : Occurrence F → ℕ}
    (hp : DirectedPath T w time) : (pathDAG w time).PairedCopies := by
  intro c hc
  obtain ⟨e, hem, rfl⟩ := mem_image.mp hc
  obtain ⟨s, hsm, he⟩ := mem_biUnion.mp hem
  have hs := List.mem_toFinset.mp hsm
  have hsc : (inArc time s).copy = (outArc time s).copy :=
    Prod.ext (linked_constraint hp.walk.1 hs) rfl
  have hec : e.copy = (inArc time s).copy := by
    rcases (show e = inArc time s ∨ e = outArc time s from by
      simpa only [mem_insert, mem_singleton] using he) with rfl | rfl
    · rfl
    · exact hsc.symm
  refine ⟨inArc time s, mem_biUnion.mpr ⟨s, hsm, (by simp)⟩,
    outArc time s, mem_biUnion.mpr ⟨s, hsm, (by simp)⟩,
    rfl, hec.symm, hsc.symm.trans hec.symm, ?_, ?_⟩
  · intro hh
    have := congrArg Arc.incoming hh
    contradiction
  · intro d hdm hdc
    obtain ⟨t, htm, hd⟩ := mem_biUnion.mp hdm
    have ht := List.mem_toFinset.mp htm
    have htc : (inArc time t).copy = (outArc time t).copy :=
      Prod.ext (linked_constraint hp.walk.1 ht) rfl
    have hdc' : d.copy = (inArc time t).copy := by
      rcases (show d = inArc time t ∨ d = outArc time t from by
        simpa only [mem_insert, mem_singleton] using hd) with rfl | rfl
      · rfl
      · exact htc.symm
    have hts := hp.copies_injective t ht s hs (hdc'.symm.trans (hdc.trans hec))
    subst t
    simpa only [mem_insert, mem_singleton] using hd

omit [DecidableEq V] in
/-- Every variable-ended prefix remains a directed path certificate. -/
theorem DirectedPath.take {T : DAG F} {w : Walk F} {time : Occurrence F → ℕ}
    (hp : DirectedPath T w time) (n : ℕ) : DirectedPath T (w.take n) time where
  walk := hp.walk.take n
  start_mem := hp.start_mem
  incoming s hs := hp.incoming s (List.mem_of_mem_take hs)
  outgoing s hs := hp.outgoing s (List.mem_of_mem_take hs)
  copies_injective s hs t ht :=
    hp.copies_injective s (List.mem_of_mem_take hs) t (List.mem_of_mem_take ht)

/-- A path graph flips exactly the incidences of the existing positional walk. -/
theorem pathDAG_flip (w : Walk F) (time : Occurrence F → ℕ) (f : OccurrenceLabeling F Bool) :
    (pathDAG w time).flip f = w.flip f := by
  have he : (pathArcs w time).image Arc.occurrence = w.edges.toFinset := by
    ext o
    simp only [mem_image, pathArcs, mem_biUnion, List.mem_toFinset, mem_insert, mem_singleton,
      Walk.edges, Walk.edgesOf, List.mem_flatMap]
    constructor
    · rintro ⟨e, ⟨s, hs, rfl | rfl⟩, rfl⟩
      · exact ⟨s, hs, by simp [inArc]⟩
      · exact ⟨s, hs, by simp [outArc]⟩
    · rintro ⟨s, hs, ho⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl
      · exact ⟨inArc time s, ⟨s, hs, Or.inl rfl⟩, rfl⟩
      · exact ⟨outArc time s, ⟨s, hs, Or.inr rfl⟩, rfl⟩
  exact congrArg (fun es => flipOn es f) he

omit [DecidableEq V] in
/-- Corollary 36(2), on actual positional walk paths. -/
theorem DirectedPath.valid_flip {sem : Rel → List Bool → Bool}
    {f : OccurrenceLabeling F Bool} {T : DAG F} {w : Walk F} {time : Occurrence F → ℕ}
    (hp : DirectedPath T w time) (h : T.IsFDAG sem f)
    (hM : EdgeInstance.EvenConstraints sem F) : ValidLabeling sem (w.flip f) := by
  classical
  have hs := h.subgraph (hp.subgraph h.supported) (pathDAG_supported w time)
  rw [← pathDAG_flip w time f]
  exact hs.valid_flip_of_pairedCopies hM hp.pairedCopies

omit [DecidableEq V] in
/-- Directed paths have valid flips at every variable-ended prefix, including the empty prefix. -/
theorem DirectedPath.valid_take {sem : Rel → List Bool → Bool}
    {f : OccurrenceLabeling F Bool} {T : DAG F} {w : Walk F} {time : Occurrence F → ℕ}
    (hp : DirectedPath T w time) (h : T.IsFDAG sem f)
    (hM : EdgeInstance.EvenConstraints sem F) (n : ℕ) :
    ValidLabeling sem ((w.take n).flip f) := (hp.take n).valid_flip h hM

omit [DecidableEq V] in
/-- Endpoint inequality and internal consistency turn a directed DAG path into an f-walk.
All prefix validity is a conclusion of Corollary 36, rather than part of the certificate. -/
theorem DirectedPath.isFWalk {sem : Rel → List Bool → Bool}
    {f : OccurrenceLabeling F Bool} {T : DAG F} {w : Walk F} {time : Occurrence F → ℕ}
    (hp : DirectedPath T w time) (h : T.IsFDAG sem f)
    (hM : EdgeInstance.EvenConstraints sem F)
    (hi : Walk.InternallyConsistent f w.steps) (he : w.start ≠ w.finish) :
    w.IsFWalk sem f := by
  refine ⟨⟨hp.walk, hi, Walk.prefixValid_iff_forall_take.mpr ?_⟩, he⟩
  intro n _
  have hv := hp.valid_take h hM n
  rwa [Walk.flip, Walk.edges, ← Walk.flipSteps_eq_flipOn f _ (hp.walk.take n).2] at hv

/-- Union of finite incidence subgraphs, retaining every isolated supported node. -/
@[expose] def union (S U : DAG F) : DAG F :=
  ⟨S.vars ∪ U.vars, S.copies ∪ U.copies, S.arcs ∪ U.arcs⟩

/-- The two terminal incidences of paths meeting at one copied constraint. -/
@[expose] def terminalPair (a b : Arc F) : DAG F :=
  ⟨{a.occurrence.var, b.occurrence.var}, {a.copy}, {a, b}⟩

/-- Uniting supported graphs preserves endpoint support. -/
theorem Supported.union {S U : DAG F} (hs : S.Supported) (hu : U.Supported) :
    (S.union U).Supported := by
  intro e he
  rcases mem_union.mp he with he | he
  · exact ⟨mem_union_left _ (hs e he).1, mem_union_left _ (hs e he).2⟩
  · exact ⟨mem_union_right _ (hu e he).1, mem_union_right _ (hu e he).2⟩

/-- Uniting two subgraphs of the same graph remains a subgraph. -/
theorem Subgraph.union {S U T : DAG F} (hs : S.Subgraph T) (hu : U.Subgraph T) :
    (S.union U).Subgraph T :=
  ⟨union_subset hs.1 hu.1, union_subset hs.2.1 hu.2.1, union_subset hs.2.2 hu.2.2⟩

/-- The two-arc property combines across disjoint sets of copied constraints. -/
theorem PairedCopies.union {S U : DAG F} (hs : S.PairedCopies) (hu : U.PairedCopies)
    (hss : S.Supported) (hus : U.Supported) (hd : Disjoint S.copies U.copies) :
    (S.union U).PairedCopies := by
  unfold PairedCopies DAG.union
  have hside : ∀ {A B : DAG F}, A.PairedCopies → B.Supported →
      Disjoint A.copies B.copies → ∀ c ∈ A.copies,
      ∃ a ∈ A.arcs ∪ B.arcs, ∃ b ∈ A.arcs ∪ B.arcs,
        a.incoming = true ∧ a.copy = c ∧ b.copy = c ∧ a ≠ b ∧
          ∀ e ∈ A.arcs ∪ B.arcs, e.copy = c → e = a ∨ e = b := by
    intro A B hp hbs hdis c hc
    obtain ⟨a, ha, b, hb, hi, hac, hbc, hab, hpair⟩ := hp c hc
    refine ⟨a, mem_union_left _ ha, b, mem_union_left _ hb, hi, hac, hbc, hab, ?_⟩
    intro e hem hec
    rcases mem_union.mp hem with hem | hem
    · exact hpair e hem hec
    · exact (disjoint_left.mp hdis hc (hec ▸ (hbs e hem).2)).elim
  intro c hc
  rcases mem_union.mp hc with hc | hc
  · exact hside hs hus hd c hc
  · simpa only [union_comm U.arcs S.arcs] using hside hu hss hd.symm c hc

/-- Two distinct incoming arcs at one terminal copy satisfy the two-arc property. -/
theorem pairedCopies_terminalPair {a b : Arc F} (hi : a.incoming = true)
    (hc : a.copy = b.copy) (hne : a ≠ b) : (terminalPair a b).PairedCopies := by
  intro c hcm
  have he : c = a.copy := mem_singleton.mp hcm
  subst c
  exact ⟨a, by simp [terminalPair], b, by simp [terminalPair], hi, rfl, hc.symm, hne,
    fun e hem _ => by simpa only [terminalPair, mem_insert, mem_singleton] using hem⟩

/-- Corollary 36(1): flip two directed paths together with their incoming terminal ports.
Only disjointness of their copied constraint nodes is needed by the stronger two-arc theorem;
the source's paths, disjoint except at the terminal copy, satisfy these hypotheses. -/
theorem DirectedPath.valid_flip_meeting {sem : Rel → List Bool → Bool}
    {f : OccurrenceLabeling F Bool} {T : DAG F} {w z : Walk F}
    {timeW timeZ : Occurrence F → ℕ} {a b : Arc F}
    (hw : DirectedPath T w timeW) (hz : DirectedPath T z timeZ)
    (h : T.IsFDAG sem f) (hM : EdgeInstance.EvenConstraints sem F)
    (ha : a ∈ T.arcs) (hb : b ∈ T.arcs) (hai : a.incoming = true)
    (hcopy : a.copy = b.copy) (hne : a ≠ b)
    (hd : Disjoint (pathDAG w timeW).copies (pathDAG z timeZ).copies)
    (hwfresh : a.copy ∉ (pathDAG w timeW).copies)
    (hzfresh : a.copy ∉ (pathDAG z timeZ).copies) :
    ValidLabeling sem
      ((((pathDAG w timeW).union (pathDAG z timeZ)).union (terminalPair a b)).flip f) := by
  have hterm : (terminalPair a b).Supported := by
    intro e he
    rcases (show e = a ∨ e = b from by
      simpa only [terminalPair, mem_insert, mem_singleton] using he) with rfl | rfl
    · exact ⟨by simp [terminalPair], mem_singleton_self _⟩
    · exact ⟨by simp [terminalPair], mem_singleton.mpr hcopy.symm⟩
  have htsub : (terminalPair a b).Subgraph T := by
    refine ⟨?_, ?_, ?_⟩
    · intro v hv
      rcases (show v = a.occurrence.var ∨ v = b.occurrence.var from by
        simpa only [terminalPair, mem_insert, mem_singleton] using hv) with rfl | rfl
      · exact (h.supported a ha).1
      · exact (h.supported b hb).1
    · intro c hc
      have he : c = a.copy := mem_singleton.mp hc
      exact he ▸ (h.supported a ha).2
    · intro e he
      rcases (show e = a ∨ e = b from by
        simpa only [terminalPair, mem_insert, mem_singleton] using he) with rfl | rfl
      · exact ha
      · exact hb
  have hsw := pathDAG_supported w timeW
  have hsz := pathDAG_supported z timeZ
  have hsu := hsw.union hsz
  have hsub := Subgraph.union (Subgraph.union (hw.subgraph h.supported)
    (hz.subgraph h.supported)) htsub
  have hpair := (hw.pairedCopies.union hz.pairedCopies hsw hsz hd).union
    (pairedCopies_terminalPair hai hcopy hne) hsu hterm (by
      apply disjoint_left.mpr
      intro c hc hct
      have he : c = a.copy := mem_singleton.mp hct
      subst c
      exact (mem_union.mp hc).elim hwfresh hzfresh)
  exact (h.subgraph hsub (hsu.union hterm)).valid_flip_of_pairedCopies hM hpair

end

end Cslib.Logic.PL.CSP.DAG
