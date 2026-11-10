/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.EdgeCSP.Forest.Terminal
public import CslibFrontier.Algorithms.Lean.EdgeCSP.Forest.BlossomData
public import CslibFrontier.Logics.Propositional.CSP.Edge.Walk.Subpath
public import CslibFrontier.Logics.Propositional.CSP.Edge.Walk.Visits
public import CslibFrontier.Logics.Propositional.CSP.Edge.DAGPaths.Preparation
public import CslibFrontier.Logics.Propositional.CSP.Edge.DAGPaths.Blossom

/-!
# Correctness of chronological forest events

Terminal events of Algorithm 1 of [KazdaKolmogorovRolinek2018], arXiv:1602.03124v6.
Paths and copied constraints are the actual parent reconstructions of the executable search.

## Main results

* `search_augment_correct`: a returned augmentation is an augmenting f-walk; its flip is
  valid and removes exactly two defects (Proposition 38, printed p. 18).
* `Meeting.Trace.variable_blossom_isFDAG`: the variable-LCA cycle's full graph certificate.

The constraint-LCA case and complete fresh-run blossom endpoint are proved in
`CslibFrontier/Algorithms/Lean/EdgeCSP/Forest/Blossom.lean`.
-/

public section

namespace Cslib.Logic.PL.CSP.Forest

open DAG

variable {Rel V : Type*} {F : CSP Rel V} [DecidableEq V]

namespace Log

omit [DecidableEq V] in
/-- A timestamp in a chronological log has only its single recorded incoming port. -/
theorem incoming_time_unique {es : Log F} {a b : Arc F} (ha : a ∈ es.arcs)
    (hb : b ∈ es.arcs) (hai : a.incoming = true) (hbi : b.incoming = true)
    (ht : a.time = b.time) : a = b := by
  induction es with
  | nil => simp [arcs] at ha
  | cons e es ih =>
    simp only [arcs, List.mem_cons, List.mem_append, List.mem_map] at ha hb
    rcases ha with rfl | ⟨o, ho, rfl⟩ | ha
    · rcases hb with rfl | ⟨o, ho, rfl⟩ | hb
      · rfl
      · cases hbi
      · have := (mem_arcs es hb).2
        change es.length = b.time at ht
        omega
    · cases hai
    · rcases hb with rfl | ⟨o, ho, rfl⟩ | hb
      · have := (mem_arcs es ha).2
        change a.time = es.length at ht
        omega
      · cases hbi
      · exact ih ha hb

/-- Appending fresh children leaves every older visited variable's ancestry unchanged. -/
theorem ancestry_cons_old {es : Log F} {e : Expansion F} {rs : List V} {v : V}
    (hf : ∀ o ∈ e.outputs, ¬ es.Visited rs o.var) (hv : es.Visited rs v) :
    Log.ancestry (e :: es) v = es.ancestry v := by
  have hh : e.outputs.find? (fun o => o.var == v) = none := by
    apply List.find?_eq_none.mpr
    intro o ho he
    have he' : o.var = v := by simpa only [beq_iff_eq] using he
    exact hf o ho (he'.symm ▸ hv)
  simp [ancestry, hh]

/-- Actual ancestry timestamps strictly increase, without any condition on variable names. -/
theorem ancestry_times_pairwise (es : Log F) (v : V) :
    ((es.ancestry v).times).Pairwise (· < ·) := by
  induction es generalizing v with
  | nil => exact List.Pairwise.nil
  | cons e es ih =>
    simp only [ancestry]
    split
    · rw [List.pairwise_append]
      refine ⟨ih e.input.var, by simp, ?_⟩
      intro a ha b hb
      have he : b = es.length := List.mem_singleton.mp hb
      exact he ▸ ancestry_time_lt es e.input.var ha
    · exact ih v

end Log

namespace Grown

variable {sem : Rel → List Bool → Bool} {f : OccurrenceLabeling F Bool}
  {rs : List V} {es : Log F}

/-- Recorded ancestry timestamps agree with the executable incoming-port lookup. -/
theorem ancestry_times_eq_stamp (hg : Grown sem f rs es) (v : V) :
    (es.ancestry v).times = (es.ancestry v).walk.steps.map (fun s => es.stamp s.1) := by
  induction hg generalizing v with
  | nil => rfl
  | @cons es e hp hv hu hf hn hfe hsat ih =>
    have oldstamp : ∀ z ∈ es.used, Log.stamp (e :: es) z = es.stamp z := by
      intro z hz
      have hne : e.input ≠ z := fun he => hu (he.symm ▸ hz)
      simp [Log.stamp, hne]
    have hmap : ∀ u, (es.ancestry u).walk.steps.map (fun s => Log.stamp (e :: es) s.1) =
        (es.ancestry u).walk.steps.map (fun s => es.stamp s.1) := by
      intro u
      apply List.map_congr_left
      intro s hs
      exact oldstamp s.1 (es.mem_arcs (hp.ancestry_arcs u hs).1).1
    simp only [Log.ancestry]
    split
    · simp only [Walk.snoc, List.map_append, List.map_singleton]
      rw [hmap, ih]
      simp [Log.stamp]
    · rw [hmap, ih]

/-- Ancestral steps are chronological with respect to their actual incoming timestamps. -/
theorem ancestry_chronological (hg : Grown sem f rs es) (v : V) :
    ((es.ancestry v).walk.steps).Pairwise (fun s t => es.stamp s.1 < es.stamp t.1) := by
  have hh := es.ancestry_times_pairwise v
  rw [hg.ancestry_times_eq_stamp v, List.pairwise_map] at hh
  exact hh

/-- Ancestor nodes carry precisely the copied constraints certified by the incoming arcs. -/
theorem ancestry_nodes (hg : Grown sem f rs es) (v : V) :
    (es.ancestry v).nodes = .inl (es.ancestry v).walk.start ::
      (es.ancestry v).walk.steps.flatMap
        (fun s => [.inr (inArc es.stamp s).copy, .inl s.2.var]) := by
  rw [Ancestry.nodes, hg.ancestry_times_eq_stamp]
  have hh : ∀ ss : List (Occurrence F × Occurrence F),
      (ss.zip (ss.map fun s => es.stamp s.1)).flatMap
        (fun ((a, b), t) => ([.inr (a.1, t), .inl b.var] : List (Node F))) =
      ss.flatMap (fun s => [.inr (inArc es.stamp s).copy, .inl s.2.var]) := by
    intro ss
    induction ss with
    | nil => rfl
    | cons s ss ih =>
      rcases s with ⟨a, b⟩
      simp only [List.map_cons, List.zip_cons_cons, List.flatMap_cons, ih, inArc, Arc.copy]
  rw [hh]

/-- The path to a step's input is the exact ancestral prefix before that step. This uses
actual parent reconstruction, including across copies of the same original constraint. -/
theorem ancestry_step_prefix (hg : Grown sem f rs es) {v : V}
    {s : Occurrence F × Occurrence F} (hs : s ∈ (es.ancestry v).walk.steps) :
    (es.ancestry s.1.var).walk.start = (es.ancestry v).walk.start ∧
      ((es.ancestry s.1.var).walk.steps ++ [s]).IsPrefix (es.ancestry v).walk.steps := by
  induction hg generalizing v with
  | nil => simp [Log.ancestry] at hs
  | @cons es e hp hv hu hf hn hfe hsat ih =>
    cases hfind : e.outputs.find? (fun o => o.var == v) with
    | none =>
      have hvpath : Log.ancestry (e :: es) v = es.ancestry v := by
        simp [Log.ancestry, hfind]
      rw [hvpath] at hs ⊢
      rw [Log.ancestry_cons_old (v := s.1.var) hf
        (Log.Grown.used_visited hp (es.mem_arcs (hp.ancestry_arcs v hs).1).1)]
      exact ih hs
    | some o =>
      have hvpath : Log.ancestry (e :: es) v =
          ⟨(es.ancestry e.input.var).walk.snoc e.input o,
            (es.ancestry e.input.var).times ++ [es.length]⟩ := by simp [Log.ancestry, hfind]
      rw [hvpath] at hs ⊢
      simp only [Walk.snoc] at hs ⊢
      rcases List.mem_append.mp hs with hs | hs
      · rw [Log.ancestry_cons_old (v := s.1.var) hf
          (Log.Grown.used_visited hp (es.mem_arcs (hp.ancestry_arcs _ hs).1).1)]
        obtain ⟨he, ⟨tail, htail⟩⟩ := ih hs
        exact ⟨he, ⟨tail ++ [(e.input, o)], by simp only [← htail, List.append_assoc]⟩⟩
      · have he : s = (e.input, o) := List.mem_singleton.mp hs
        subst s
        rw [Log.ancestry_cons_old hf hv]
        exact ⟨rfl, ⟨[], by simp⟩⟩

/-- Before any ancestral copied constraint, its input's entire root path is shared. -/
theorem ancestry_step_nodes_prefix (hg : Grown sem f rs es) {v : V}
    {s : Occurrence F × Occurrence F} (hs : s ∈ (es.ancestry v).walk.steps) :
    ((es.ancestry s.1.var).nodes ++ [(Sum.inr (inArc es.stamp s).copy : Node F)]).IsPrefix
      (es.ancestry v).nodes := by
  obtain ⟨hstart, ⟨tail, htail⟩⟩ := hg.ancestry_step_prefix hs
  refine ⟨.inl s.2.var :: tail.flatMap
    (fun t => [.inr (inArc es.stamp t).copy, .inl t.2.var]), ?_⟩
  rw [hg.ancestry_nodes, hg.ancestry_nodes, ← htail, ← hstart]
  simp only [List.flatMap_append, List.flatMap_cons, List.cons_append, List.nil_append,
    List.append_assoc]

/-- The full node prefix through any ancestral step is determined by its input's ancestry. -/
theorem ancestry_step_full_nodes_prefix (hg : Grown sem f rs es) {v : V}
    {s : Occurrence F × Occurrence F} (hs : s ∈ (es.ancestry v).walk.steps) :
    ((es.ancestry s.1.var).nodes ++
      ([.inr (inArc es.stamp s).copy, .inl s.2.var] : List (Node F))).IsPrefix
      (es.ancestry v).nodes := by
  obtain ⟨hstart, ⟨tail, htail⟩⟩ := hg.ancestry_step_prefix hs
  refine ⟨tail.flatMap (fun t => [.inr (inArc es.stamp t).copy, .inl t.2.var]), ?_⟩
  rw [hg.ancestry_nodes, hg.ancestry_nodes, ← htail, ← hstart]
  simp only [List.flatMap_append, List.flatMap_cons, List.cons_append, List.nil_append,
    List.append_assoc]

/-- A step remaining after dropping `k` steps cannot have a shorter root-side parent path. -/
theorem ancestry_step_prefix_length (hg : Grown sem f rs es) {v : V} {k : ℕ}
    {s : Occurrence F × Occurrence F} (hs : s ∈ (es.ancestry v).walk.steps.drop k) :
    k ≤ (es.ancestry s.1.var).walk.steps.length := by
  have hsm := List.mem_of_mem_drop hs
  obtain ⟨_, ⟨tail, he⟩⟩ := hg.ancestry_step_prefix hsm
  have hn : (es.ancestry v).walk.steps.Nodup :=
    (hg.ancestry_chronological v).imp
      (fun {_ _} hlt he => by cases he; exact Nat.lt_irrefl _ hlt)
  rw [← he, List.append_assoc, List.singleton_append] at hn hs
  have hnot : s ∉ tail := (List.nodup_cons.mp (List.nodup_append.mp hn).2.1).1
  by_contra hk
  have hle : (es.ancestry s.1.var).walk.steps.length ≤ k := by omega
  have hpos : 0 < k - (es.ancestry s.1.var).walk.steps.length := by omega
  rw [List.drop_append, List.drop_eq_nil_of_le hle, List.nil_append] at hs
  cases hx : k - (es.ancestry s.1.var).walk.steps.length with
  | zero => omega
  | succ n =>
    rw [hx, List.drop_succ_cons] at hs
    exact hnot (List.mem_of_mem_drop hs)

/-- Paths sharing a copied constraint share its whole root-side node prefix. -/
theorem ancestry_shared_copy_prefix (hg : Grown sem f rs es) {u v : V}
    {s t : Occurrence F × Occurrence F}
    (hs : s ∈ (es.ancestry u).walk.steps) (ht : t ∈ (es.ancestry v).walk.steps)
    (hc : (inArc es.stamp s).copy = (inArc es.stamp t).copy) :
    ((es.ancestry s.1.var).nodes ++ [(Sum.inr (inArc es.stamp s).copy : Node F)]).IsPrefix
      (es.ancestry u).nodes ∧
    ((es.ancestry s.1.var).nodes ++ [(Sum.inr (inArc es.stamp s).copy : Node F)]).IsPrefix
      (es.ancestry v).nodes := by
  have he := Log.incoming_time_unique (hg.ancestry_arcs u hs).1 (hg.ancestry_arcs v ht).1
    rfl rfl (congrArg Prod.snd hc)
  have hinput : s.1 = t.1 := congrArg Arc.occurrence he
  refine ⟨hg.ancestry_step_nodes_prefix hs, ?_⟩
  simpa only [hinput, hc] using hg.ancestry_step_nodes_prefix ht

/-- An ancestral copied constraint belongs to just one rooted tree. Repeated original
constraints at different timestamps are not identified. -/
theorem ancestry_root_eq_of_copy (hg : Grown sem f rs es) {u v : V}
    {s t : Occurrence F × Occurrence F}
    (hs : s ∈ (es.ancestry u).walk.steps) (ht : t ∈ (es.ancestry v).walk.steps)
    (hc : (inArc es.stamp s).copy = (inArc es.stamp t).copy) :
    (es.ancestry u).walk.start = (es.ancestry v).walk.start := by
  induction hg generalizing u v s t with
  | nil => simp [Log.ancestry] at hs
  | @cons es e hp hv hu hf hn hfe hsat ih =>
    have oldstamp : ∀ z ∈ es.used, Log.stamp (e :: es) z = es.stamp z := by
      intro z hz
      have hne : e.input ≠ z := fun he => hu (he.symm ▸ hz)
      simp [Log.stamp, hne]
    have older : ∀ {x y : V} {s t : Occurrence F × Occurrence F},
        s ∈ (es.ancestry x).walk.steps → t ∈ (es.ancestry y).walk.steps →
        (inArc (Log.stamp (e :: es)) s).copy =
          (inArc (Log.stamp (e :: es)) t).copy →
        (es.ancestry x).walk.start = (es.ancestry y).walk.start := by
      intro x y s t hs ht hc
      apply ih hs ht
      simpa only [inArc, Arc.copy,
        oldstamp s.1 (es.mem_arcs (hp.ancestry_arcs x hs).1).1,
        oldstamp t.1 (es.mem_arcs (hp.ancestry_arcs y ht).1).1] using hc
    have notnew : ∀ {x : V} {s : Occurrence F × Occurrence F},
        s ∈ (es.ancestry x).walk.steps →
        (inArc (Log.stamp (e :: es)) s).copy ≠ (e.input.1, es.length) := by
      intro x s hs he
      have hsa := (hp.ancestry_arcs x hs).1
      have hlt := (es.mem_arcs hsa).2
      have htime := congrArg Prod.snd he
      change Log.stamp (e :: es) s.1 = es.length at htime
      rw [oldstamp s.1 (es.mem_arcs hsa).1] at htime
      change es.stamp s.1 < es.length at hlt
      omega
    cases hfu : e.outputs.find? (fun o => o.var == u) with
    | some a =>
      cases hfv : e.outputs.find? (fun o => o.var == v) with
      | some b => simp only [Log.ancestry, hfu, hfv, Walk.snoc]
      | none =>
        simp only [Log.ancestry, hfu, hfv, Walk.snoc] at hs ht ⊢
        rcases List.mem_append.mp hs with hs | hs
        · exact older hs ht hc
        · have he : s = (e.input, a) := List.mem_singleton.mp hs
          subst s
          apply False.elim (notnew ht ?_)
          simpa only [inArc, Arc.copy, Log.stamp, ↓reduceIte] using hc.symm
    | none =>
      cases hfv : e.outputs.find? (fun o => o.var == v) with
      | some b =>
        simp only [Log.ancestry, hfu, hfv, Walk.snoc] at hs ht ⊢
        rcases List.mem_append.mp ht with ht | ht
        · exact older hs ht hc
        · have he : t = (e.input, b) := List.mem_singleton.mp ht
          subst t
          apply False.elim (notnew hs ?_)
          simpa only [inArc, Arc.copy, Log.stamp, ↓reduceIte] using hc
      | none =>
        simp only [Log.ancestry, hfu, hfv] at hs ht ⊢
        exact older hs ht hc

/-- Ancestries from different rooted trees have disjoint copied-constraint supports. -/
theorem ancestry_disjoint_copies (hg : Grown sem f rs es) {u v : V}
    (hu : es.Visited rs u) (hv : es.Visited rs v)
    (hne : (es.ancestry u).walk.start ≠ (es.ancestry v).walk.start) :
    Disjoint (pathDAG (es.ancestry u).walk es.stamp).copies
      (pathDAG (es.ancestry v).walk es.stamp).copies := by
  apply Finset.disjoint_left.mpr
  intro c hc hd
  obtain ⟨s, hs, hsc⟩ := (hg.ancestry_directed hu).mem_copies.mp hc
  obtain ⟨t, ht, htc⟩ := (hg.ancestry_directed hv).mem_copies.mp hd
  exact hne (hg.ancestry_root_eq_of_copy hs ht (hsc.trans htc.symm))

/-- Every output variable of a reconstructed ancestry is consistent in the reference
labeling. Inconsistent variables are roots, never discovered children. -/
theorem ancestry_output_consistent (hg : Grown sem f (roots f) es) (v : V)
    {s : Occurrence F × Occurrence F} (hs : s ∈ (es.ancestry v).walk.steps) :
    ¬ Inconsistent f s.2.var := by
  have ho := hg.ancestry_arcs v hs |>.2
  exact fun hi => hg.outgoing_not_root (Log.mem_outgoing_of_arc ho rfl)
    ((mem_roots f _).mpr hi)

/-- A nonempty ancestry ends at a discovered, hence consistent, variable. -/
theorem ancestry_finish_consistent (hg : Grown sem f (roots f) es) {v : V}
    (hne : (es.ancestry v).walk.steps ≠ []) : ¬ Inconsistent f v := by
  have hc : ∀ (ss : List (Occurrence F × Occurrence F)) (u : V), ss ≠ [] →
      (∀ s ∈ ss, ¬ Inconsistent f s.2.var) → ¬ Inconsistent f (Walk.finishFrom u ss) := by
    intro ss u
    induction ss using List.reverseRecOn with
    | nil => intro hn; exact False.elim (hn rfl)
    | append_singleton ss s ih =>
      intro _ hs
      simpa only [Walk.finishFrom_append, Walk.finishFrom] using
        hs s (List.mem_append_right _ (List.mem_singleton_self _))
  have hh := hc (es.ancestry v).walk.steps (es.ancestry v).walk.start hne
    (fun s hs => hg.ancestry_output_consistent v hs)
  rwa [← Walk.finish, es.ancestry_finish] at hh

/-- All ancestral prefixes have the source's internal-consistency and validity properties,
including the empty path at an inconsistent root. -/
theorem ancestry_isFPrefix (hg : Grown sem f (roots f) es) (hF : EdgeInstance F)
    (hf : ValidLabeling sem f) (hM : EdgeInstance.EvenConstraints sem F) {v : V}
    (hv : es.Visited (roots f) v) : (es.ancestry v).walk.IsFPrefix sem f := by
  refine ⟨hg.ancestry_isWalk v, ?_, Walk.prefixValid_iff_forall_take.mpr ?_⟩
  · have hc : ∀ (ss : List (Occurrence F × Occurrence F)),
        (∀ s ∈ ss, ¬ Inconsistent f s.2.var) → Walk.InternallyConsistent f ss := by
      intro ss
      induction ss with
      | nil => intro _; trivial
      | cons s ss ih =>
        intro hc
        exact ⟨Or.inr (hc s List.mem_cons_self), ih (fun t ht => hc t (List.mem_cons_of_mem s ht))⟩
    exact hc _ (fun s hs => hg.ancestry_output_consistent v hs)
  · intro n _
    rw [Walk.flipSteps_eq_flipOn f ((es.ancestry v).walk.steps.take n)
      ((hg.ancestry_isWalk v).take n).2]
    exact hg.ancestry_valid_take hF hf hM hv n

end Grown

namespace Ancestry

omit [DecidableEq V] in
/-- Every reconstructed node list ends at a variable, including the length-zero ancestry. -/
theorem nodes_last_variable (p : Ancestry F) :
    ∃ v : V, p.nodes.getLast? = some (.inl v) := by
  have hh : ∀ (ss : List ((Occurrence F × Occurrence F) × ℕ)),
      ∃ v : V, ((.inl p.walk.start : Node F) :: ss.flatMap
        (fun ((a, b), t) => [.inr (a.1, t), .inl b.var])).getLast? = some (.inl v) := by
    intro ss
    induction ss using List.reverseRecOn with
    | nil => exact ⟨p.walk.start, rfl⟩
    | append_singleton ss s ih =>
      rcases s with ⟨⟨a, b⟩, t⟩
      refine ⟨b.var, ?_⟩
      rw [List.flatMap_append]
      change (((.inl p.walk.start : Node F) :: ss.flatMap
        (fun (x : (Occurrence F × Occurrence F) × ℕ) =>
          ([.inr (x.1.1.1, x.2), .inl x.1.2.var] : List (Node F)))) ++
        ([.inr (a.1, t), .inl b.var] : List (Node F))).getLast? = _
      rw [List.getLast?_append]
      rfl
  exact hh _

omit [DecidableEq V] in
/-- A correctly stamped ancestry has one variable node and two nodes per step. -/
theorem nodes_length (p : Ancestry F) (hl : p.times.length = p.walk.steps.length) :
    p.nodes.length = 2 * p.walk.steps.length + 1 := by
  have hh : ∀ (ss : List ((Occurrence F × Occurrence F) × ℕ)),
      (ss.flatMap (fun ((a, b), t) => ([.inr (a.1, t), .inl b.var] : List (Node F)))).length =
        2 * ss.length := by
    intro ss
    induction ss with
    | nil => rfl
    | cons s ss ih =>
      rcases s with ⟨⟨a, b⟩, t⟩
      simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.length_cons, ih]
      omega
  simp only [nodes, List.length_cons, hh, List.length_zip, hl, Nat.min_self]

omit [DecidableEq V] in
/-- Even node indices are exactly the endpoints of the corresponding walk prefixes. -/
theorem nodes_getElem?_even (p : Ancestry F) (hl : p.times.length = p.walk.steps.length)
    (k : ℕ) (hk : k ≤ p.walk.steps.length) :
    p.nodes[2 * k]? = some (.inl (p.walk.take k).finish) := by
  rcases p with ⟨⟨v, ss⟩, ts⟩
  induction k generalizing v ss ts with
  | zero => rfl
  | succ k ih =>
    cases ss with
    | nil => simp at hk
    | cons s ss =>
      cases ts with
      | nil => simp at hl
      | cons t ts =>
        rcases s with ⟨a, b⟩
        have hl' : ts.length = ss.length := by simpa using hl
        have hk' : k ≤ ss.length := by simpa only [List.length_cons, Nat.succ_le_succ_iff] using hk
        have hh := ih (v := b.var) (ss := ss) (ts := ts) hl' hk'
        simpa only [nodes, Walk.take, Walk.finish, Walk.finishFrom, List.zip_cons_cons,
          List.flatMap_cons, List.cons_append, List.nil_append, Nat.mul_succ,
          List.getElem?_cons_succ, List.take_succ_cons] using hh

omit [DecidableEq V] in
/-- Odd node indices are exactly the timestamped constraints of the corresponding steps. -/
theorem nodes_getElem?_odd (p : Ancestry F) (hl : p.times.length = p.walk.steps.length)
    (k : ℕ) (hk : k < p.walk.steps.length) :
    p.nodes[2 * k + 1]? = some (.inr ((p.walk.steps[k]).1.1, p.times[k]'(by omega))) := by
  rcases p with ⟨⟨v, ss⟩, ts⟩
  induction k generalizing v ss ts with
  | zero =>
    cases ss with
    | nil => simp at hk
    | cons s ss =>
      cases ts with
      | nil => simp at hl
      | cons t ts => rfl
  | succ k ih =>
    cases ss with
    | nil => simp at hk
    | cons s ss =>
      cases ts with
      | nil => simp at hl
      | cons t ts =>
        rcases s with ⟨a, b⟩
        have hl' : ts.length = ss.length := by simpa using hl
        have hk' : k < ss.length := by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hk
        have hh := ih (v := b.var) (ss := ss) (ts := ts) hl' hk'
        simpa only [nodes, List.zip_cons_cons, List.flatMap_cons, List.cons_append,
          List.nil_append, Nat.mul_succ, Nat.add_assoc, List.getElem?_cons_succ,
          List.getElem_cons_succ] using hh

end Ancestry

namespace Meeting

variable {sem : Rel → List Bool → Bool} {f : OccurrenceLabeling F Bool} {m : Meeting F}

/-- The executable common-node list is a prefix of both actual ancestral node lists. -/
theorem commonNodes_prefix (m : Meeting F) :
    m.commonNodes.IsPrefix m.left.nodes ∧ m.commonNodes.IsPrefix m.right.nodes := by
  have hp : ∀ (ls rs : List (Node F)),
      (((ls.zip rs).takeWhile fun (a, b) => a == b).map Prod.fst).IsPrefix ls ∧
      (((ls.zip rs).takeWhile fun (a, b) => a == b).map Prod.fst).IsPrefix rs := by
    intro ls
    induction ls with
    | nil => intro rs; exact ⟨⟨[], rfl⟩, ⟨rs, rfl⟩⟩
    | cons a ls ih =>
      intro rs
      cases rs with
      | nil => exact ⟨⟨a :: ls, rfl⟩, ⟨[], rfl⟩⟩
      | cons b rs =>
        by_cases he : a = b
        · subst b
          obtain ⟨⟨xs, hxs⟩, ⟨ys, hys⟩⟩ := ih rs
          constructor
          · exact ⟨xs, by simpa using congrArg (List.cons a) hxs⟩
          · exact ⟨ys, by simpa using congrArg (List.cons a) hys⟩
        · constructor
          · exact ⟨a :: ls, by simp [he]⟩
          · exact ⟨b :: rs, by simp [he]⟩
  exact hp _ _

/-- Every common node prefix is contained in the prefix selected by the extractor. -/
theorem commonNodes_maximal (m : Meeting F) (ps : List (Node F))
    (hl : ps.IsPrefix m.left.nodes) (hr : ps.IsPrefix m.right.nodes) :
    ps.length ≤ m.commonNodes.length := by
  have hh : ∀ (ps ls rs : List (Node F)), ps.IsPrefix ls → ps.IsPrefix rs →
      ps.length ≤ (((ls.zip rs).takeWhile fun (a, b) => a == b).map Prod.fst).length := by
    intro ps
    induction ps with
    | nil => intro ls rs _ _; exact Nat.zero_le _
    | cons p ps ih =>
      intro ls rs ⟨xs, hxs⟩ ⟨ys, hys⟩
      rw [← hxs, ← hys]
      have hh := ih (ps ++ xs) (ps ++ ys) ⟨xs, rfl⟩ ⟨ys, rfl⟩
      simpa using Nat.add_le_add_right hh 1
  exact hh _ _ _ hl hr

/-- A copied constraint shared by the two ancestries lies inside their computed common
prefix, with its complete root path. -/
theorem Trace.shared_copy_common_length (h : Trace sem f m)
    {s t : Occurrence F × Occurrence F}
    (hs : s ∈ m.left.walk.steps) (ht : t ∈ m.right.walk.steps)
    (hc : (inArc m.older.stamp s).copy = (inArc m.older.stamp t).copy) :
    2 * (m.older.ancestry s.1.var).walk.steps.length + 2 ≤ m.commonNodes.length := by
  obtain ⟨hl, hr⟩ := h.expansion.grown.ancestry_shared_copy_prefix hs ht hc
  have hh := m.commonNodes_maximal _ hl hr
  have hlen := (m.older.ancestry s.1.var).nodes_length (m.older.ancestry_length _)
  simpa only [List.length_append, List.length_singleton, hlen, Nat.add_assoc] using hh

/-- A common root always supplies at least one common node. -/
theorem commonNodes_ne_nil (m : Meeting F) (he : m.left.walk.start = m.right.walk.start) :
    m.commonNodes ≠ [] := by
  simp [commonNodes, Ancestry.nodes, he]

/-- Every index inside the common prefix names the same actual node on both paths. -/
theorem commonNodes_getElem? (m : Meeting F) {i : ℕ} (hi : i < m.commonNodes.length) :
    m.left.nodes[i]? = m.right.nodes[i]? := by
  obtain ⟨xs, hx⟩ := m.commonNodes_prefix.1
  obtain ⟨ys, hy⟩ := m.commonNodes_prefix.2
  rw [← hx, ← hy, List.getElem?_append_left hi, List.getElem?_append_left hi]

/-- Whole shared steps carry the same timestamp prefix on both ancestries. -/
theorem common_times_take (m : Meeting F) (k : ℕ) (hk : 2 * k + 1 ≤ m.commonNodes.length) :
    m.left.times.take k = m.right.times.take k := by
  have hll := m.commonNodes_prefix.1.length_le
  have hrl := m.commonNodes_prefix.2.length_le
  have hllen := m.left.nodes_length (m.older.ancestry_length _)
  have hrlen := m.right.nodes_length (m.older.ancestry_length _)
  have hlsteps : k ≤ m.left.walk.steps.length := by omega
  have hrsteps : k ≤ m.right.walk.steps.length := by omega
  have hltimes : k ≤ m.left.times.length := by
    have hl : m.left.times.length = m.left.walk.steps.length := m.older.ancestry_length _
    omega
  have hrtimes : k ≤ m.right.times.length := by
    have hl : m.right.times.length = m.right.walk.steps.length := m.older.ancestry_length _
    omega
  apply List.ext_getElem
  · simp only [List.length_take, Nat.min_eq_left hltimes, Nat.min_eq_left hrtimes]
  · intro i hi hj
    have hik : i < k := by simpa only [List.length_take, Nat.min_eq_left hltimes] using hi
    have hil : i < m.left.walk.steps.length := by omega
    have hir : i < m.right.walk.steps.length := by omega
    have hnodes := m.commonNodes_getElem? (i := 2 * i + 1) (by omega)
    rw [m.left.nodes_getElem?_odd (m.older.ancestry_length _) i hil,
      m.right.nodes_getElem?_odd (m.older.ancestry_length _) i hir] at hnodes
    have htimes := congrArg Prod.snd (Sum.inr.inj (Option.some.inj hnodes))
    simpa only [List.getElem_take] using htimes

/-- A shared root prefix predates every step on the remaining right arm. -/
theorem Trace.prefix_time_lt_right_drop (h : Trace sem f m) (k : ℕ)
    (hk : 2 * k + 1 ≤ m.commonNodes.length) {s t : Occurrence F × Occurrence F}
    (hs : s ∈ m.left.walk.steps.take k) (ht : t ∈ m.right.walk.steps.drop k) :
    m.older.stamp s.1 < m.older.stamp t.1 := by
  have hml : m.left.times.take k =
      (m.left.walk.steps.take k).map (fun s => m.older.stamp s.1) := by
    simpa only [Meeting.left, List.map_take] using congrArg (List.take k)
      (h.expansion.grown.ancestry_times_eq_stamp m.current.input.var)
  have hmr : m.right.times.drop k =
      (m.right.walk.steps.drop k).map (fun s => m.older.stamp s.1) := by
    simpa only [Meeting.right, List.map_drop] using congrArg (List.drop k)
      (h.expansion.grown.ancestry_times_eq_stamp m.output.var)
  have hst : m.older.stamp s.1 ∈ m.right.times.take k := by
    rw [← m.common_times_take k hk, hml]
    exact List.mem_map.mpr ⟨s, hs, rfl⟩
  have htt : m.older.stamp t.1 ∈ m.right.times.drop k := by
    rw [hmr]
    exact List.mem_map.mpr ⟨t, ht, rfl⟩
  have hp : (m.right.times.take k ++ m.right.times.drop k).Pairwise (· < ·) := by
    rw [List.take_append_drop]
    exact m.older.ancestry_times_pairwise _
  exact (List.pairwise_append.mp hp).2.2 _ hst _ htt

/-- The selected ancestor occurs at the final shared index on each ancestral node list. -/
theorem ancestor_at_common_index (m : Meeting F) {a : Node F}
    (ha : m.ancestor? = some a) :
    m.left.nodes[m.commonNodes.length - 1]? = some a ∧
      m.right.nodes[m.commonNodes.length - 1]? = some a := by
  have hpos : 0 < m.commonNodes.length := by
    cases he : m.commonNodes with
    | nil => simp [ancestor?, he] at ha
    | cons b bs => simp
  have hidx : m.commonNodes.length - 1 < m.commonNodes.length := by omega
  have hh : m.commonNodes[m.commonNodes.length - 1]? = some a := by
    rw [← List.getLast?_eq_getElem?]
    exact ha
  have hside : ∀ ls : List (Node F), m.commonNodes.IsPrefix ls →
      ls[m.commonNodes.length - 1]? = some a := by
    intro ls ⟨tail, he⟩
    rw [← he, List.getElem?_append_left hidx]
    exact hh
  exact ⟨hside _ m.commonNodes_prefix.1, hside _ m.commonNodes_prefix.2⟩

/-- The common-node computation finds an ancestor whenever the two roots agree. -/
theorem ancestor?_isSome (m : Meeting F) (he : m.left.walk.start = m.right.walk.start) :
    m.ancestor?.isSome := by
  cases ha : m.ancestor? with
  | none => exact False.elim (m.commonNodes_ne_nil he
      (List.getLast?_eq_none_iff.mp ha))
  | some a => rfl

/-- A copied-constraint ancestor occurs before a step on each path. The `Option` branches
in the raw extractor cannot fail on that case, even for timestamp zero. -/
theorem ancestor_constraint_index_lt (m : Meeting F) {c : Copy F}
    (hc : m.ancestor? = some (.inr c)) :
    (m.commonNodes.length - 1) / 2 < m.left.walk.steps.length ∧
      (m.commonNodes.length - 1) / 2 < m.right.walk.steps.length := by
  have hside : ∀ p : Ancestry F, p.times.length = p.walk.steps.length →
      m.commonNodes.IsPrefix p.nodes → (m.commonNodes.length - 1) / 2 < p.walk.steps.length := by
    intro p hl hp
    have hle := hp.length_le
    have hlen := p.nodes_length hl
    have hpos : 0 < m.commonNodes.length := by
      cases he : m.commonNodes with
      | nil => simp [ancestor?, he] at hc
      | cons a as => simp
    by_contra hn
    have he : m.commonNodes.length = p.nodes.length := by omega
    have heq := hp.eq_of_length_le (Nat.le_of_eq he.symm)
    obtain ⟨v, hv⟩ := p.nodes_last_variable
    have hh : some (.inr c : Node F) = some (.inl v) := by
      rw [← hc, ancestor?, heq]
      exact hv
    cases hh
  exact ⟨hside _ (m.older.ancestry_length _) m.commonNodes_prefix.1,
    hside _ (m.older.ancestry_length _) m.commonNodes_prefix.2⟩

/-- A variable LCA is the last node of a whole-step common prefix. -/
theorem ancestor_variable_length (m : Meeting F) {v : V}
    (hv : m.ancestor? = some (.inl v)) :
    m.commonNodes.length = 2 * ((m.commonNodes.length - 1) / 2) + 1 := by
  have hpos : 0 < m.commonNodes.length := by
    cases he : m.commonNodes with
    | nil => simp [ancestor?, he] at hv
    | cons a as => simp
  have hle := m.commonNodes_prefix.1.length_le
  have hlen := m.left.nodes_length (m.older.ancestry_length _)
  by_cases hm : (m.commonNodes.length - 1) % 2 = 0
  · omega
  · have hj : m.commonNodes.length - 1 = 2 * ((m.commonNodes.length - 1) / 2) + 1 := by omega
    have hk : (m.commonNodes.length - 1) / 2 < m.left.walk.steps.length := by omega
    have hh := (m.ancestor_at_common_index hv).1
    rw [hj, m.left.nodes_getElem?_odd (m.older.ancestry_length _) _ hk] at hh
    cases hh

/-- A variable ancestor is the actual endpoint of both shared walk prefixes. -/
theorem ancestor_variable_prefix (m : Meeting F) {v : V}
    (hv : m.ancestor? = some (.inl v)) :
    (m.left.walk.take ((m.commonNodes.length - 1) / 2)).finish = v ∧
      (m.right.walk.take ((m.commonNodes.length - 1) / 2)).finish = v := by
  have hside : ∀ p : Ancestry F, p.times.length = p.walk.steps.length →
      m.commonNodes.IsPrefix p.nodes →
      p.nodes[m.commonNodes.length - 1]? = some (.inl v) →
      (p.walk.take ((m.commonNodes.length - 1) / 2)).finish = v := by
    intro p hl hp he
    have hpos : 0 < m.commonNodes.length := by
      cases hx : m.commonNodes with
      | nil => simp [ancestor?, hx] at hv
      | cons a as => simp
    have hlen := p.nodes_length hl
    have hle := hp.length_le
    have hk : (m.commonNodes.length - 1) / 2 ≤ p.walk.steps.length := by omega
    have hlength := m.ancestor_variable_length hv
    have hj : m.commonNodes.length - 1 = 2 * ((m.commonNodes.length - 1) / 2) := by omega
    rw [hj, p.nodes_getElem?_even hl _ hk] at he
    exact Sum.inl.inj (Option.some.inj he)
  exact ⟨hside _ (m.older.ancestry_length _) m.commonNodes_prefix.1
      (m.ancestor_at_common_index hv).1,
    hside _ (m.older.ancestry_length _) m.commonNodes_prefix.2
      (m.ancestor_at_common_index hv).2⟩

/-- Past the last common copied node, the left ancestry shares no copied constraint
with the right ancestry. This is derived from exact parent prefixes, not assumed as an
event-correctness premise. -/
theorem Trace.left_drop_disjoint_right (h : Trace sem f m) (k : ℕ)
    (hk : m.commonNodes.length < 2 * k + 2) :
    Disjoint (pathDAG (m.left.walk.drop k) m.older.stamp).copies
      (pathDAG m.right.walk m.older.stamp).copies := by
  have hp := (h.expansion.grown.ancestry_directed h.expansion.visited).drop
    (m.older.toDAG_supported m.roots) k
  apply Finset.disjoint_left.mpr
  intro c hc hd
  obtain ⟨s, hs, hsc⟩ := hp.mem_copies.mp hc
  obtain ⟨t, ht, htc⟩ := (h.expansion.grown.ancestry_directed h.old_visited).mem_copies.mp hd
  have hbound := h.shared_copy_common_length (List.mem_of_mem_drop hs) ht (hsc.trans htc.symm)
  have hindex := h.expansion.grown.ancestry_step_prefix_length hs
  omega

/-- At a same-root event the actual raw extractor returns cycle data; neither LCA case
is lost through an absent ancestor or an out-of-bounds child port. -/
theorem blossomData_isSome (m : Meeting F) (he : m.left.walk.start = m.right.walk.start) :
    m.blossomData.isSome := by
  have ha := m.ancestor?_isSome he
  cases hc : m.ancestor? with
  | none => simp [hc] at ha
  | some a =>
    cases a with
    | inl v => simp [blossomData, hc]
    | inr c =>
      obtain ⟨hl, hr⟩ := m.ancestor_constraint_index_lt hc
      simp [blossomData, hc, List.getElem?_eq_getElem hl, List.getElem?_eq_getElem hr]

/-- The older forest survives terminal pruning as a supported subgraph. -/
theorem Trace.older_subgraph_pruned (h : Trace sem f m) :
    (m.older.toDAG m.roots).Subgraph m.prunedDAG := by
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    apply List.mem_toFinset.mpr
    rcases List.mem_append.mp (List.mem_toFinset.mp hv) with hv | hv
    · exact List.mem_append_left _ hv
    · obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hv
      exact List.mem_append_right _ (List.mem_map.mpr ⟨o,
        List.mem_cons_of_mem _ (List.mem_append_right _ ho), rfl⟩)
  · intro c hc
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hc)
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨a,
      List.mem_cons_of_mem _ (List.mem_append_right _ ha), rfl⟩)
  · intro a ha
    rw [h.pruned_arcs]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ha)

/-- The actual left ancestral path remains directed after terminal pruning. -/
theorem Trace.left_directed (h : Trace sem f m) :
    DirectedPath m.prunedDAG m.left.walk m.older.stamp :=
  (h.expansion.grown.ancestry_directed h.expansion.visited).mono h.older_subgraph_pruned

/-- The actual right ancestral path remains directed after terminal pruning. -/
theorem Trace.right_directed (h : Trace sem f m) :
    DirectedPath m.prunedDAG m.right.walk m.older.stamp :=
  (h.expansion.grown.ancestry_directed h.old_visited).mono h.older_subgraph_pruned

/-- The new terminal copy is absent from every older ancestry, including timestamp zero. -/
theorem Trace.copy_fresh (h : Trace sem f m) {v : V}
    (hv : m.older.Visited m.roots v) :
    m.copy ∉ (pathDAG (m.older.ancestry v).walk m.older.stamp).copies := by
  intro hm
  obtain ⟨s, hs, he⟩ := (h.expansion.grown.ancestry_directed hv).mem_copies.mp hm
  have ht := (m.older.mem_arcs (h.expansion.grown.ancestry_arcs v hs).1).2
  have he := congrArg Prod.snd he
  change m.older.stamp s.1 = m.older.length at he
  change m.older.stamp s.1 < m.older.length at ht
  omega

/-- Both ancestral paths and the terminal pair give valid flips at every prefix of the
actual returned augmentation walk. Reversed prefixes are justified by directed suffixes. -/
theorem Trace.augment_valid_take (h : Trace sem f m) (hF : EdgeInstance F)
    (hf : ValidLabeling sem f) (hM : EdgeInstance.EvenConstraints sem F)
    (hne : m.left.walk.start ≠ m.right.walk.start) (n : ℕ) :
    ValidLabeling sem ((m.walk.take n).flip f) := by
  have ht := h.pruned_isFDAG hF hf
  have hpair := (mem_partners sem f _ _).mp h.partner
  apply h.left_directed.valid_take_meeting h.right_directed ht hM
    (a := ⟨m.current.input, m.older.length, true⟩)
    (b := ⟨m.output, m.older.length, true⟩)
  · rw [h.pruned_arcs]
    simp
  · rw [h.pruned_arcs]
    simp
  · rfl
  · exact Prod.ext hpair.1 rfl
  · intro he
    exact hpair.2.1 (congrArg (fun a : Arc F => a.occurrence.var) he)
  · exact h.expansion.grown.ancestry_disjoint_copies h.expansion.visited h.old_visited hne
  · exact h.copy_fresh h.expansion.visited
  · exact h.copy_fresh h.old_visited

/-- The candidate from two different rooted trees is an actual incidence trail. -/
theorem Trace.augment_isWalk (h : Trace sem f m) (hF : EdgeInstance F)
    (hf : ValidLabeling sem f) (hne : m.left.walk.start ≠ m.right.walk.start) :
    m.walk.IsWalk := by
  have hg := h.expansion.grown
  have hd := hg.ancestry_disjoint_copies h.expansion.visited h.old_visited hne
  have hed := h.left_directed.disjoint_edges h.right_directed (h.pruned_isFDAG hF hf) hd
  have hpair := (mem_partners sem f _ _).mp h.partner
  have hno : m.current.input ∉ m.left.walk.edges := fun hm =>
    h.expansion.unused (m.older.ancestry_edges_subset _ hm)
  have hnp : m.output ∉ m.left.walk.edges := fun hm =>
    h.output_unused (m.older.ancestry_edges_subset _ hm)
  have hleft : (m.left.walk.snoc m.current.input m.output).IsWalk := by
    exact h.left_directed.walk.snoc (m.older.ancestry_finish _).symm hpair.1
      (fun he => hpair.2.1 (congrArg Occurrence.var he)) hno hnp
  apply hleft.append h.right_directed.walk.reverse
  · rw [Walk.finish_snoc]
    exact (m.older.ancestry_finish _).symm
  · intro o ho hp
    rw [Walk.edges_reverse, List.mem_reverse] at hp
    change o ∈ Walk.edgesOf (m.left.walk.steps ++ [(m.current.input, m.output)]) at ho
    rw [Walk.edgesOf_append] at ho
    change o ∈ m.left.walk.edges ++ [m.current.input, m.output] at ho
    rcases List.mem_append.mp ho with ho | ho
    · exact hed ho hp
    · rcases (show o = m.current.input ∨ o = m.output by simpa using ho) with rfl | rfl
      · exact h.expansion.unused (m.older.ancestry_edges_subset _ hp)
      · exact h.output_unused (m.older.ancestry_edges_subset _ hp)

/-- Source Proposition 38 at the walk level: the returned candidate is an augmenting
f-walk, including internal consistency and validity after every prefix. -/
theorem Trace.augment_isAugmenting (h : Trace sem f m) (hF : EdgeInstance F)
    (hf : ValidLabeling sem f) (hM : EdgeInstance.EvenConstraints sem F)
    (hne : m.left.walk.start ≠ m.right.walk.start) : m.walk.IsAugmenting sem f := by
  have hg := h.expansion.grown
  have hroots := h.roots_eq
  have hg' : Grown sem f (Forest.roots f) m.older := hroots ▸ hg
  have hfinish : m.walk.finish = m.right.walk.start := by
    change Walk.finishFrom _ (_ ++ _) = _
    rw [Walk.finishFrom_append]
    change Walk.finishFrom (m.left.walk.snoc m.current.input m.output).finish
      m.right.walk.reverse.steps = _
    rw [Walk.finish_snoc, ← m.older.ancestry_finish m.output.var]
    exact Walk.finish_reverse _ h.right_directed.walk.1
  refine ⟨⟨⟨h.augment_isWalk hF hf hne, ?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · have htail : Walk.InternallyConsistent f
        ((m.current.input, m.output) :: m.right.walk.reverse.steps) := by
      refine ⟨?_, (hg'.ancestry_isFPrefix hF hf hM (hroots ▸ h.old_visited)).2.1.reverse
        h.right_directed.walk.1⟩
      by_cases hz : m.right.walk.steps = []
      · exact Or.inl (by simp [Walk.reverse, hz])
      · exact Or.inr (hg'.ancestry_finish_consistent hz)
    change Walk.InternallyConsistent f
      ((m.left.walk.steps ++ [(m.current.input, m.output)]) ++ m.right.walk.reverse.steps)
    rw [List.append_assoc]
    exact Walk.InternallyConsistent.append_of_outputs
      (fun s hs => hg'.ancestry_output_consistent _ hs) htail
  · apply Walk.prefixValid_iff_forall_take.mpr
    intro n _
    have hv := h.augment_valid_take hF hf hM hne n
    rwa [Walk.flip, Walk.edges, ← Walk.flipSteps_eq_flipOn f _
      ((h.augment_isWalk hF hf hne).take n).2] at hv
  · change m.left.walk.start ≠ m.walk.finish
    rwa [hfinish]
  · apply (mem_roots f _).mp
    rw [← hroots]
    exact hg.ancestry_start_root h.expansion.visited
  · rw [hfinish]
    apply (mem_roots f _).mp
    rw [← hroots]
    exact hg.ancestry_start_root h.old_visited

/-- Every preparatory root-path flip actually returned by the cycle extractor is valid.
This is the preparatory-labeling assertion of source Lemma 41; the remaining blossom
assertion additionally requires the closed cycle's complete f-DAG certificate. -/
theorem Trace.blossom_prepare_valid (h : Trace sem f m) (hF : EdgeInstance F)
    (hf : ValidLabeling sem f) (hM : EdgeInstance.EvenConstraints sem F)
    {b : BlossomData F} (hb : m.blossomData = some b) :
    ValidLabeling sem (b.prepare.flip f) := by
  unfold Meeting.blossomData at hb
  split at hb
  · cases hb
  next ancestor ha =>
    cases ancestor with
    | inl base =>
      dsimp only at hb
      cases hb
      exact h.expansion.grown.ancestry_valid_take hF hf hM h.expansion.visited _
    | inr c =>
      dsimp only at hb
      split at hb
      · cases hb
        exact h.expansion.grown.ancestry_valid_take hF hf hM h.expansion.visited _
      · cases hb

/-- The cycle returned by either actual LCA branch is closed at its recorded base. -/
theorem Trace.blossom_cycle_closed (h : Trace sem f m) {b : BlossomData F}
    (hb : m.blossomData = some b) : b.cycle.finish = b.cycle.start := by
  unfold Meeting.blossomData at hb
  split at hb
  · cases hb
  next ancestor ha =>
    cases ancestor with
    | inl base =>
      dsimp only at hb
      cases hb
      have hp := (m.ancestor_variable_prefix ha).2
      let k := (m.commonNodes.length - 1) / 2
      have hright : (⟨base, m.right.walk.steps.drop k⟩ : Walk F) = m.right.walk.drop k := by
        unfold Walk.drop
        rw [hp]
      have hr := h.right_directed.walk.drop k
      change Walk.finishFrom _ (_ ++ _) = base
      rw [Walk.finishFrom_append]
      change Walk.finishFrom
        ((⟨base, m.left.walk.steps.drop k⟩ : Walk F).snoc m.current.input m.output).finish _ = base
      rw [Walk.finish_snoc]
      change Walk.finishFrom (m.output.var) (Walk.reverse
        (⟨base, m.right.walk.steps.drop k⟩ : Walk F)).steps = base
      rw [hright]
      have he : (m.right.walk.drop k).reverse.start = m.output.var := by
        simp only [Walk.reverse, Walk.finish_drop, Meeting.right, Log.ancestry_finish]
      rw [← he]
      change (m.right.walk.drop k).reverse.finish = base
      rw [Walk.finish_reverse _ hr.1]
      exact hp
    | inr c =>
      dsimp only at hb
      split at hb
      · cases hb
        exact Walk.finish_snoc _ _ _
      · cases hb

/-- In the variable-LCA branch, the cycle's actual timestamped graph is an f-DAG after
the returned preparatory flip. Both feasibility and no shortcuts are preserved. -/
theorem Trace.variable_blossom_isFDAG (h : Trace sem f m) (hF : EdgeInstance F)
    (hf : ValidLabeling sem f) (hM : EdgeInstance.EvenConstraints sem F)
    {base : V} (ha : m.ancestor? = some (.inl base)) {b : BlossomData F}
    (hb : m.blossomData = some b) :
    (blossomDAG b.cycle b.times b.pivot).IsFDAG sem (b.prepare.flip f) := by
  simp only [Meeting.blossomData, ha] at hb
  cases hb
  let k := (m.commonNodes.length - 1) / 2
  have hlen : m.commonNodes.length = 2 * k + 1 := m.ancestor_variable_length ha
  have hp := m.ancestor_variable_prefix ha
  have hleft : (⟨base, m.left.walk.steps.drop k⟩ : Walk F) = m.left.walk.drop k := by
    unfold Walk.drop
    rw [hp.1]
  have hright : (⟨base, m.right.walk.steps.drop k⟩ : Walk F) = m.right.walk.drop k := by
    unfold Walk.drop
    rw [hp.2]
  have htl : m.left.times.drop k = (m.left.walk.drop k).steps.map
      (fun s => m.older.stamp s.1) := by
    simpa only [Meeting.left, Walk.drop, List.map_drop] using congrArg (List.drop k)
      (h.expansion.grown.ancestry_times_eq_stamp m.current.input.var)
  have htr : m.right.times.drop k = (m.right.walk.drop k).steps.map
      (fun s => m.older.stamp s.1) := by
    simpa only [Meeting.right, Walk.drop, List.map_drop] using congrArg (List.drop k)
      (h.expansion.grown.ancestry_times_eq_stamp m.output.var)
  dsimp only
  rw [hleft, hright, htl, htr]
  have ht := h.pruned_isFDAG hF hf
  have hlp := h.left_directed.drop ht.supported k
  have hrp := h.right_directed.drop ht.supported k
  let S := blossomDAG
    (((m.left.walk.drop k).snoc m.current.input m.output).append (m.right.walk.drop k).reverse)
    ((m.left.walk.drop k).steps.map (fun s => m.older.stamp s.1) ++ [m.older.length] ++
      ((m.right.walk.drop k).steps.map fun s => m.older.stamp s.1).reverse)
    ((m.left.walk.drop k).steps.length + 1)
  have hsub : S.Subgraph m.prunedDAG := by
    apply blossomDAG_subgraph_meeting hlp hrp ht.supported
    · rw [h.pruned_arcs]; simp
    · rw [h.pruned_arcs]; simp
  have hchron : (m.left.walk.take k).steps.Pairwise
      (fun s t => m.older.stamp s.1 < m.older.stamp t.1) :=
    (h.expansion.grown.ancestry_chronological _).sublist (List.take_sublist k _)
  apply (h.left_directed.take k).flip_later_subgraph ht hM hchron hsub
    (blossomDAG_supported _ _ _)
  intro c hc s hs
  have hctime := blossomDAG_copy_time_mem _ _ _ hc
  rcases List.mem_append.mp hctime with hc | hc
  · rcases List.mem_append.mp hc with hc | hc
    · obtain ⟨t, ht', he⟩ := List.mem_map.mp hc
      have hpair : (m.left.walk.steps.take k ++ m.left.walk.steps.drop k).Pairwise
          (fun s t => m.older.stamp s.1 < m.older.stamp t.1) := by
        rw [List.take_append_drop]
        exact h.expansion.grown.ancestry_chronological _
      rw [← he]
      exact (List.pairwise_append.mp hpair).2.2 s hs t ht'
    · have he : c.2 = m.older.length := List.mem_singleton.mp hc
      rw [he]
      exact (m.older.mem_arcs
        (h.expansion.grown.ancestry_arcs _ (List.mem_of_mem_take hs)).1).2
  · rw [List.mem_reverse] at hc
    obtain ⟨t, ht', he⟩ := List.mem_map.mp hc
    rw [← he]
    exact h.prefix_time_lt_right_drop k (by omega) hs ht'

end Meeting

/-- Agreement of a terminal tag with the two reconstructed roots. -/
@[expose] def Result.Classified : Result F → Prop
  | .exhausted _ => True
  | .augment m => m.left.walk.start ≠ m.right.walk.start
  | .blossom m => m.left.walk.start = m.right.walk.start

/-- The executable event tag records exactly whether the two ancestries have the same root. -/
theorem run_event_roots (sem : Rel → List Bool → Bool) (f : OccurrenceLabeling F Bool)
    (rs : List V) (es : Log F) (remaining : List (Occurrence F)) :
    (run sem f rs es remaining).Classified := by
  unfold run
  split
  · trivial
  next input hi =>
    split
    next os o =>
      dsimp only
      split
      · assumption
      · assumption
    next os => exact run_event_roots sem f rs _ _
termination_by remaining.length
decreasing_by
  rename_i input hi _ _ os _ _
  have hm : input ∈ remaining := List.mem_of_find?_eq_some hi
  have hpos := List.length_pos_of_mem hm
  have he := List.length_erase_of_mem hm
  have hf := List.length_filter_le (fun a => decide
    (a ∉ Log.used ((⟨input, os⟩ : Expansion F) :: es))) (remaining.erase input)
  omega

/-- Source Proposition 38 for a fresh executable run: an actual returned augmentation is
an augmenting f-walk and its flip is valid and removes exactly two defects. -/
theorem search_augment_correct (sem : Rel → List Bool → Bool)
    (f : OccurrenceLabeling F Bool) (hF : EdgeInstance F) (hf : ValidLabeling sem f)
    (hM : EdgeInstance.EvenConstraints sem F) {m : Meeting F}
    (hr : search sem f = .augment m) :
    m.walk.IsAugmenting sem f ∧ ValidLabeling sem (m.walk.flip f) ∧
      (defects (m.walk.flip f)).card + 2 = (defects f).card := by
  have hs := search_trace sem f hF
  rw [hr] at hs
  have he := run_event_roots sem f (roots f) [] (incidenceList F)
  change (match search sem f with
    | .exhausted _ => True
    | .augment m => m.left.walk.start ≠ m.right.walk.start
    | .blossom m => m.left.walk.start = m.right.walk.start) at he
  rw [hr] at he
  have ha := hs.augment_isAugmenting hF hf hM he
  refine ⟨ha, ?_, ha.card_defects_flip_add_two hF⟩
  have hv := hs.augment_valid_take hF hf hM he m.walk.steps.length
  simpa only [Walk.take, List.take_length] using hv

end Cslib.Logic.PL.CSP.Forest
