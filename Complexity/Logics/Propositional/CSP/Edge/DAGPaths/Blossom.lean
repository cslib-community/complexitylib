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
# Blossoms with their full timestamped DAG certificate

Definition 39 of [KazdaKolmogorovRolinek2018], arXiv:1602.03124v6, printed p. 19.
The closed incidence trail has one inconsistent base and consistent internal variables.
Its timestamped graph consists of the forward initial arm and the reversed final arm,
meeting at the copied constraint of step `pivot`. That constraint has two incoming ports.
Every step retains a distinct copied constraint, including between the two arms. This makes
explicit the two-arm geometry used by Lemma 40 when it invokes Corollary 36: the graph union
alone can hide a shared four-port copy. Original constraints may recur at different times.
The graph must satisfy every condition of `DAG.IsFDAG`, including no shortcuts; validity
of the final or proper-prefix flip alone is not a blossom certificate.
-/

public section

namespace Cslib.Logic.PL.CSP

variable {Rel V : Type*} {F : CSP Rel V}

namespace DAG

/-- A variable that already has a parent cannot branch toward two different copies in an
edge-instance DAG: its two original incidences are the parent port and one outgoing port. -/
theorem IsFDAG.incoming_eq_of_parent {sem : Rel → List Bool → Bool}
    {f : OccurrenceLabeling F Bool} {T : DAG F} (h : T.IsFDAG sem f)
    (hF : EdgeInstance F) {p a b : Arc F}
    (hp : p ∈ T.arcs) (ha : a ∈ T.arcs) (hb : b ∈ T.arcs)
    (hpo : p.incoming = false) (hai : a.incoming = true) (hbi : b.incoming = true)
    (hap : a.occurrence.var = p.occurrence.var) (hbp : b.occurrence.var = p.occurrence.var) :
    a = b := by
  have hport : ∀ c ∈ T.arcs, c.incoming = true → c.occurrence.var = p.occurrence.var →
      c.occurrence = hF.partner p.occurrence := by
    intro c hc hci hcv
    rcases hF.eq_or_eq_partner hcv with he | he
    · have hh := congrArg Arc.incoming (h.unique c hc p hp he)
      simp only [hci, hpo] at hh
      cases hh
    · exact he
  exact h.unique a ha b hb ((hport a ha hai hap).trans (hport b hb hbi hbp).symm)

/-- The source's two arms of a cycle. The one-based pivot is the common terminal copied
constraint; before it, steps run forward, and after it, steps run backward. -/
@[expose] def blossomArcs :
    List (Occurrence F × Occurrence F) → List ℕ → ℕ → List (Arc F)
  | [], _, _ => []
  | _, [], _ => []
  | (a, b) :: ss, t :: ts, pivot =>
    ⟨a, t, decide (0 < pivot)⟩ :: ⟨b, t, decide (pivot ≤ 1)⟩ ::
      blossomArcs ss ts (pivot - 1)

/-- The full incidence DAG in Definition 39, retaining the cycle's base as a supported
variable. Timestamps are attached to steps, so repeated original constraints remain distinct. -/
@[expose] def blossomDAG [DecidableEq V] (w : Walk F) (times : List ℕ) (pivot : ℕ) : DAG F where
  vars := insert w.start ((blossomArcs w.steps times pivot).map fun a => a.occurrence.var).toFinset
  copies := ((blossomArcs w.steps times pivot).map Arc.copy).toFinset
  arcs := (blossomArcs w.steps times pivot).toFinset

/-- The cycle graph supports every generated incidence and its actual endpoints. -/
theorem blossomDAG_supported [DecidableEq V] (w : Walk F) (times : List ℕ) (pivot : ℕ) :
    (blossomDAG w times pivot).Supported := by
  intro a ha
  have hm := List.mem_toFinset.mp ha
  exact ⟨Finset.mem_insert_of_mem (List.mem_toFinset.mpr
    (List.mem_map.mpr ⟨a, hm, rfl⟩)),
    List.mem_toFinset.mpr (List.mem_map.mpr ⟨a, hm, rfl⟩)⟩

/-- Every generated arc uses one of the supplied step timestamps. -/
theorem blossomArcs_time_mem {ss : List (Occurrence F × Occurrence F)} {ts : List ℕ}
    {pivot : ℕ} {a : Arc F} (ha : a ∈ blossomArcs ss ts pivot) : a.time ∈ ts := by
  induction ss generalizing ts pivot with
  | nil => simp [blossomArcs] at ha
  | cons s ss ih =>
    cases ts with
    | nil => simp [blossomArcs] at ha
    | cons t ts =>
      rcases s with ⟨o, p⟩
      simp only [blossomArcs, List.mem_cons] at ha
      rcases ha with rfl | rfl | ha
      · exact List.mem_cons_self
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih ha)

/-- Every copied constraint in the cycle graph retains its supplied timestamp. -/
theorem blossomDAG_copy_time_mem [DecidableEq V] (w : Walk F) (times : List ℕ) (pivot : ℕ)
    {c : Copy F} (hc : c ∈ (blossomDAG w times pivot).copies) : c.2 ∈ times := by
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hc)
  exact blossomArcs_time_mem ha

/-- Once the pivot has been passed, appending a cycle step adds a backward-oriented pair. -/
theorem blossomArcs_append_after (ss : List (Occurrence F × Occurrence F)) (ts : List ℕ)
    (pivot : ℕ) (hl : ts.length = ss.length) (hp : pivot ≤ ss.length)
    (s : Occurrence F × Occurrence F) (t : ℕ) :
    blossomArcs (ss ++ [s]) (ts ++ [t]) pivot =
      blossomArcs ss ts pivot ++ [⟨s.1, t, false⟩, ⟨s.2, t, true⟩] := by
  induction ss generalizing ts pivot with
  | nil =>
    cases ts with
    | nil =>
      have he : pivot = 0 := by simpa using hp
      subst pivot
      rfl
    | cons a ts => simp at hl
  | cons p ss ih =>
    cases ts with
    | nil => simp at hl
    | cons u ts =>
      rcases p with ⟨a, b⟩
      have hl' : ts.length = ss.length := by simpa using hl
      have hp' : pivot - 1 ≤ ss.length := by simp only [List.length_cons] at hp; omega
      simp only [List.cons_append, blossomArcs]
      rw [ih ts (pivot - 1) hl' hp']

/-- A computed cycle graph is a subgraph whenever its base and all its actual arcs are
supported by the ambient graph. Copied-node support is inherited from those arcs. -/
theorem blossomDAG_subgraph_of_arcs [DecidableEq V] (w : Walk F) (times : List ℕ) (pivot : ℕ)
    {T : DAG F} (hbase : w.start ∈ T.vars) (hs : T.Supported)
    (ha : ∀ a ∈ blossomArcs w.steps times pivot, a ∈ T.arcs) :
    (blossomDAG w times pivot).Subgraph T := by
  refine ⟨?_, ?_, fun a ham => ha a (List.mem_toFinset.mp ham)⟩
  · intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact hbase
    · obtain ⟨a, ham, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hv)
      exact (hs a (ha a ham)).1
  · intro c hc
    obtain ⟨a, ham, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hc)
    exact (hs a (ha a ham)).2

private theorem blossomArcs_reverse_zero
    (time : Occurrence F → ℕ) (ss : List (Occurrence F × Occurrence F)) {e : Arc F}
    (he : e ∈ blossomArcs (ss.reverse.map Prod.swap) ((ss.map fun s => time s.1).reverse) 0) :
    ∃ s ∈ ss, e = inArc time s ∨ e = outArc time s := by
  induction ss using List.reverseRecOn with
  | nil => simp [blossomArcs] at he
  | append_singleton ss s ih =>
    rcases s with ⟨a, b⟩
    simp only [List.reverse_append, List.reverse_singleton, List.map_append,
      List.map_singleton, List.singleton_append] at he
    change e ∈ outArc time (a, b) :: inArc time (a, b) ::
      blossomArcs (ss.reverse.map Prod.swap) ((ss.map fun s => time s.1).reverse) 0 at he
    simp only [List.mem_cons] at he
    rcases he with rfl | rfl | he
    · exact ⟨(a, b), List.mem_append_right _ (List.mem_singleton_self _), Or.inr rfl⟩
    · exact ⟨(a, b), List.mem_append_right _ (List.mem_singleton_self _), Or.inl rfl⟩
    · obtain ⟨s, hs, he⟩ := ih he
      exact ⟨s, List.mem_append_left _ hs, he⟩

/-- Every cycle arc comes from one of its two directed arms or the terminal incoming pair. -/
theorem blossomArcs_meeting_mem (timeW timeZ : Occurrence F → ℕ)
    (ss zs : List (Occurrence F × Occurrence F)) (a b : Occurrence F) (t : ℕ) {e : Arc F}
    (he : e ∈ blossomArcs (ss ++ (a, b) :: (zs.reverse.map Prod.swap))
      ((ss.map fun s => timeW s.1) ++ t :: (zs.map fun s => timeZ s.1).reverse)
      (ss.length + 1)) :
    (∃ s ∈ ss, e = inArc timeW s ∨ e = outArc timeW s) ∨
      e = ⟨a, t, true⟩ ∨ e = ⟨b, t, true⟩ ∨
      ∃ s ∈ zs, e = inArc timeZ s ∨ e = outArc timeZ s := by
  induction ss with
  | nil =>
    change e ∈ ⟨a, t, true⟩ :: ⟨b, t, true⟩ ::
      blossomArcs (zs.reverse.map Prod.swap) ((zs.map fun s => timeZ s.1).reverse) 0 at he
    simp only [List.mem_cons] at he
    rcases he with he | he | he
    · exact Or.inr (Or.inl he)
    · exact Or.inr (Or.inr (Or.inl he))
    · exact Or.inr (Or.inr (Or.inr (blossomArcs_reverse_zero timeZ zs he)))
  | cons s ss ih =>
    rcases s with ⟨o, p⟩
    change e ∈ inArc timeW (o, p) :: outArc timeW (o, p) ::
      blossomArcs (ss ++ (a, b) :: (zs.reverse.map Prod.swap))
        ((ss.map fun s => timeW s.1) ++ t :: (zs.map fun s => timeZ s.1).reverse)
        (ss.length + 1) at he
    simp only [List.mem_cons] at he
    rcases he with rfl | rfl | he
    · exact Or.inl ⟨(o, p), List.mem_cons_self, Or.inl rfl⟩
    · exact Or.inl ⟨(o, p), List.mem_cons_self, Or.inr rfl⟩
    · rcases ih he with ⟨s, hs, he⟩ | he
      · exact Or.inl ⟨s, List.mem_cons_of_mem _ hs, he⟩
      · exact Or.inr he

/-- Two directed arms and their incoming meeting ports embed the computed cycle graph in
the ambient DAG. The closed-trail and consistency requirements of a blossom are separate. -/
theorem blossomDAG_subgraph_meeting [DecidableEq V] {T : DAG F} {w z : Walk F}
    {timeW timeZ : Occurrence F → ℕ} {a b : Occurrence F} {t : ℕ}
    (hw : DirectedPath T w timeW) (hz : DirectedPath T z timeZ) (hs : T.Supported)
    (ha : (⟨a, t, true⟩ : Arc F) ∈ T.arcs) (hb : (⟨b, t, true⟩ : Arc F) ∈ T.arcs) :
    (blossomDAG ((w.snoc a b).append z.reverse)
      (w.steps.map (fun s => timeW s.1) ++ [t] ++ (z.steps.map fun s => timeZ s.1).reverse)
      (w.steps.length + 1)).Subgraph T := by
  have harcs : ∀ e ∈ blossomArcs ((w.snoc a b).append z.reverse).steps
      (w.steps.map (fun s => timeW s.1) ++ [t] ++ (z.steps.map fun s => timeZ s.1).reverse)
      (w.steps.length + 1), e ∈ T.arcs := by
    intro e he
    change e ∈ blossomArcs ((w.steps ++ [(a, b)]) ++ z.steps.reverse.map Prod.swap)
      ((w.steps.map (fun s => timeW s.1) ++ [t]) ++
        (z.steps.map fun s => timeZ s.1).reverse) _ at he
    rw [List.append_assoc, List.append_assoc] at he
    rcases blossomArcs_meeting_mem timeW timeZ w.steps z.steps a b t he with
      ⟨s, hs, rfl | rfl⟩ | rfl | rfl | ⟨s, hs, rfl | rfl⟩
    · exact hw.incoming s hs
    · exact hw.outgoing s hs
    · exact ha
    · exact hb
    · exact hz.incoming s hs
    · exact hz.outgoing s hs
  exact blossomDAG_subgraph_of_arcs _ _ _ hw.start_mem hs harcs

end DAG

namespace Walk

/-- Original constraint positions paired with the supplied timestamps, one per cycle step.
The two incidences of the meeting step refer to the same copy and are counted only once. -/
@[expose] def copies (w : Walk F) (times : List ℕ) : List (DAG.Copy F) :=
  (w.steps.zip times).map fun ((input, _), time) => (input.1, time)

/-- Every cycle step has a timestamp and uses its own copied constraint node. Repeated
original constraints are allowed at different times. This excludes a four-port shared copy
hidden by taking the union of the two arms in `DAG.blossomDAG`. -/
@[expose] def DistinctCopies (w : Walk F) (times : List ℕ) : Prop :=
  times.length = w.steps.length ∧ (w.copies times).Nodup

/-- Distinct timestamps give distinct copied steps, independently of original constraint
repetitions. Length equality prevents the zip from discarding steps. -/
theorem distinctCopies_of_nodup_times (w : Walk F) {times : List ℕ}
    (hl : times.length = w.steps.length) (hn : times.Nodup) : w.DistinctCopies times := by
  refine ⟨hl, List.Nodup.of_map (f := Prod.snd) ?_⟩
  simp only [copies, List.map_map]
  change ((w.steps.zip times).map Prod.snd).Nodup
  rwa [List.map_snd_zip (Nat.le_of_eq hl)]

/-- An f-blossom following source Definition 39, retaining distinct copied steps. Witnesses specify the
copied constraints and the terminal meeting, rather than assuming an event-correctness oracle. -/
@[expose] def IsBlossom (sem : Rel → List Bool → Bool) (f : OccurrenceLabeling F Bool)
    (w : Walk F) : Prop :=
  w.IsWalk ∧ w.finish = w.start ∧ w.steps ≠ [] ∧ Inconsistent f w.start ∧
    InternallyConsistent f w.steps ∧
    ∃ (times : List ℕ) (pivot : ℕ), w.DistinctCopies times ∧
      0 < pivot ∧ pivot ≤ w.steps.length ∧
      letI : DecidableEq V := Classical.decEq V
      (DAG.blossomDAG w times pivot).IsFDAG sem f

end Walk

end Cslib.Logic.PL.CSP
