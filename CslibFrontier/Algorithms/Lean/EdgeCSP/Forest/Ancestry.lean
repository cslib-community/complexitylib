/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.EdgeCSP.Forest.Invariant

/-!
# Actual incidence trails reconstructed from chronological parents

Parent reconstruction uses only older expansion records. The endpoint and trail proofs
below concern the existing `Walk` semantics; they do not posit a second graph or walk model.
The source is Algorithm 1's root paths, [KazdaKolmogorovRolinek2018],
arXiv:1602.03124v6, printed pp. 10–11.

## Main results

* `Grown.ancestry_directed`: actual directed ancestral paths in the existing DAG.
* `Grown.ancestry_valid_take`: every variable-ended prefix preserves validity.
-/

public section

namespace Cslib.Logic.PL.CSP.Forest

open DAG

variable {Rel V : Type*} {F : CSP Rel V} [DecidableEq V]

namespace Log

/-- Timestamp of the expansion using a port as input; zero when no such expansion exists.
For actual incoming arcs the fallback is unreachable. -/
@[expose] def stamp : Log F → Occurrence F → ℕ
  | [], _ => 0
  | e :: es, o => if e.input = o then es.length else stamp es o

/-- Ancestry reconstruction always ends at the requested variable, including the empty path
for an undiscovered variable. -/
theorem ancestry_finish (es : Log F) (v : V) : (es.ancestry v).walk.finish = v := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [ancestry]
    split
    next o ho =>
      rw [Walk.finish_snoc]
      simpa only [beq_iff_eq] using List.find?_some ho
    next => exact ih

/-- Every reconstructed trail port is an actual recorded input or output port. -/
theorem ancestry_edges_subset (es : Log F) (v : V) :
    (es.ancestry v).walk.edges ⊆ es.used := by
  induction es generalizing v with
  | nil => simp [ancestry, Walk.edges, Walk.edgesOf]
  | cons e es ih =>
    simp only [ancestry]
    split
    next o ho =>
      intro a ha
      change a ∈ Walk.edgesOf ((Log.ancestry es e.input.var).walk.steps ++ [(e.input, o)]) at ha
      rw [Walk.edgesOf_append] at ha
      rcases List.mem_append.mp ha with ha | ha
      · exact List.mem_cons_of_mem _ (List.mem_append_right _ (ih _ ha))
      · have he : a = e.input ∨ a = o := by simpa [Walk.edgesOf] using ha
        rcases he with rfl | rfl
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_of_find?_eq_some ho))
    next =>
      intro a ha
      exact List.mem_cons_of_mem _ (List.mem_append_right _ (ih v ha))

omit [DecidableEq V] in
/-- Recording an expansion whose input port is fresh leaves the timestamps of the ports
already used unchanged. -/
theorem stamp_cons_of_mem_used {e : Expansion F} {es : Log F} {z : Occurrence F}
    (hu : e.input ∉ es.used) (hz : z ∈ es.used) : stamp (e :: es) z = es.stamp z := by
  have hne : e.input ≠ z := fun he => hu (he ▸ hz)
  simp only [stamp, hne, ↓reduceIte]

end Log

namespace Grown

variable {sem : Rel → List Bool → Bool} {f : OccurrenceLabeling F Bool}
  {rs : List V} {es : Log F}

/-- Actual incoming ports retain their chronological timestamps in executable lookup. -/
theorem stamp_eq (hg : Grown sem f rs es) {a : Arc F} (ha : a ∈ es.arcs)
    (hi : a.incoming = true) : es.stamp a.occurrence = a.time := by
  induction hg with
  | nil => simp [Log.arcs] at ha
  | @cons es e hp hv hu hf hn hfe hs ih =>
    simp only [Log.arcs, List.mem_cons, List.mem_append, List.mem_map] at ha
    rcases ha with rfl | ⟨o, ho, rfl⟩ | ha
    · simp [Log.stamp]
    · cases hi
    · rw [Log.stamp_cons_of_mem_used hu (es.mem_arcs ha).1]
      exact ih ha

/-- Reconstructed ancestries are linked incidence trails, without any assumption of path
correctness. Constraint copies may repeat their original constraint position. -/
theorem ancestry_isWalk (hg : Grown sem f rs es) (v : V) :
    (es.ancestry v).walk.IsWalk := by
  induction hg generalizing v with
  | nil => exact ⟨trivial, by simp [Log.ancestry, Walk.edges, Walk.edgesOf]⟩
  | @cons es e hp hv hu hf hn hfe hs ih =>
    simp only [Log.ancestry]
    split
    next o ho =>
      have hom := List.mem_of_find?_eq_some ho
      have hc := ((mem_partners sem f e.input o).mp (hfe o hom)).1
      have hw := ih e.input.var
      refine ⟨hw.1.snoc (es.ancestry_finish e.input.var).symm hc, ?_⟩
      change (Walk.edgesOf ((es.ancestry e.input.var).walk.steps ++ [(e.input, o)])).Nodup
      rw [Walk.edgesOf_append, List.nodup_append]
      have hne : e.input ≠ o := fun he => hf o hom (he ▸ hv)
      refine ⟨hw.2, by simpa [Walk.edgesOf] using hne, ?_⟩
      intro a ha b hb he
      have ham := es.ancestry_edges_subset e.input.var ha
      have hb' : b = e.input ∨ b = o := by simpa [Walk.edgesOf] using hb
      rcases hb' with hbInput | hbOut
      · exact hu ((he.trans hbInput) ▸ ham)
      · exact hf o hom ((he.trans hbOut) ▸ Log.Grown.used_visited hp ham)
    next => exact ih v

/-- Every reconstructed step is supported by its actual incoming and outgoing graph arcs.
This certifies the copied node, not merely its original constraint. -/
theorem ancestry_arcs (hg : Grown sem f rs es) (v : V)
    {s : Occurrence F × Occurrence F} (hm : s ∈ (es.ancestry v).walk.steps) :
    inArc es.stamp s ∈ es.arcs ∧ outArc es.stamp s ∈ es.arcs := by
  induction hg generalizing v with
  | nil => simp [Log.ancestry] at hm
  | @cons es e hp hv hu hf hn hfe hs ih =>
    -- A step of an older ancestry keeps both arcs, since its timestamp is unchanged.
    have old : ∀ w, s ∈ (es.ancestry w).walk.steps →
        inArc (Log.stamp (e :: es)) s ∈ Log.arcs (e :: es) ∧
          outArc (Log.stamp (e :: es)) s ∈ Log.arcs (e :: es) := fun w hm => by
      obtain ⟨hi, hout⟩ := ih w hm
      have he : Log.stamp (e :: es) s.1 = es.stamp s.1 :=
        Log.stamp_cons_of_mem_used hu (es.mem_arcs hi).1
      simp only [inArc, outArc, he] at hi hout ⊢
      exact ⟨List.mem_cons_of_mem _ (List.mem_append_right _ hi),
        List.mem_cons_of_mem _ (List.mem_append_right _ hout)⟩
    simp only [Log.ancestry] at hm
    split at hm
    next o ho =>
      rcases List.mem_append.mp hm with hm | hm
      · exact old _ hm
      · obtain rfl : s = (e.input, o) := List.mem_singleton.mp hm
        constructor
        · simp [inArc, Log.stamp, Log.arcs]
        · have hout : (⟨o, es.length, false⟩ : Arc F) ∈ Log.arcs (e :: es) :=
            List.mem_cons_of_mem _ (List.mem_append_left _
              (List.mem_map.mpr ⟨o, List.mem_of_find?_eq_some ho, rfl⟩))
          simpa only [outArc, Log.stamp, ↓reduceIte] using hout
    next => exact old v hm

/-- When an expansion with a fresh input is recorded, every step of an existing ancestry keeps
its incoming timestamp, which precedes the new expansion's timestamp `es.length`. -/
theorem stamp_cons_of_mem_ancestry (hg : Grown sem f rs es) {e : Expansion F}
    (hu : e.input ∉ es.used) {w : V} {x : Occurrence F × Occurrence F}
    (hx : x ∈ (es.ancestry w).walk.steps) :
    Log.stamp (e :: es) x.1 = es.stamp x.1 ∧ es.stamp x.1 < es.length := by
  have hxa := es.mem_arcs (hg.ancestry_arcs w hx).1
  exact ⟨Log.stamp_cons_of_mem_used hu hxa.1, hxa.2⟩

/-- An ancestral path visits each copied constraint at most once. Distinct copies of the
same original constraint remain allowed. -/
theorem ancestry_copies_injective (hg : Grown sem f rs es) (v : V)
    {s t : Occurrence F × Occurrence F}
    (hs : s ∈ (es.ancestry v).walk.steps) (ht : t ∈ (es.ancestry v).walk.steps)
    (hc : (inArc es.stamp s).copy = (inArc es.stamp t).copy) : s = t := by
  induction hg generalizing v with
  | nil => simp [Log.ancestry] at hs
  | @cons es e hp hv hu hf hn hfe hsat ih =>
    have old : ∀ w, s ∈ (es.ancestry w).walk.steps → t ∈ (es.ancestry w).walk.steps → s = t :=
      fun w hs ht => ih w hs ht <| by
        simpa only [inArc, Arc.copy, (hp.stamp_cons_of_mem_ancestry hu hs).1,
          (hp.stamp_cons_of_mem_ancestry hu ht).1] using hc
    have htime : Log.stamp (e :: es) s.1 = Log.stamp (e :: es) t.1 := congrArg Prod.snd hc
    have hnew : Log.stamp (e :: es) e.input = es.length := by simp [Log.stamp]
    cases hfind : e.outputs.find? (fun o => o.var == v) with
    | some o =>
      simp only [Log.ancestry, hfind, Walk.snoc] at hs ht
      rcases List.mem_append.mp hs with hs | hs <;>
        rcases List.mem_append.mp ht with ht | ht
      · exact old _ hs ht
      · obtain rfl : t = (e.input, o) := List.mem_singleton.mp ht
        have := hp.stamp_cons_of_mem_ancestry hu hs
        dsimp only at htime
        omega
      · obtain rfl : s = (e.input, o) := List.mem_singleton.mp hs
        have := hp.stamp_cons_of_mem_ancestry hu ht
        dsimp only at htime
        omega
      · exact (List.mem_singleton.mp hs).trans (List.mem_singleton.mp ht).symm
    | none =>
      simp only [Log.ancestry, hfind] at hs ht
      exact old v hs ht

/-- The reconstructed path of every visited variable starts at one of the supplied roots. -/
theorem ancestry_start_root (hg : Grown sem f rs es) {v : V}
    (hv : es.Visited rs v) : (es.ancestry v).walk.start ∈ rs := by
  induction hg generalizing v with
  | nil => exact hv.elim id (by simp [Log.children])
  | @cons es e hp hinput hu hf hn hfe hsat ih =>
    cases hfind : e.outputs.find? (fun o => o.var == v) with
    | some o => simpa only [Log.ancestry, hfind, Walk.snoc] using ih hinput
    | none =>
      have hold : es.Visited rs v := by
        rcases hv with hv | hv
        · exact Or.inl hv
        · rcases List.mem_append.mp hv with hv | hv
          · obtain ⟨o, ho, he⟩ := List.mem_map.mp hv
            exact False.elim (List.find?_eq_none.mp hfind o ho (by simpa using he))
          · exact Or.inr hv
      simpa only [Log.ancestry, hfind] using ih hold

/-- Executable parent reconstruction gives an actual directed path in the existing DAG,
including copied-node injectivity and original-incidence trail nonreuse. -/
theorem ancestry_directed (hg : Grown sem f rs es) {v : V}
    (hv : es.Visited rs v) : DirectedPath (es.toDAG rs) (es.ancestry v).walk es.stamp where
  walk := hg.ancestry_isWalk v
  start_mem := Log.Visited.mem_vars (Or.inl (hg.ancestry_start_root hv))
  incoming _s hs := List.mem_toFinset.mpr (hg.ancestry_arcs v hs).1
  outgoing _s hs := List.mem_toFinset.mpr (hg.ancestry_arcs v hs).2
  copies_injective _s hs _t ht := hg.ancestry_copies_injective v hs ht

/-- Every variable-ended prefix of a reconstructed root path preserves validity. This uses
the existing DAG-path/surgery theorem, including repeated original constraints. -/
theorem ancestry_valid_take (hg : Grown sem f rs es) (hF : EdgeInstance F)
    (hf : ValidLabeling sem f) (hM : EdgeInstance.EvenConstraints sem F) {v : V}
    (hv : es.Visited rs v) (n : ℕ) :
    ValidLabeling sem (((es.ancestry v).walk.take n).flip f) :=
  (hg.ancestry_directed hv).valid_take (hg.isFDAG hF hf) hM n

end Grown

end Cslib.Logic.PL.CSP.Forest
