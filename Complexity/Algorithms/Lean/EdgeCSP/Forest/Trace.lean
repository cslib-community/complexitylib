/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.EdgeCSP.Forest.Search

/-!
# Incidence accounting for chronological forest traces

These are representation and scan facts for Algorithm 1 of
[KazdaKolmogorovRolinek2018], arXiv:1602.03124v6, printed p. 10. Original constraints
remain positional, copied constraints retain their chronological timestamps, and no theorem
identifies different copies of the same original constraint.

## Main results

* `scan_saturated`: a completed scan covers every feasible positional partner.
* `Log.SameParent.mem_outgoing`: step 4b identifies the exact already-used port.
-/

public section

namespace Cslib.Logic.PL.CSP.Forest

open DAG

variable {Rel V : Type*} {F : CSP Rel V} [DecidableEq V]

namespace Log

/-- Output ports in reverse expansion order and each expansion's scan order. -/
@[expose] def outgoing : Log F → List (Occurrence F)
  | [] => []
  | e :: es => e.outputs ++ outgoing es

omit [DecidableEq V] in
/-- Forgetting output port positions gives precisely the discovered variables. -/
theorem children_eq_map_outgoing (es : Log F) :
    es.children = es.outgoing.map Occurrence.var := by
  induction es with
  | nil => rfl
  | cons e es ih => simp only [children, outgoing, List.map_append, ih]

omit [DecidableEq V] in
/-- Every output port is used. -/
theorem outgoing_subset_used (es : Log F) : es.outgoing ⊆ es.used := by
  induction es with
  | nil => exact List.Subset.refl _
  | cons e es ih =>
    intro o ho
    rcases List.mem_append.mp ho with ho | ho
    · exact List.mem_cons_of_mem _ (List.mem_append_left _ ho)
    · exact List.mem_cons_of_mem _ (List.mem_append_right _ (ih ho))

/-- The parent lookup returns actual output ports with the requested variable. -/
theorem parent?_sound (es : Log F) (v : V) {p : Parent F}
    (hp : es.parent? v = some p) :
    p.output ∈ es.outgoing ∧ p.output.var = v ∧ p.time < es.length := by
  induction es with
  | nil => simp [parent?] at hp
  | cons e es ih =>
    simp only [parent?] at hp
    split at hp
    next o ho =>
      cases hp
      exact ⟨List.mem_append_left _ (List.mem_of_find?_eq_some ho),
        by simpa only [beq_iff_eq] using List.find?_some ho, Nat.lt_succ_self _⟩
    next =>
      obtain ⟨hm, hv, ht⟩ := ih hp
      exact ⟨List.mem_append_right _ hm, hv, ht.trans (Nat.lt_succ_self _)⟩

/-- A skipped partner already has an actual output port at this original constraint. -/
theorem SameParent.exists_output {es : Log F} {v : V} {i : Fin F.length}
    (h : es.SameParent v i) :
    ∃ o ∈ es.outgoing, o.var = v ∧ o.1 = i := by
  unfold SameParent at h
  split at h
  · exact False.elim h
  next p hp =>
    obtain ⟨hm, hv, _⟩ := es.parent?_sound v hp
    exact ⟨p.output, hm, hv, h⟩

/-- In an edge instance a skipped feasible partner is the exact already-used positional port.
This uses the source's distinct-variable-within-a-scope convention. -/
theorem SameParent.mem_outgoing (hF : EdgeInstance F) {es : Log F} {b : Occurrence F}
    (h : es.SameParent b.var b.1) : b ∈ es.outgoing := by
  obtain ⟨o, ho, hv, hi⟩ := h.exists_output
  exact hF.eq_of_constraint_eq hv hi ▸ ho

omit [DecidableEq V] in
/-- Every recorded arc uses a recorded port, at a strictly earlier timestamp than the next
expansion. This holds even for malformed external logs. -/
theorem mem_arcs (es : Log F) {a : Arc F} (ha : a ∈ es.arcs) :
    a.occurrence ∈ es.used ∧ a.time < es.length := by
  induction es with
  | nil => simp [arcs] at ha
  | cons e es ih =>
    simp only [arcs, List.mem_cons, List.mem_append, List.mem_map] at ha
    rcases ha with rfl | ⟨o, ho, rfl⟩ | ha
    · exact ⟨List.mem_cons_self, Nat.lt_succ_self _⟩
    · exact ⟨List.mem_cons_of_mem _ (List.mem_append_left _ ho), Nat.lt_succ_self _⟩
    · obtain ⟨ho, ht⟩ := ih ha
      exact ⟨List.mem_cons_of_mem _ (List.mem_append_right _ ho),
        ht.trans (Nat.lt_succ_self _)⟩

/-- All arcs of the converted DAG have supported endpoints, including isolated roots. -/
theorem toDAG_supported (rs : List V) (es : Log F) : (es.toDAG rs).Supported := by
  intro a ha
  have hm : a ∈ es.arcs := List.mem_toFinset.mp ha
  refine ⟨List.mem_toFinset.mpr (List.mem_append_right _
    (List.mem_map.mpr ⟨a.occurrence, (es.mem_arcs hm).1, rfl⟩)), ?_⟩
  exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨a, hm, rfl⟩)

/-- A visited variable belongs to the converted DAG even when it is an isolated root. -/
theorem Visited.mem_vars {rs : List V} {es : Log F} {v : V}
    (hv : es.Visited rs v) : v ∈ (es.toDAG rs).vars := by
  apply List.mem_toFinset.mpr
  rcases hv with hv | hv
  · exact List.mem_append_left _ hv
  · rw [children_eq_map_outgoing] at hv
    obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hv
    exact List.mem_append_right _
      (List.mem_map.mpr ⟨o, es.outgoing_subset_used ho, rfl⟩)

omit [DecidableEq V] in
/-- Original occurrences of converted arcs are exactly the used ports. -/
theorem exists_arc_iff (es : Log F) (o : Occurrence F) :
    (∃ a ∈ es.arcs, a.occurrence = o) ↔ o ∈ es.used := by
  induction es with
  | nil => simp [arcs, used]
  | cons e es ih =>
    simp only [arcs, used, List.mem_cons, List.mem_append, List.mem_map]
    constructor
    · rintro ⟨a, rfl | ⟨p, hp, rfl⟩ | ha, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl hp)
      · exact Or.inr (Or.inr (ih.mp ⟨a, ha, rfl⟩))
    · rintro (rfl | ho | ho)
      · exact ⟨_, Or.inl rfl, rfl⟩
      · exact ⟨_, Or.inr (Or.inl ⟨o, ho, rfl⟩), rfl⟩
      · obtain ⟨a, ha, he⟩ := ih.mpr ho
        exact ⟨a, Or.inr (Or.inr ha), he⟩

end Log

/-- A continuing scan only adds outputs; it never discards a previously inserted child. -/
theorem scan_outputs_mono (rs : List V) (es : Log F) (input : Occurrence F)
    (bs os : List (Occurrence F)) {out : List (Occurrence F)}
    (h : scan rs es input os bs = .continued out) : os ⊆ out := by
  induction bs generalizing os with
  | nil => cases h; exact List.Subset.refl _
  | cons b bs ih =>
    simp only [scan] at h
    split at h
    · intro o ho
      exact ih _ h (List.mem_append_left _ ho)
    · split at h
      · exact ih _ h
      · cases h

/-- On completion, every candidate has an outgoing incidence, either newly discovered or
already present at a copy of this same original constraint (step 4b). This is saturation of
one actual completed scan, not a reachability assumption. -/
theorem scan_saturated (hF : EdgeInstance F) (rs : List V) (es : Log F)
    (input : Occurrence F) (bs os : List (Occurrence F))
    (hbs : ∀ b ∈ bs, b.1 = input.1) {out : List (Occurrence F)}
    (h : scan rs es input os bs = .continued out) :
    ∀ b ∈ bs, b ∈ out ++ es.outgoing := by
  induction bs generalizing os with
  | nil => simp
  | cons b bs ih =>
    simp only [scan] at h
    have htail : ∀ c ∈ bs, c.1 = input.1 := fun c hc => hbs c (List.mem_cons_of_mem b hc)
    split at h
    next hn =>
      have hm := scan_outputs_mono rs es input bs (os ++ [b]) h
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact List.mem_append_left _ (hm (by simp))
      · exact ih _ htail h c hc
    next hv =>
      split at h
      next hp =>
        have hb : b ∈ os ++ es.outgoing := by
          change b ∈ Log.outgoing ((⟨input, os⟩ : Expansion F) :: es)
          apply Log.SameParent.mem_outgoing hF
          simpa only [hbs b List.mem_cons_self] using hp
        intro c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · rcases List.mem_append.mp hb with hb | hb
          · exact List.mem_append_left _ (scan_outputs_mono rs es input bs os h hb)
          · exact List.mem_append_right _ hb
        · exact ih _ htail h c hc
      next => cases h

end Cslib.Logic.PL.CSP.Forest
