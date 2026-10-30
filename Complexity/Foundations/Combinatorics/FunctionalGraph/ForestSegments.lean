/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Combinatorics.FunctionalGraph.CheckpointForest

/-!
# Short, nonmerging segments between refined checkpoints

Between refined checkpoints in `forestMarks f H`, every non-root mark `x ∈ forestMarks f H`
(`0 < transientDepth f x`) has a unique compressed forest edge `IsForestEdge f H x d` ending at the
first positive-time visit to `forestMarks f H` (`IsForestEdge.unique`). When `H` satisfies the
`L`-step checkpoint covering property (`Repeats f x L ∨ ∃ t < 2 * L, f^[t] x ∈ H`), every
compressed edge has length `d ≤ 2 * L` (`exists_short_forest_edge`), and every state in
`checkpointHull f H` either belongs to `forestMarks f H` or lies on a compressed edge of length at
most `2 * L` (`forest_hull_partition`).

Because unmarked vertices in the hull have at most one transient hull predecessor
(`forestPredecessor_unique`), two compressed edges cannot merge in their interiors
(`forest_edge_interior_inj`), so each compressed edge is uniquely identified by its last predecessor
`f^[d - 1] x` before its upper endpoint (`forest_edge_last_injective`).

## Main definitions

* `Cslib.FunctionalGraph.IsForestEdge`: compressed edge from a mark `x ∈ forestMarks f H` to the
  next mark `f^[d] x ∈ forestMarks f H` along the transient path.

## Main results

* `Cslib.FunctionalGraph.IsForestEdge.unique`: the length `d` of a compressed edge from `x` is
  unique.
* `Cslib.FunctionalGraph.exists_short_forest_edge`: every non-root mark has a compressed edge of
  length at most `2 * L`.
* `Cslib.FunctionalGraph.forest_edge_interior_inj`: interiors of compressed edges are disjoint.
* `Cslib.FunctionalGraph.forest_edge_last_injective`: the last predecessor `f^[d - 1] x` uniquely
  identifies `(x, d)`.
* `Cslib.FunctionalGraph.forest_hull_partition`: every state in `checkpointHull f H` is either a
  mark or lies on a compressed edge of length at most `2 * L`.
* `Cslib.FunctionalGraph.forest_segment_contains_of_depth`: depth filtering ensures any matching
  last-predecessor key on a short prefix identifies the containing compressed edge.
* `Cslib.FunctionalGraph.forest_reaches_through_edge`: any mark reaching the interior of a
  compressed edge passes through its lower endpoint.
* `Cslib.FunctionalGraph.checkpoint_before_distant_target`: any transient target at distance
  greater than `2 * L` is preceded by a checkpoint in `H` within fewer than `2 * L` steps.

## References

* Adapted from lean/Proofs/ForestSegments.lean in
  [S. Schlesinger,
  *Square-root circuit bounds for iterated functions*][Schlesinger2026IteratedFunctions].
-/

@[expose] public section

namespace Cslib.FunctionalGraph

universe u
variable {α : Type u} [Finite α] (f : α → α) (H : Finset α)

/-- The cycle entry `f^[transientDepth f x] x` of a hull state `x` is marked. -/
theorem forest_cycle_entry_mem {x : α} (hx : x ∈ checkpointHull f H) :
    f^[transientDepth f x] x ∈ forestMarks f H := by
  apply forestRoot_mem_marks f H (checkpointHull_iterate f H hx le_rfl)
  rw [transientDepth_iterate, Nat.sub_self]

/-- For a hull state `x` and `i < transientDepth f x`, the state `f^[i] x` is a forest source. -/
theorem forest_iterate_mem_sources {x : α} (hx : x ∈ checkpointHull f H)
    {i : ℕ} (hi : i < transientDepth f x) : f^[i] x ∈ forestSources f H := by
  apply (mem_forestSources f H _).mpr
  refine ⟨checkpointHull_iterate f H hx hi.le, ?_⟩
  rw [transientDepth_iterate]
  lia

/-- A compressed edge ends at the next mark, no later than cycle entry. -/
structure IsForestEdge (x : α) (d : ℕ) : Prop where
  /-- The starting vertex is a refined mark. -/
  start_mem : x ∈ forestMarks f H
  /-- The edge has positive length. -/
  pos : 0 < d
  /-- The edge does not cross the cycle entry of `x`. -/
  le_depth : d ≤ transientDepth f x
  /-- The upper endpoint is a refined mark. -/
  end_mem : f^[d] x ∈ forestMarks f H
  /-- No intermediate vertex is a refined mark. -/
  interior : ∀ i, 0 < i → i < d → f^[i] x ∉ forestMarks f H

/-- Every state `f^[i] x` with `i < d` on a compressed edge is a forest source. -/
theorem IsForestEdge.source {x : α} {d : ℕ} (h : IsForestEdge f H x d)
    {i : ℕ} (hi : i < d) : f^[i] x ∈ forestSources f H :=
  forest_iterate_mem_sources f H (forestMarks_subset_hull f H h.start_mem) (hi.trans_le h.le_depth)

/-- The length of a compressed edge from `x` is unique. -/
theorem IsForestEdge.unique {x : α} {d₁ d₂ : ℕ}
    (h₁ : IsForestEdge f H x d₁) (h₂ : IsForestEdge f H x d₂) : d₁ = d₂ := by
  apply le_antisymm
  · by_contra h
    exact h₁.interior d₂ h₂.pos (by lia) h₂.end_mem
  · by_contra h
    exact h₂.interior d₁ h₁.pos (by lia) h₁.end_mem

/-- Applying checkpoint coverage after one step bounds each compressed edge by `2 * L`. -/
theorem exists_short_forest_edge {L : ℕ} (_hL : 0 < L)
    (hcover : ∀ x, Repeats f x L ∨ ∃ t < 2 * L, f^[t] x ∈ H)
    {x : α} (hx : x ∈ forestMarks f H) (hd : 0 < transientDepth f x) :
    ∃ d ≤ 2 * L, IsForestEdge f H x d := by
  classical
  have hxS := forestMarks_subset_hull f H hx
  have hroot := forest_cycle_entry_mem f H hxS
  have hex : ∃ d, 0 < d ∧ f^[d] x ∈ forestMarks f H := ⟨_, hd, hroot⟩
  have hshort : ∃ t, 0 < t ∧ t ≤ 2 * L ∧ f^[t] x ∈ forestMarks f H := by
    rcases hcover (f x) with ⟨i, j, hij, hj, he⟩ | ⟨t, ht, hmem⟩
    · have hperiod := transientDepth_add_cycleLength_le_of_iterate_eq f (f x) hij he
      have hdepth : transientDepth f (f x) = transientDepth f x - 1 := by
        simpa only [Function.iterate_one] using transientDepth_iterate f x 1
      exact ⟨_, hd, by lia, hroot⟩
    · refine ⟨t + 1, by lia, by lia, ?_⟩
      rw [Function.iterate_succ_apply]
      exact subset_forestMarks f H hmem
  let d := Nat.find hex
  have hspec := Nat.find_spec hex
  have hdepth : d ≤ transientDepth f x := Nat.find_min' hex ⟨hd, hroot⟩
  obtain ⟨t, ht, htL, htm⟩ := hshort
  have hdt : d ≤ t := Nat.find_min' hex ⟨ht, htm⟩
  refine ⟨d, hdt.trans htL, hx, hspec.1, hdepth, hspec.2, ?_⟩
  intro i hi hid him
  exact Nat.find_min hex hid ⟨hi, him⟩

/-- Interiors of compressed edges are disjoint, including their starting marks. -/
theorem forest_edge_interior_inj {x y : α} {d e : ℕ}
    (hx : IsForestEdge f H x d) (hy : IsForestEdge f H y e)
    {i j : ℕ} (hi : i < d) (hj : j < e) (he : f^[i] x = f^[j] y) :
    x = y ∧ i = j := by
  induction i generalizing j with
  | zero =>
    cases j with
    | zero => exact ⟨he, rfl⟩
    | succ j =>
      have hnot := hy.interior (j + 1) (by lia) hj
      exact (hnot (he ▸ hx.start_mem)).elim
  | succ i ih =>
    cases j with
    | zero =>
      have hnot := hx.interior (i + 1) (by lia) hi
      exact (hnot (he.symm ▸ hy.start_mem)).elim
    | succ j =>
      have hpred : f^[i] x = f^[j] y := by
        apply forestPredecessor_unique f H (hx.source f H (by lia)) (hy.source f H (by lia))
          (z := f^[i + 1] x)
        · exact (Function.iterate_succ_apply' f i x).symm
        · exact (Function.iterate_succ_apply' f j y).symm.trans he.symm
        · exact hx.interior (i + 1) (by lia) hi
      obtain ⟨hxy, hij⟩ := ih (by lia) (by lia) hpred
      exact ⟨hxy, by lia⟩

/-- Last-predecessor keys identify compressed edges uniquely. -/
theorem forest_edge_last_injective {x y : α} {d e : ℕ}
    (hx : IsForestEdge f H x d) (hy : IsForestEdge f H y e)
    (he : f^[d - 1] x = f^[e - 1] y) : x = y ∧ d = e := by
  have h := forest_edge_interior_inj f H hx hy (by have := hx.pos; lia) (by have := hy.pos; lia) he
  exact ⟨h.1, by have := hx.pos; have := hy.pos; lia⟩

/-- Every hull point is marked or belongs to a short compressed edge. -/
theorem forest_hull_partition {L : ℕ} (hL : 0 < L)
    (hcover : ∀ x, Repeats f x L ∨ ∃ t < 2 * L, f^[t] x ∈ H)
    {y : α} (hy : y ∈ checkpointHull f H) :
    y ∈ forestMarks f H ∨ ∃ a d i, IsForestEdge f H a d ∧
      d ≤ 2 * L ∧ i < d ∧ f^[i] a = y := by
  have visit (t : ℕ) : ∀ a ∈ forestMarks f H, t ≤ transientDepth f a →
      f^[t] a ∈ forestMarks f H ∨ ∃ b d i, IsForestEdge f H b d ∧
        d ≤ 2 * L ∧ i < d ∧ f^[i] b = f^[t] a := by
    induction t using Nat.strong_induction_on with
    | ind t ih =>
      intro a ha ht
      by_cases hz : t = 0
      · subst t
        exact Or.inl ha
      obtain ⟨d, hd, hedge⟩ := exists_short_forest_edge f H hL hcover ha (by lia)
      by_cases htd : t < d
      · exact Or.inr ⟨a, d, t, hedge, hd, htd, rfl⟩
      have hdpos := hedge.pos
      have he : f^[t - d] (f^[d] a) = f^[t] a := by
        rw [← Function.iterate_add_apply, Nat.sub_add_cancel (by lia : d ≤ t)]
      have hh := ih (t - d) (by lia) (f^[d] a) hedge.end_mem (by
        rw [transientDepth_iterate]
        lia)
      simpa only [he] using hh
  obtain ⟨a, ha, t, ht, rfl⟩ := (mem_checkpointHull f H y).mp hy
  exact visit t a (subset_forestMarks f H ha) ht

/-- A matched interior can be traced backwards as far as its lower endpoint. -/
private theorem forest_backtrack_interior {a y : α} {d i j : ℕ}
    (ha : IsForestEdge f H a d) (hy : y ∈ checkpointHull f H)
    (hi : i < d) (hji : j ≤ i) (hj : j < transientDepth f y)
    (he : f^[i] a = f^[j] y) : f^[i - j] a = y := by
  induction j generalizing i with
  | zero => simpa only [Nat.sub_zero, Function.iterate_zero_apply] using he
  | succ j ih =>
    cases i with
    | zero => lia
    | succ i =>
      have hpred : f^[i] a = f^[j] y := by
        apply forestPredecessor_unique f H (ha.source f H (by lia))
          (forest_iterate_mem_sources f H hy (by lia)) (z := f^[i + 1] a)
        · exact (Function.iterate_succ_apply' f i a).symm
        · exact (Function.iterate_succ_apply' f j y).symm.trans he.symm
        · exact ha.interior (i + 1) (by lia) hi
      simpa only [Nat.succ_sub_succ_eq_sub] using ih (by lia) (by lia) (by lia) hpred

/-- Depth filtering makes any eligible last-predecessor match identify the containing edge. -/
theorem forest_segment_contains_of_depth {a y : α} {d k : ℕ}
    (ha : IsForestEdge f H a d) (hy : y ∈ checkpointHull f H)
    (hdepth : transientDepth f y ≤ transientDepth f a)
    (he : f^[k] y = f^[d - 1] a) : ∃ i < d, f^[i] a = y := by
  have hd : d - 1 < d := by have := ha.pos; lia
  have hlast := (mem_forestSources f H _).mp (ha.source f H hd)
  have hdy := transientDepth_iterate f y k
  have hda := transientDepth_iterate f a (d - 1)
  rw [he] at hdy
  have hbound := ha.le_depth
  have hk : k < transientDepth f y := by lia
  have hkd : k ≤ d - 1 := by lia
  exact ⟨d - 1 - k, by lia,
    forest_backtrack_interior f H ha hy hd hkd hk he.symm⟩

/-- A marked vertex reaches an edge interior only by passing its lower marked endpoint. -/
theorem forest_reaches_through_edge {a h : α} {d i t : ℕ}
    (ha : IsForestEdge f H a d) (hh : h ∈ forestMarks f H)
    (hi : i < d) (he : f^[t] h = f^[i] a) : ∃ u, f^[u] h = a := by
  induction i generalizing t with
  | zero => exact ⟨t, he⟩
  | succ i ih =>
    cases t with
    | zero => exact (ha.interior (i + 1) (by lia) hi (he ▸ hh)).elim
    | succ t =>
      have htarget := (mem_forestSources f H _).mp (ha.source f H hi)
      have hdepth := transientDepth_iterate f h (t + 1)
      rw [he] at hdepth
      have ht : t < transientDepth f h := by lia
      have hpred : f^[t] h = f^[i] a := by
        apply forestPredecessor_unique f H
          (forest_iterate_mem_sources f H (forestMarks_subset_hull f H hh) ht)
          (ha.source f H (by lia)) (z := f^[i + 1] a)
        · exact (Function.iterate_succ_apply' f t h).symm.trans he
        · exact (Function.iterate_succ_apply' f i a).symm
        · exact ha.interior (i + 1) (by lia) hi
      exact ih (by lia) hpred

/-- A state of positive transient depth that is reachable from a hull state lies in the hull. -/
theorem forest_transient_reachable_mem {x y : α} (hx : x ∈ checkpointHull f H)
    (hy : 0 < transientDepth f y) (hr : ∃ t, f^[t] x = y) : y ∈ checkpointHull f H := by
  obtain ⟨t, ht⟩ := hr
  have hd := transientDepth_iterate f x t
  rw [ht] at hd
  have hmem := checkpointHull_iterate f H hx (t := t) (by lia)
  exact ht ▸ hmem

/-- A transient target beyond the inspected prefix lies above a prefix checkpoint. -/
theorem checkpoint_before_distant_target {L : ℕ}
    (hcover : ∀ x, Repeats f x L ∨ ∃ t < 2 * L, f^[t] x ∈ H)
    {x y : α} (hy : 0 < transientDepth f y) (hr : ∃ t, f^[t] x = y)
    (hfar : ∀ i ≤ 2 * L, f^[i] x ≠ y) :
    ∃ d < 2 * L, f^[d] x ∈ H ∧ ∃ u, f^[u] (f^[d] x) = y := by
  obtain ⟨t, ht⟩ := hr
  have hgt : 2 * L < t := by by_contra h; exact hfar t (by lia) ht
  have hdepth := transientDepth_iterate f x t
  rw [ht] at hdepth
  rcases hcover x with ⟨i, j, hij, hj, he⟩ | ⟨d, hd, hmem⟩
  · have hrepeat := transientDepth_add_cycleLength_le_of_iterate_eq f x hij he
    lia
  · refine ⟨d, hd, hmem, t - d, ?_⟩
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel (by lia : d ≤ t)]
    exact ht

end Cslib.FunctionalGraph
