/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.FunctionalGraph.ForestIntervals
public import CslibFrontier.Foundations.Combinatorics.FunctionalGraph.ForestSegments

/-!
# Navigation through a compressed checkpoint forest

For a transient target `y`, an anchor `a` (`ForestAnchor f H L y a`) is either `y` itself when
`y ∈ forestMarks f H`, or the lower endpoint `a` of a compressed edge `IsForestEdge f H a d` of
length `d ≤ 2 * L` whose last-predecessor key `f^[d - 1] a` is reached from `y` within `k ≤ 2 * L`
steps while `transientDepth f y ≤ transientDepth f a`. On `checkpointHull f H`, every vertex has a
unique anchor (`exists_forest_anchor`, `forestAnchor_unique`), and any mark reaching `y` must pass
through `a` (`forest_anchor_contains`).

Combining a short `2 * L`-step prefix check from `x`, a selected prefix mark `h ∈ forestMarks f H`
(sound and complete for hitting `H` within `< 2 * L` steps), an anchor `a` for `y` with a short
`2 * L`-step verification prefix from `a` to `y`, and subtree interval containment
`low a ≤ low h ∧ low h ≤ high a` yields an exact characterization of reachability `∃ t, f^[t] x = y`
(`forest_navigation_spec`).

`ForestEdgeTable` packages the compressed edges of all non-root marks into a finite table of at
most `(forestMarks f H).card` entries with injective last-predecessor keys (`key_injective`),
characterizing `ForestAnchor` by key lookup and depth comparison (`ForestEdgeTable.anchor_iff`).

## Main definitions

* `Cslib.FunctionalGraph.ForestAnchor`: candidate lower endpoint for a target `y`, obtained either
  as a mark `y ∈ forestMarks f H` or via a depth-filtered last-predecessor key of a short
  compressed edge.
* `Cslib.FunctionalGraph.ForestEdgeTable`: finite table storing one short compressed edge per
  non-root mark in `forestMarks f H`.
* `Cslib.FunctionalGraph.ForestEdgeTable.key`: the last predecessor `f^[length j - 1] (start j)` of
  the `j`-th compressed edge.

## Main results

* `Cslib.FunctionalGraph.exists_forest_anchor`: every state in `checkpointHull f H` has an anchor.
* `Cslib.FunctionalGraph.forestAnchor_unique`: the anchor of any state in `checkpointHull f H` is
  unique.
* `Cslib.FunctionalGraph.forest_anchor_contains`: on `checkpointHull f H`, an anchor is a mark
  reaching `y` in at most `2 * L` steps through which every mark reaching `y` must pass.
* `Cslib.FunctionalGraph.forest_navigation_spec`: exact transient reachability via two selected
  records, interval labels, and short orbit prefixes.
* `Cslib.FunctionalGraph.exists_forest_edge_table`: existence of `ForestEdgeTable f H L`.
* `Cslib.FunctionalGraph.ForestEdgeTable.key_injective`: the last-predecessor keys of the table
  are pairwise distinct.
* `Cslib.FunctionalGraph.ForestEdgeTable.anchor_iff`: characterization of `ForestAnchor` via table
  keys.

## References

* Adapted from lean/Proofs/ForestNavigation.lean in
  [S. Schlesinger,
  *Square-root circuit bounds for iterated functions*][Schlesinger2026IteratedFunctions].
-/

@[expose] public section

namespace Cslib.FunctionalGraph

universe u
variable {α : Type u} [Finite α] (f : α → α) (H : Finset α) (L : ℕ)

/-- A candidate lower endpoint obtained from a marked target or a depth-filtered edge key. -/
def ForestAnchor (y a : α) : Prop :=
  (y ∈ forestMarks f H ∧ a = y) ∨
    ∃ d k, IsForestEdge f H a d ∧ d ≤ 2 * L ∧ k ≤ 2 * L ∧
      transientDepth f y ≤ transientDepth f a ∧ f^[k] y = f^[d - 1] a

/-- If every orbit repeats among its first `L` states or meets `H` within `2 * L` steps, every
state of `checkpointHull f H` has an anchor. -/
theorem exists_forest_anchor (hL : 0 < L)
    (hcover : ∀ x, Repeats f x L ∨ ∃ t < 2 * L, f^[t] x ∈ H)
    {y : α} (hy : y ∈ checkpointHull f H) : ∃ a, ForestAnchor f H L y a := by
  rcases forest_hull_partition f H hL hcover hy with hm | ⟨a, d, i, he, hd, hi, hiy⟩
  · exact ⟨y, Or.inl ⟨hm, rfl⟩⟩
  · refine ⟨a, Or.inr ⟨d, d - 1 - i, he, hd, by lia, ?_, ?_⟩⟩
    · rw [← hiy, transientDepth_iterate]
      exact Nat.sub_le _ _
    · rw [← hiy, ← Function.iterate_add_apply]
      congr 1
      lia

/-- Every state in `checkpointHull f H` has at most one anchor. -/
theorem forestAnchor_unique {y a₁ a₂ : α} (hy : y ∈ checkpointHull f H)
    (h₁ : ForestAnchor f H L y a₁) (h₂ : ForestAnchor f H L y a₂) : a₁ = a₂ := by
  rcases h₁ with ⟨hm₁, rfl⟩ | ⟨d₁, k₁, hedge₁, _, _, hdepth₁, he₁⟩
  · rcases h₂ with ⟨_, rfl⟩ | ⟨d₂, k₂, hedge₂, _, _, hdepth₂, he₂⟩
    · rfl
    · obtain ⟨i, hi, hiy⟩ := forest_segment_contains_of_depth f H hedge₂ hy hdepth₂ he₂
      rcases i.eq_zero_or_pos with rfl | hipos
      · simpa only [Function.iterate_zero_apply] using hiy.symm
      · exact (hedge₂.interior i hipos hi (hiy.symm ▸ hm₁)).elim
  · obtain ⟨i₁, hi₁, hiy₁⟩ := forest_segment_contains_of_depth f H hedge₁ hy hdepth₁ he₁
    rcases h₂ with ⟨hm₂, rfl⟩ | ⟨d₂, k₂, hedge₂, _, _, hdepth₂, he₂⟩
    · rcases i₁.eq_zero_or_pos with rfl | hipos
      · simpa only [Function.iterate_zero_apply] using hiy₁
      · exact (hedge₁.interior i₁ hipos hi₁ (hiy₁.symm ▸ hm₂)).elim
    · obtain ⟨i₂, hi₂, hiy₂⟩ := forest_segment_contains_of_depth f H hedge₂ hy hdepth₂ he₂
      exact (forest_edge_interior_inj f H hedge₁ hedge₂ hi₁ hi₂ (hiy₁.trans hiy₂.symm)).1

/-- All eligible keys are safe on hull points; selection need not choose the first key. -/
theorem forest_anchor_contains {y a : α} (hy : y ∈ checkpointHull f H)
    (ha : ForestAnchor f H L y a) :
    a ∈ forestMarks f H ∧ (∃ i ≤ 2 * L, f^[i] a = y) ∧
      ∀ h ∈ forestMarks f H, (∃ t, f^[t] h = y) → ∃ t, f^[t] h = a := by
  rcases ha with ⟨hm, rfl⟩ | ⟨d, k, hedge, hd, _, hdepth, he⟩
  · exact ⟨hm, ⟨0, Nat.zero_le _, rfl⟩, fun _ _ hr => hr⟩
  · obtain ⟨i, hi, hiy⟩ := forest_segment_contains_of_depth f H hedge hy hdepth he
    refine ⟨hedge.start_mem, ⟨i, hi.le.trans hd, hiy⟩, ?_⟩
    intro h hh hr
    obtain ⟨t, ht⟩ := hr
    exact forest_reaches_through_edge f H hedge hh hi (ht.trans hiy.symm)

omit [Finite α] in
/-- A target beyond a prefix remains reachable from every state in that prefix. -/
private theorem reaches_from_prefix {x y h : α} (hr : ∃ t, f^[t] x = y)
    (hfar : ∀ i ≤ 2 * L, f^[i] x ≠ y) (hp : ∃ d ≤ 2 * L, f^[d] x = h) :
    ∃ t, f^[t] h = y := by
  obtain ⟨t, ht⟩ := hr
  obtain ⟨d, hd, rfl⟩ := hp
  have hgt : 2 * L < t := by by_contra h; exact hfar t (by lia) ht
  refine ⟨t - d, ?_⟩
  rw [← Function.iterate_add_apply, Nat.sub_add_cancel (by lia : d ≤ t)]
  exact ht

/-- Exact transient reachability using two selected records and one verification prefix. -/
theorem forest_navigation_spec (hL : 0 < L)
    (hcover : ∀ x, Repeats f x L ∨ ∃ t < 2 * L, f^[t] x ∈ H)
    (low high : α → Fin (Nat.card α))
    (hinterval : ∀ x y, (low y ≤ low x ∧ low x ≤ high y) ↔
      ∃ t ≤ transientDepth f x, f^[t] x = y)
    (x y h a : α) (hy : 0 < transientDepth f y)
    (foundH foundA : Bool)
    (hHsound : foundH = true → h ∈ forestMarks f H ∧ ∃ d ≤ 2 * L, f^[d] x = h)
    (hHcomplete : (∃ d ≤ 2 * L, f^[d] x ∈ forestMarks f H) → foundH = true)
    (hAsound : foundA = true → ForestAnchor f H L y a)
    (hAcomplete : (∃ b, ForestAnchor f H L y b) → foundA = true) :
    (∃ t, f^[t] x = y) ↔ (∃ i ≤ 2 * L, f^[i] x = y) ∨
      (foundH = true ∧ foundA = true ∧ (∃ i ≤ 2 * L, f^[i] a = y) ∧
        low a ≤ low h ∧ low h ≤ high a) := by
  constructor
  · intro hr
    by_cases hshort : ∃ i ≤ 2 * L, f^[i] x = y
    · exact Or.inl hshort
    have hfar : ∀ i ≤ 2 * L, f^[i] x ≠ y := by
      intro i hi he
      exact hshort ⟨i, hi, he⟩
    obtain ⟨d, hd, hmem, _⟩ := checkpoint_before_distant_target f H hcover hy hr hfar
    have hfound : foundH = true :=
      hHcomplete ⟨d, hd.le, subset_forestMarks f H hmem⟩
    obtain ⟨hh, hprefix⟩ := hHsound hfound
    have hreach := reaches_from_prefix f L hr hfar hprefix
    have hyS := forest_transient_reachable_mem f H (forestMarks_subset_hull f H hh) hy hreach
    have hafound := hAcomplete (exists_forest_anchor f H L hL hcover hyS)
    obtain ⟨_, hverify, hthrough⟩ := forest_anchor_contains f H L hyS (hAsound hafound)
    obtain ⟨t, ht⟩ := hthrough h hh hreach
    have haPos : 0 < transientDepth f a := by
      obtain ⟨i, _, hi⟩ := hverify
      have hh := transientDepth_iterate f a i
      rw [hi] at hh
      lia
    have hdepth := transientDepth_iterate f h t
    rw [ht] at hdepth
    exact Or.inr ⟨hfound, hafound, hverify, (hinterval h a).mpr ⟨t, by lia, ht⟩⟩
  · rintro (⟨i, _, hi⟩ | ⟨hfound, _, ⟨i, _, hi⟩, hlo, hhi⟩)
    · exact ⟨i, hi⟩
    · obtain ⟨_, d, _, hd⟩ := hHsound hfound
      obtain ⟨t, _, ht⟩ := (hinterval h a).mp ⟨hlo, hhi⟩
      refine ⟨i + t + d, ?_⟩
      rw [Function.iterate_add_apply, hd, Function.iterate_add_apply, ht, hi]

/-- The finite table stores one short edge for each nonroot marked vertex. -/
structure ForestEdgeTable where
  /-- Number of stored compressed edges. -/
  count : ℕ
  /-- Lower marked endpoint of each compressed edge. -/
  start : Fin count → α
  /-- Step length of each compressed edge. -/
  length : Fin count → ℕ
  /-- Every entry is a valid compressed edge. -/
  edge : ∀ j, IsForestEdge f H (start j) (length j)
  /-- Every compressed edge has length at most `2 * L`. -/
  short : ∀ j, length j ≤ 2 * L
  /-- Lower endpoints are pairwise distinct. -/
  start_injective : Function.Injective start
  /-- Every non-root mark in `forestMarks f H` appears in the table. -/
  complete : ∀ a ∈ forestMarks f H, 0 < transientDepth f a → ∃ j, start j = a
  /-- The number of edges is at most `(forestMarks f H).card`. -/
  card_le : count ≤ (forestMarks f H).card

/-- If every orbit repeats among its first `L` states or meets `H` within `2 * L` steps, a table
of short compressed edges for the non-root marks exists. -/
theorem exists_forest_edge_table (hL : 0 < L)
    (hcover : ∀ x, Repeats f x L ∨ ∃ t < 2 * L, f^[t] x ∈ H) :
    Nonempty (ForestEdgeTable f H L) := by
  classical
  let S := (forestMarks f H).filter fun a => 0 < transientDepth f a
  let start : Fin S.card → α := fun j => (S.equivFin.symm j).val
  have hstart (j : Fin S.card) : start j ∈ forestMarks f H ∧ 0 < transientDepth f (start j) :=
    Finset.mem_filter.mp (S.equivFin.symm j).property
  have hex (j : Fin S.card) : ∃ d ≤ 2 * L, IsForestEdge f H (start j) d :=
    exists_short_forest_edge f H hL hcover (hstart j).1 (hstart j).2
  choose length hs he using hex
  refine ⟨⟨S.card, start, length, he, hs, ?_, ?_, Finset.card_le_card (Finset.filter_subset _ _)⟩⟩
  · intro i j hij
    exact S.equivFin.symm.injective (Subtype.ext hij)
  · intro a ha hd
    exact ⟨S.equivFin ⟨a, Finset.mem_filter.mpr ⟨ha, hd⟩⟩, by simp [start]⟩

namespace ForestEdgeTable

variable {f H L} (table : ForestEdgeTable f H L)

/-- The last predecessor before the upper endpoint of the `j`-th compressed edge. -/
def key (j : Fin table.count) : α := f^[table.length j - 1] (table.start j)

/-- Distinct table entries have distinct last-predecessor keys. -/
theorem key_injective : Function.Injective table.key := by
  intro i j he
  exact table.start_injective (forest_edge_last_injective f H (table.edge i) (table.edge j) he).1

/-- The edge dictionary and the depth filter characterize exactly the edge-anchor candidates. -/
theorem anchor_iff (y a : α) : ForestAnchor f H L y a ↔
    (y ∈ forestMarks f H ∧ a = y) ∨ ∃ j k, table.start j = a ∧ k ≤ 2 * L ∧
      transientDepth f y ≤ transientDepth f a ∧ f^[k] y = table.key j := by
  constructor
  · rintro (hm | ⟨d, k, hedge, hd, hk, hdepth, he⟩)
    · exact Or.inl hm
    · have haPos : 0 < transientDepth f a := lt_of_lt_of_le hedge.pos hedge.le_depth
      obtain ⟨j, hj⟩ := table.complete a hedge.start_mem haPos
      have hedge' : IsForestEdge f H a (table.length j) := hj ▸ table.edge j
      have hdEq : d = table.length j := hedge.unique f H hedge'
      exact Or.inr ⟨j, k, hj, hk, hdepth, by simpa only [key, hj, hdEq] using he⟩
  · rintro (hm | ⟨j, k, rfl, hk, hdepth, he⟩)
    · exact Or.inl hm
    · exact Or.inr ⟨table.length j, k, table.edge j, table.short j, hk, hdepth, he⟩

end ForestEdgeTable

end Cslib.FunctionalGraph
