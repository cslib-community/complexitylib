/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexity.Foundations.Combinatorics.SimpleGraph.ColorRefinement
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Star

/-!
# Tests for color refinement

* The path `P₄` and the star `K₁,₃` have the same order, but color refinement separates them after
  one round, since their degree histograms differ.
* The cycle `C₆` and the disjoint union `C₃ ⊕ C₃` are both `2`-regular of order `6`, so color
  refinement gives them the same histograms in every round, but they are not isomorphic.
* Equitable and non-equitable colorings and partitions, and stable colorings of `P₃` and `C₆`; the
  stable partition of `P₃` is computed exactly.
-/

public section

open SimpleGraph

namespace Cslib.Tests.ColorRefinement

/-! ### A pair that color refinement separates -/

/-- `P₄` and `K₁,₃` are not isomorphic: after one round, the center of the star has a color of
degree `3`, which no vertex of the path has. -/
example : IsEmpty (pathGraph 4 ≃g starGraph (0 : Fin 4)) := by
  refine isEmpty_iso_of_colorHistogram_ne (n := 1) fun h => ?_
  have hmem : (starGraph (0 : Fin 4)).refinementColoring (fun _ => ()) 1 0 ∈
      (pathGraph 4).colorHistogram (fun _ => ()) 1 := by
    rw [h, mem_colorHistogram]
    exact ⟨0, rfl⟩
  obtain ⟨v, hv⟩ := mem_colorHistogram.1 hmem
  have hdeg := congrArg (fun c : RefinementColor Unit 1 => Multiset.card c.2) hv
  simp only [refinementColoring_succ, card_refineColoring_snd] at hdeg
  clear hv
  revert v
  decide

/-! ### A pair that color refinement does not separate -/

theorem cycleGraph_six_regular : (cycleGraph 6).IsRegularOfDegree 2 := by
  intro v
  revert v
  decide

theorem cycleGraph_three_regular : (cycleGraph 3).IsRegularOfDegree 2 := by
  intro v
  revert v
  decide

theorem cycleGraph_three_sum_regular : (cycleGraph 3 ⊕g cycleGraph 3).IsRegularOfDegree 2 := by
  rintro (v | v)
  · rw [← card_neighborFinset_eq_degree, neighborFinset_sum_inl, Finset.card_map,
      card_neighborFinset_eq_degree, cycleGraph_three_regular.degree_eq]
  · rw [← card_neighborFinset_eq_degree, neighborFinset_sum_inr, Finset.card_map,
      card_neighborFinset_eq_degree, cycleGraph_three_regular.degree_eq]

/-- `C₆` and `C₃ ⊕ C₃` have the same color histograms in every round. -/
example (n : ℕ) : (cycleGraph 6).colorHistogram (fun _ => ()) n =
    (cycleGraph 3 ⊕g cycleGraph 3).colorHistogram (fun _ => ()) n :=
  cycleGraph_six_regular.colorHistogram_eq cycleGraph_three_sum_regular rfl n

/-- `C₆` and `C₃ ⊕ C₃` are not isomorphic: one is connected and the other is not. -/
example : IsEmpty (cycleGraph 6 ≃g cycleGraph 3 ⊕g cycleGraph 3) :=
  ⟨fun e => not_connected_sum (e.connected_iff.1 connected_cycleGraph_add_one)⟩

/-! ### Equitable colorings and partitions -/

/-- The constant coloring of the `2`-regular graph `C₆` is equitable. -/
theorem isEquitable_cycleGraph_six : (cycleGraph 6).IsEquitable (fun _ => ()) :=
  (isEquitable_const_iff ()).2 fun v w => by
    rw [cycleGraph_six_regular.degree_eq, cycleGraph_six_regular.degree_eq]

/-- The constant coloring of `P₃` is not equitable: the middle vertex has degree `2` and the ends
have degree `1`. -/
example : ¬(pathGraph 3).IsEquitable (fun _ => ()) := by
  rw [isEquitable_const_iff]
  decide

/-- Coloring the middle vertex of `P₃` apart from the ends is equitable. -/
theorem isEquitable_pathGraph_three_middle :
    (pathGraph 3).IsEquitable (fun v : Fin 3 => decide (v = 1)) := by
  rw [isEquitable_iff_card_filter]
  decide

/-- The partition of `P₃` into the middle vertex and the ends is an equitable partition. -/
example : (pathGraph 3).IsEquitablePartition (Setoid.ker fun v : Fin 3 => decide (v = 1)) :=
  isEquitablePartition_ker_iff.2 isEquitable_pathGraph_three_middle

/-! ### Stable colorings -/

/-- The stable coloring of `P₃` separates an end from the middle vertex, because the coloring
after one round already does. -/
example : (pathGraph 3).stableColoring (fun _ => ()) 0 ≠
    (pathGraph 3).stableColoring (fun _ => ()) 1 := by
  intro h
  rw [stableColoring_eq] at h
  have h1 : (pathGraph 3).refinementColoring (fun _ => ()) 1 0 =
      (pathGraph 3).refinementColoring (fun _ => ()) 1 1 :=
    antitone_ker_refinementColoring (show 1 ≤ Fintype.card (Fin 3) by simp) h
  have hdeg := congrArg (fun c : RefinementColor Unit 1 => Multiset.card c.2) h1
  simp only [refinementColoring_succ, card_refineColoring_snd] at hdeg
  revert hdeg
  decide

/-- The stable coloring of `C₆` from the constant coloring has a single class, since the constant
coloring is already equitable. -/
example : Setoid.ker ((cycleGraph 6).stableColoring (fun _ => ())) = ⊤ := by
  refine top_le_iff.1 (le_trans ?_ (isEquitable_cycleGraph_six.ker_le_ker_stableColoring le_rfl))
  exact fun _ _ _ => rfl

/-- The stable partition of `P₃` from the constant coloring is the partition into the middle vertex
and the ends. The middle/ends partition is equitable and refines the constant coloring, so it
refines the stable partition. Conversely, the stable partition refines the partition of round `1`,
which separates the middle vertex (degree `2`) from the ends (degree `1`). -/
example : Setoid.ker ((pathGraph 3).stableColoring (fun _ => ())) =
    Setoid.ker fun v : Fin 3 => decide (v = 1) := by
  refine le_antisymm (fun v w h => ?_) ((isGreatest_ker_stableColoring (G := pathGraph 3)
    (χ₀ := fun _ => ())).2 ⟨fun _ _ _ => rfl,
      isEquitablePartition_ker_iff.2 isEquitable_pathGraph_three_middle⟩)
  rw [Setoid.ker_def, stableColoring_eq] at h
  have h1 : (pathGraph 3).refinementColoring (fun _ => ()) 1 v =
      (pathGraph 3).refinementColoring (fun _ => ()) 1 w :=
    antitone_ker_refinementColoring (show 1 ≤ Fintype.card (Fin 3) by simp) h
  have hdeg := congrArg (fun c : RefinementColor Unit 1 => Multiset.card c.2) h1
  simp only [refinementColoring_succ, card_refineColoring_snd] at hdeg
  rw [Setoid.ker_def]
  clear h h1
  revert v w
  decide

end Cslib.Tests.ColorRefinement
