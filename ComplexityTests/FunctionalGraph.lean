/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.Combinatorics.FunctionalGraph.CheckpointForest
import Complexity.Foundations.Combinatorics.FunctionalGraph.ForestIntervals
import Complexity.Foundations.Combinatorics.FunctionalGraph.ForestNavigation
import Complexity.Foundations.Combinatorics.FunctionalGraph.ForestSegments
import Complexity.Foundations.Data.List.Lex

/-!
# Checkpoint forest, interval label, segment, and navigation tests

Exercise `checkpointHull`, `forestMarks`, `forestPath`, `exists_forest_intervals`, `IsForestEdge`,
`ForestAnchor`, `ForestEdgeTable`, and `forest_navigation_spec` on concrete finite functional
graphs.
-/

namespace ComplexityTests.FunctionalGraph

open Cslib Cslib.FunctionalGraph Function

/-! ### Concrete functional graph: `toZero` on `Fin 2` -/

/-- Constant map `x ↦ 0` on `Fin 2`: `0` is periodic (`transientDepth = 0`) and `1` is transient
(`transientDepth = 1`). -/
private def toZero : Fin 2 → Fin 2 := fun _ => 0

private theorem transientDepth_toZero_zero : transientDepth toZero 0 = 0 :=
  transientDepth_eq_zero_of_mem_periodicPts toZero (mk_mem_periodicPts one_pos rfl)

private theorem transientDepth_toZero_one : transientDepth toZero 1 = 1 := by
  have h0 : toZero^[1] 1 ∈ periodicPts toZero := mk_mem_periodicPts one_pos rfl
  have h1 : (1 : Fin 2) ∉ periodicPts toZero := by
    rintro ⟨p, hp, hper⟩
    obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
    have hstep : toZero^[k + 1] 1 = 0 := by rw [iterate_succ_apply']; rfl
    exact absurd (hstep.symm.trans hper.eq) (by decide)
  have hle := (iterate_mem_periodicPts_iff toZero 1 1).mp h0
  have hpos : transientDepth toZero 1 ≠ 0 := fun h => h1 ((transientDepth_eq_zero_iff _ _).mp h)
  omega

-- Refine checkpoint `{1}`: the hull contains `0` and `1`, and `forestMarks` has size at most `2`.
example : (1 : Fin 2) ∈ checkpointHull toZero {1} ∧ (0 : Fin 2) ∈ checkpointHull toZero {1} ∧
    (forestMarks toZero {1}).card ≤ 2 := by
  have h1 : (1 : Fin 2) ∈ checkpointHull toZero {1} :=
    subset_checkpointHull toZero {1} (Finset.mem_singleton_self 1)
  refine ⟨h1, ?_, ?_⟩
  · have h := checkpointHull_iterate toZero {1} h1 (t := 1) (by rw [transientDepth_toZero_one])
    simpa [toZero] using h
  · simpa using forestMarks_card toZero {1}

-- Concrete `IsForestEdge` instance from `1` to `0` of length `1`.
example : IsForestEdge toZero {1} 1 1 where
  start_mem := subset_forestMarks toZero {1} (by simp)
  pos := one_pos
  le_depth := by rw [transientDepth_toZero_one]
  end_mem := by
    have h1 : (1 : Fin 2) ∈ checkpointHull toZero {1} := subset_checkpointHull toZero {1} (by simp)
    have h := forest_cycle_entry_mem toZero {1} h1
    rwa [transientDepth_toZero_one] at h
  interior i hi1 hi2 := by omega

-- Non-vacuous `ForestEdgeTable` instance for `toZero` with `H = Finset.univ` and `L = 1`.
noncomputable def sampleForestEdgeTable : ForestEdgeTable toZero Finset.univ 1 :=
  Classical.choice (exists_forest_edge_table toZero Finset.univ 1 one_pos
    (fun x => Or.inr ⟨0, by decide, Finset.mem_univ _⟩))

-- Edge-table cardinality bound, forest intervals on `toZero`, and lexicographic prefix interval
-- lemmas.
example (c : List ℕ) (h1 : [1, 2] ≤ c) (h2 : c ≤ [1, 2, 3]) :
    sampleForestEdgeTable.count ≤ (forestMarks toZero Finset.univ).card ∧
    (∃ low high : Fin 2 → Fin (Nat.card (Fin 2)),
      ∀ x y, (low y ≤ low x ∧ low x ≤ high y) ↔
        ∃ t ≤ transientDepth toZero x, toZero^[t] x = y) ∧
    [1, 2] <+: c ∧
    ([1, 2] : List ℕ) ≤ [1, 2, 3] :=
  ⟨sampleForestEdgeTable.card_le,
    exists_forest_intervals toZero,
    List.IsPrefix.of_le_of_le ⟨[3], rfl⟩ h1 h2,
    List.isPrefix_le ⟨[3], rfl⟩⟩

/-! ### Nontrivial compressed edge, navigation, and off-hull key collision on `Fin 5`

On `Fin 5`, `branchGraph` has fixed point `0`, a 3-step hull path `3 → 2 → 1 → 0` from the single
checkpoint `H = {3}` (`L = 5`), and an off-hull transient side branch `4 → 1 → 0`:
- The compressed edge from `3` to `0` has length `3` (`1 < 3`), with interior `{2, 1}` and
  last-predecessor key `branchGraph^[3 - 1] 3 = 1`.
- The reachable interior target `2` has anchor `3` and is accepted by `forest_navigation_spec`.
- The off-hull side branch `4` shares the same last-predecessor key `1` (`branchGraph^[1] 4 = 1`)
  and passes the depth filter
  (`transientDepth branchGraph 4 = 2 ≤ 3 = transientDepth branchGraph 3`), so
  `ForestAnchor branchGraph {3} 5 4 3` holds, yet the short verification prefix from `a = 3` fails
  (`∀ i ≤ 10, branchGraph^[i] 3 ≠ 4`) and `forest_navigation_spec` rejects reachability from `3`
  to `4`. -/

private def branchGraph : Fin 5 → Fin 5
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 2
  | 4 => 1

private def branchDepth : Fin 5 → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 2

private theorem branchGraph_iterate_three (x : Fin 5) : branchGraph^[3] x = 0 := by
  revert x; decide

private theorem branchGraph_iterate_add_three (x : Fin 5) (k : ℕ) :
    branchGraph^[k + 3] x = 0 := by
  induction k with
  | zero => exact branchGraph_iterate_three x
  | succ k ih =>
    rw [Nat.succ_add, iterate_succ_apply', ih]
    rfl

private theorem mem_periodicPts_branchGraph_iff (x : Fin 5) :
    x ∈ periodicPts branchGraph ↔ x = 0 := by
  refine ⟨fun ⟨p, hp, hper⟩ => ?_, fun h => h ▸ mk_mem_periodicPts one_pos rfl⟩
  have h3 : branchGraph^[p * 3] x = x := (hper.mul_const 3).eq
  obtain ⟨k, hk⟩ : ∃ k, p * 3 = k + 3 := ⟨p * 3 - 3, by omega⟩
  rw [hk, branchGraph_iterate_add_three] at h3
  exact h3.symm

private theorem le_transientDepth_branchGraph_iff (x : Fin 5) (t : ℕ) :
    transientDepth branchGraph x ≤ t ↔ branchGraph^[t] x = 0 := by
  rw [← iterate_mem_periodicPts_iff, mem_periodicPts_branchGraph_iff]

private theorem transientDepth_branchGraph (x : Fin 5) :
    transientDepth branchGraph x = branchDepth x := by
  apply le_antisymm
  · rw [le_transientDepth_branchGraph_iff]
    revert x; decide
  · by_contra hlt
    have hlt' : transientDepth branchGraph x < branchDepth x := Nat.lt_of_not_ge hlt
    have h0 : branchGraph^[transientDepth branchGraph x] x = 0 :=
      (le_transientDepth_branchGraph_iff x _).mp le_rfl
    have hne : ∀ y : Fin 5, ∀ t < branchDepth y, branchGraph^[t] y ≠ 0 := by decide
    exact hne x _ hlt' h0

private theorem mem_checkpointHull_branchGraph_iff (x : Fin 5) :
    x ∈ checkpointHull branchGraph {3} ↔ x ≠ 4 := by
  rw [mem_checkpointHull]
  simp only [Finset.mem_singleton, exists_eq_left, transientDepth_branchGraph]
  revert x; decide

private theorem mem_forestSources_branchGraph_iff (x : Fin 5) :
    x ∈ forestSources branchGraph {3} ↔ x = 1 ∨ x = 2 ∨ x = 3 := by
  rw [mem_forestSources, mem_checkpointHull_branchGraph_iff, transientDepth_branchGraph]
  revert x; decide

private theorem not_mem_forestBranches_branchGraph (x : Fin 5) :
    x ∉ forestBranches branchGraph {3} := by
  rw [mem_forestBranches]
  rintro ⟨_, hcard⟩
  obtain ⟨y₁, hy₁, y₂, hy₂, hne⟩ := Finset.one_lt_card.mp hcard
  rw [mem_forestChildren, mem_checkpointHull_branchGraph_iff, transientDepth_branchGraph] at hy₁ hy₂
  have hinj : ∀ a b : Fin 5, a ≠ 4 → 0 < branchDepth a → b ≠ 4 → 0 < branchDepth b →
      branchGraph a = branchGraph b → a = b := by decide
  exact hne (hinj y₁ y₂ hy₁.1 hy₁.2.1 hy₂.1 hy₂.2.1 (hy₁.2.2.trans hy₂.2.2.symm))

private theorem mem_forestMarks_branchGraph_iff (x : Fin 5) :
    x ∈ forestMarks branchGraph {3} ↔ x = 3 ∨ x = 0 := by
  rw [mem_forestMarks, Finset.mem_singleton, mem_forestRoots, mem_checkpointHull_branchGraph_iff,
    transientDepth_branchGraph]
  have h0 : x ≠ 4 ∧ branchDepth x = 0 ↔ x = 0 := by revert x; decide
  simp only [h0, not_mem_forestBranches_branchGraph, or_false]

-- (a) Compressed edge from `3` to `0` of length `3 > 1` (nontrivial interior `{2, 1}`).
private theorem edge_branchGraph : IsForestEdge branchGraph {3} 3 3 where
  start_mem := (mem_forestMarks_branchGraph_iff 3).mpr (Or.inl rfl)
  pos := by decide
  le_depth := by rw [transientDepth_branchGraph]; decide
  end_mem := (mem_forestMarks_branchGraph_iff _).mpr (Or.inr rfl)
  interior i hi1 hi2 := by
    rw [mem_forestMarks_branchGraph_iff]
    rcases (by omega : i = 1 ∨ i = 2) with rfl | rfl <;> decide

private theorem cover_branchGraph (x : Fin 5) :
    Repeats branchGraph x 5 ∨ ∃ t < 2 * 5, branchGraph^[t] x ∈ ({3} : Finset (Fin 5)) :=
  Or.inl ⟨3, 4, by decide, by decide, by revert x; decide⟩

-- Both the interior hull target `2` and the off-hull side branch `4` match the anchor `3` via the
-- shared last-predecessor key `branchGraph^[3 - 1] 3 = 1`.
private theorem anchor_branchGraph_two : ForestAnchor branchGraph {3} 5 2 3 :=
  Or.inr ⟨3, 1, edge_branchGraph, by decide, by decide,
    by rw [transientDepth_branchGraph, transientDepth_branchGraph]; decide, rfl⟩

private theorem anchor_branchGraph_four : ForestAnchor branchGraph {3} 5 4 3 :=
  Or.inr ⟨3, 1, edge_branchGraph, by decide, by decide,
    by rw [transientDepth_branchGraph, transientDepth_branchGraph]; decide, rfl⟩

-- (b) Positive navigation client: `forest_navigation_spec` certifies reachability of the interior
-- hull vertex `2` from `3`.
example : ∃ t, branchGraph^[t] 3 = 2 := by
  obtain ⟨low, high, hinterval⟩ := exists_forest_intervals branchGraph
  have hnav := forest_navigation_spec branchGraph {3} 5 (by decide) cover_branchGraph low high
    hinterval 3 2 3 3 (by rw [transientDepth_branchGraph]; decide) true true
    (fun _ => ⟨(mem_forestMarks_branchGraph_iff 3).mpr (Or.inl rfl), 0, by decide, rfl⟩)
    (fun _ => rfl)
    (fun _ => anchor_branchGraph_two)
    (fun _ => rfl)
  exact hnav.mpr (Or.inr ⟨rfl, rfl, ⟨1, by decide, rfl⟩,
    (hinterval 3 3).mpr ⟨0, Nat.zero_le _, rfl⟩⟩)

-- (c) Negative navigation client (off-hull key collision): `4 ∉ checkpointHull branchGraph {3}`
-- still satisfies `ForestAnchor branchGraph {3} 5 4 3` and passes the interval check for `h = 3,
-- a = 3`, but the short verification prefix from `a = 3` fails and `forest_navigation_spec`
-- rejects reachability from `3` to `4`.
example : (4 : Fin 5) ∉ checkpointHull branchGraph {3} ∧
    ForestAnchor branchGraph {3} 5 4 3 ∧
    ¬ ∃ t, branchGraph^[t] 3 = 4 := by
  obtain ⟨low, high, hinterval⟩ := exists_forest_intervals branchGraph
  have hnav := forest_navigation_spec branchGraph {3} 5 (by decide) cover_branchGraph low high
    hinterval 3 4 3 3 (by rw [transientDepth_branchGraph]; decide) true true
    (fun _ => ⟨(mem_forestMarks_branchGraph_iff 3).mpr (Or.inl rfl), 0, by decide, rfl⟩)
    (fun _ => rfl)
    (fun _ => anchor_branchGraph_four)
    (fun _ => rfl)
  have hno_prefix : ¬ ∃ i ≤ 2 * 5, branchGraph^[i] 3 = 4 := by decide
  refine ⟨by rw [mem_checkpointHull_branchGraph_iff]; decide, anchor_branchGraph_four, ?_⟩
  rw [hnav]
  rintro (hshort | ⟨_, _, hverify, _⟩)
  · exact hno_prefix hshort
  · exact hno_prefix hverify

end ComplexityTests.FunctionalGraph
