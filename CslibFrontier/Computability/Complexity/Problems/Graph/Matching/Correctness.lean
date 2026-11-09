/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.Matching.Algorithm
public import CslibFrontier.Computability.Complexity.Problems.Graph.Matching.Comparison
import Mathlib.Data.List.GetD

/-!
# Complete unweighted matching correctness

Maximum output is optimal against every actual Mathlib matching, with no supplied solver,
model or runtime hypothesis. Successful perfect search returns exactly the original edge pairs
of a perfect Mathlib subgraph; decision is equivalent to existence of a perfect matching.
All claims use the normalized existing `Graph.induced` convention on every raw graph.
-/

public section

namespace Cslib.Complexity.Graph

open Cslib.Logic.PL CSP

variable {G : Graph}

/-- Minimum defect is maximum cardinality among all actual graph matchings. -/
theorem isMaximumMatching_positionsOfLabeling {f : OccurrenceLabeling G.matchingInstance Bool}
    (hf : IsOptimalLabeling Table.sem f) :
    (G.matchingOfPositions (G.positionsOfLabeling f)).IsMaximumMatching := by
  have hm := isMatching_positionsOfLabeling hf.1
  apply SimpleGraph.Subgraph.isMaximumMatching_iff_ncard.mpr
  refine ⟨hm, fun M hM => ?_⟩
  have hg := comparisonLabeling_valid G (positions M)
  have hle := hf.2 (G.comparisonLabeling (positions M)) hg
  have hid := defects_add_two_mul_positions hf.1
  have hgd := defects_add_two_mul_positions hg
  have hsub := Finset.card_le_card (positions_subset_comparison hM)
  have hpos : positions (G.matchingOfPositions (G.positionsOfLabeling f)) =
      G.positionsOfLabeling f := positions_matchingOfPositions
        (fun i hi => (mem_positionsOfLabeling f i).mp hi |>.1)
  rw [← card_positions M, ← card_positions _, hpos]
  omega

/-- The executable position scan is exactly the semantic mutually selected edge set. -/
theorem matchingPositions_toFinset (G : Graph) (bits : List Bool) :
    (G.matchingPositions bits).toFinset =
      G.positionsOfLabeling (CSP.EdgeAugmenting.labeling G.matchingInstance bits) := by
  ext i
  simp only [List.mem_toFinset, mem_matchingPositions, mem_positionsOfLabeling]

/-- The total algorithm returns a Mathlib maximum matching on every raw input. -/
theorem maximumMatchingSubgraph_isMaximumMatching (G : Graph) :
    G.maximumMatchingSubgraph.IsMaximumMatching := by
  obtain ⟨bits, hb, hf⟩ := matching_optimizer_spec G
  unfold maximumMatchingSubgraph maximumMatchingPositions
  rw [hb, Option.getD_some, matchingPositions_toFinset]
  exact isMaximumMatching_positionsOfLabeling hf

/-- Every returned position names an actual normalized original edge. -/
theorem maximumMatchingPositions_lt {i : ℕ} (hi : i ∈ G.maximumMatchingPositions) :
    i < G.edgeList.length := by
  exact (List.mem_filter.mp hi).1 |> List.mem_range.mp

/-- Returned canonical positions never repeat. -/
theorem nodup_maximumMatchingPositions (G : Graph) : G.maximumMatchingPositions.Nodup :=
  (List.nodup_range.filter _)

/-- Every returned edge is an original edge between distinct declared vertices. -/
theorem of_mem_maximumMatching {e : ℕ × ℕ} (he : e ∈ G.maximumMatching) :
    e ∈ G.2 ∧ e.1 ≠ e.2 ∧ e.1 ∈ G.1 ∧ e.2 ∈ G.1 := by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp he
  exact of_mem_edgeList (getD_edgeList_mem (maximumMatchingPositions_lt hi))

/-- The public edge pairs are precisely the executable conversion of returned positions. -/
theorem maximumMatching_eq_edgesAtPositions (G : Graph) :
    G.maximumMatching = G.edgesAtPositions G.maximumMatchingPositions := rfl

/-- The number of returned original edge pairs is the actual subgraph's edge cardinality. -/
theorem length_maximumMatching (G : Graph) :
    G.maximumMatching.length = G.maximumMatchingSubgraph.edgeSet.ncard := by
  rw [maximumMatching, edgesAtPositions, List.length_map, ← card_positions,
    maximumMatchingSubgraph, positions_matchingOfPositions (fun _ hi => maximumMatchingPositions_lt
      (List.mem_toFinset.mp hi)), List.toFinset_card_of_nodup (nodup_maximumMatchingPositions G)]

/-- Maximum output is as large as every actual matching, including matchings with no extension
of the particular returned edges. -/
theorem maximumMatching_cardinality (G : Graph) (M : G.induced.Subgraph) (hM : M.IsMatching) :
    M.edgeSet.ncard ≤ G.maximumMatching.length := by
  rw [length_maximumMatching]
  exact (SimpleGraph.Subgraph.isMaximumMatching_iff_ncard.mp
    (maximumMatchingSubgraph_isMaximumMatching G)).2 M hM

/-- Covered vertices of valid position sets are exactly the endpoints of selected original edges. -/
theorem mem_verts_matchingOfPositions_iff {S : Finset ℕ}
    (hS : ∀ i ∈ S, i < G.edgeList.length) (v : ℕ) (hv : v ∈ G.1) :
    (⟨v, hv⟩ : {v // v ∈ G.1}) ∈ (G.matchingOfPositions S).verts ↔
      ∃ i ∈ S, incident (G.edgeList.getD i (0, 0)) v = true := by
  constructor
  · rintro ⟨w, _, i, hi, he⟩
    refine ⟨i, hi, ?_⟩
    rcases he with h | h <;> rw [h] <;> simp [incident]
  · rintro ⟨i, hi, hinc⟩
    apply mem_verts_of_incident_positions hv _ hinc
    rw [positions_matchingOfPositions hS]
    exact hi

/-- The executable coverage scan is exactly spanning of the returned Mathlib subgraph. -/
theorem coversVertices_maximumMatching (G : Graph) :
    G.coversVertices G.maximumMatching = true ↔ G.maximumMatchingSubgraph.IsSpanning := by
  simp only [coversVertices, List.all_eq_true, mem_distinctVertices, List.any_eq_true,
    maximumMatching, edgesAtPositions, List.mem_map]
  constructor
  · intro h v
    obtain ⟨_, ⟨i, hi, rfl⟩, hinc⟩ := h v.val v.2
    exact (mem_verts_matchingOfPositions_iff
      (fun _ hi => maximumMatchingPositions_lt (List.mem_toFinset.mp hi)) v.val v.2).mpr
        ⟨i, List.mem_toFinset.mpr hi, hinc⟩
  · intro h v hv
    obtain ⟨i, hi, hinc⟩ := (mem_verts_matchingOfPositions_iff
      (fun _ hi => maximumMatchingPositions_lt (List.mem_toFinset.mp hi)) v hv).mp (h ⟨v, hv⟩)
    exact ⟨_, ⟨i, List.mem_toFinset.mp hi, rfl⟩, hinc⟩

/-- A maximum matching spans exactly when any perfect matching exists. -/
theorem maximumMatchingSubgraph_isSpanning_iff (G : Graph) :
    G.maximumMatchingSubgraph.IsSpanning ↔ ∃ M : G.induced.Subgraph, M.IsPerfectMatching := by
  constructor
  · intro h
    exact ⟨_, (maximumMatchingSubgraph_isMaximumMatching G).isMatching, h⟩
  · rintro ⟨M, hM⟩
    have hm := maximumMatchingSubgraph_isMaximumMatching G
    have hle := hm.isMatching.isMaximumMatching_iff_ncard_verts.mp hm M hM.1
    rw [hM.2.verts_eq_univ] at hle
    have heq := Set.eq_of_subset_of_ncard_le (Set.subset_univ G.maximumMatchingSubgraph.verts)
      hle (Set.toFinite _)
    exact fun v => heq ▸ Set.mem_univ v

/-- Complete successful perfect-search specification in the existing Mathlib subgraph model. -/
theorem perfectMatching_spec {edges : List (ℕ × ℕ)} (h : G.perfectMatching = some edges) :
    edges = G.maximumMatching ∧ G.maximumMatchingSubgraph.IsPerfectMatching := by
  unfold perfectMatching at h
  dsimp only at h
  split at h
  next hc =>
    cases Option.some.inj h
    exact ⟨rfl, (maximumMatchingSubgraph_isMaximumMatching G).isMatching,
      (coversVertices_maximumMatching G).mp hc⟩
  next => contradiction

/-- Complete perfect decision, including normalization, empty graphs and isolates. -/
theorem decidePerfectMatching_eq_true (G : Graph) :
    G.decidePerfectMatching = true ↔ ∃ M : G.induced.Subgraph, M.IsPerfectMatching := by
  rw [← maximumMatchingSubgraph_isSpanning_iff, ← coversVertices_maximumMatching]
  unfold decidePerfectMatching perfectMatching
  dsimp only
  split <;> simp_all

/-- Search fails exactly when the actual induced graph has no perfect matching. -/
theorem perfectMatching_eq_none_iff (G : Graph) :
    G.perfectMatching = none ↔ ¬∃ M : G.induced.Subgraph, M.IsPerfectMatching := by
  rw [← decidePerfectMatching_eq_true]
  unfold decidePerfectMatching
  cases G.perfectMatching <;> simp

end Cslib.Complexity.Graph

namespace Cslib.Complexity.Graph

/-- The returned original endpoint pairs are exactly the edges of the certified subgraph. -/
theorem maximumMatchingSubgraph_adj_iff (G : Graph) (u v : {v // v ∈ G.1}) :
    G.maximumMatchingSubgraph.Adj u v ↔
      (u.val, v.val) ∈ G.maximumMatching ∨ (v.val, u.val) ∈ G.maximumMatching := by
  constructor
  · rintro ⟨_, i, hi, he⟩
    rcases he with he | he
    · exact Or.inl (List.mem_map.mpr ⟨i, List.mem_toFinset.mp hi, he⟩)
    · exact Or.inr (List.mem_map.mpr ⟨i, List.mem_toFinset.mp hi, he⟩)
  · intro h
    have ha : G.induced.Adj u v := by
      rw [induced_adj, toSimpleGraph_adj]
      rcases h with h | h
      · obtain ⟨hm, hne, _, _⟩ := of_mem_maximumMatching h
        exact ⟨hne, Or.inl hm⟩
      · obtain ⟨hm, hne, _, _⟩ := of_mem_maximumMatching h
        exact ⟨hne.symm, Or.inr hm⟩
    refine ⟨ha, ?_⟩
    rcases h with h | h <;> obtain ⟨i, hi, he⟩ := List.mem_map.mp h
    · exact ⟨i, List.mem_toFinset.mpr hi, Or.inl he⟩
    · exact ⟨i, List.mem_toFinset.mpr hi, Or.inr he⟩

end Cslib.Complexity.Graph
