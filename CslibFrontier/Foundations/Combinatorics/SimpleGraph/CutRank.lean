/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.LinearAlgebra.Matrix.CutRank
public import CslibFrontier.Foundations.LinearAlgebra.Matrix.RankSupport
public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix

/-!
# Cut rank from exterior neighbors

For a vertex set `S` of a finite simple graph, every vertex outside `S` adjacent to `S` gives a
nonzero column of the adjacency matrix across the cut. If the vertices in `S` have degree at
most `d`, the matrix support bound gives

`|{v ∉ S | ∃ u ∈ S, G.Adj u v}| ≤ cutRank(S) * d`.

This holds over every field, including characteristic two. In particular, a neighborhood
expansion estimate gives a cut-rank lower bound without extracting an induced matching.
The result is a finite graph consequence of the sparse-matrix argument in
[C. Lee, J. Lee, and S. Oum, *Rank-width of random graphs*][LeeLeeOum2012], Lemma 4.3.

## Main results

* `SimpleGraph.ncard_externalNeighbors_le_cutRank_mul`: exterior neighbors bound cut rank
  from below when degrees on the row side are bounded.
* `SimpleGraph.card_neighbors_le_card_add_cutRank_mul`: the full neighborhood is bounded by
  the size of the set plus its cut rank times the degree bound.

## References

* [C. Lee, J. Lee, and S. Oum, *Rank-width of random graphs*][LeeLeeOum2012]
-/

public section

namespace SimpleGraph

open Finset Matrix

variable {V K : Type*} [Fintype V] [Field K] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Exterior neighbors of `S` give nonzero columns of the cut matrix. If the degrees in `S`
are at most `d`, their number is at most the cut rank times `d`, over every field. -/
theorem ncard_externalNeighbors_le_cutRank_mul (S : Set V) (d : ℕ)
    (hdegree : ∀ v ∈ S, G.degree v ≤ d) :
    ({v | v ∉ S ∧ ∃ u ∈ S, G.Adj u v} : Set V).ncard ≤
      (G.adjMatrix K).cutRank S * d := by
  classical
  let B : Matrix S ↥(Sᶜ) K := (G.adjMatrix K).submatrix Subtype.val Subtype.val
  have hrow (i : S) : #{j : ↥(Sᶜ) | B i j ≠ 0} ≤ d := by
    have hsub : (Finset.image Subtype.val {j : ↥(Sᶜ) | B i j ≠ 0}) ⊆ G.neighborFinset i := by
      intro v hv
      obtain ⟨j, hj, rfl⟩ := mem_image.mp hv
      apply (G.mem_neighborFinset _ _).mpr
      simpa [B, adjMatrix_apply] using (mem_filter.mp hj).2
    calc
      #{j : ↥(Sᶜ) | B i j ≠ 0} = #(Finset.image Subtype.val {j : ↥(Sᶜ) | B i j ≠ 0}) :=
        (card_image_of_injective _ Subtype.val_injective).symm
      _ ≤ #(G.neighborFinset i) := card_le_card hsub
      _ ≤ d := hdegree i i.property
  have hcols : #{j : ↥(Sᶜ) | ∃ i : S, B i j ≠ 0} =
      #{v : V | v ∉ S ∧ ∃ u ∈ S, G.Adj u v} := by
    refine card_bij (fun j _ ↦ (j : V)) ?_ ?_ ?_
    · intro j hj
      obtain ⟨i, hi⟩ := (mem_filter.mp hj).2
      refine mem_filter.mpr ⟨mem_univ _, j.property, i, i.property, ?_⟩
      simpa [B, adjMatrix_apply] using hi
    · intro i hi j hj hij
      exact Subtype.ext hij
    · intro v hv
      obtain ⟨hvS, u, huS, huv⟩ := (mem_filter.mp hv).2
      refine ⟨⟨v, hvS⟩, mem_filter.mpr ⟨mem_univ _, ⟨⟨u, huS⟩, ?_⟩⟩, rfl⟩
      simp [B, adjMatrix_apply, huv]
  have h := B.card_nonzero_columns_le_rank_mul d hrow
  rw [hcols, show B.rank = (G.adjMatrix K).cutRank S from
    ((G.adjMatrix K).cutRank_eq_rank S).symm] at h
  simpa only [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred] using h

/-- The full neighborhood of `S` consists of at most `|S|` internal vertices and the exterior
neighbors controlled by its cut rank. -/
theorem card_neighbors_le_card_add_cutRank_mul [DecidableEq V] (S : Finset V) (d : ℕ)
    (hdegree : ∀ v ∈ S, G.degree v ≤ d) :
    #(S.biUnion (fun v ↦ G.neighborFinset v)) ≤ #S + (G.adjMatrix K).cutRank (↑S : Set V) * d := by
  classical
  have hext : ({v | v ∉ (↑S : Set V) ∧ ∃ u ∈ (↑S : Set V), G.Adj u v} : Set V).toFinset =
      S.biUnion (fun v ↦ G.neighborFinset v) \ S := by
    ext v
    simp only [Set.mem_toFinset, Set.mem_ofPred_eq, mem_coe, mem_sdiff, mem_biUnion,
      mem_neighborFinset]
    tauto
  have h := G.ncard_externalNeighbors_le_cutRank_mul (K := K) (↑S : Set V) d hdegree
  rw [Set.ncard_eq_toFinset_card', hext] at h
  have hc : #(S.biUnion (fun v ↦ G.neighborFinset v)) ≤
      #(S.biUnion (fun v ↦ G.neighborFinset v) \ S) + #S :=
    card_le_card_sdiff_add_card
  omega

end SimpleGraph
