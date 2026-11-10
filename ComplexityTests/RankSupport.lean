/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.Combinatorics.Expander.CutRank
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Matrix support rank bounds

A matrix with two disjoint pairs of nonzero columns attains the nonzero-column bound over
`𝔽₂`. The entry-count estimate also detects its full row rank. The empty-row case checks that
the division-free bound needs no nonempty or positive-degree hypotheses.
The graph application detects the full cut rank of two disjoint edges.
The complete graph on eight vertices supplies a concrete degree-seven spectral certificate
and a balanced-cut application.
-/

namespace ComplexityTests.RankSupport

open Finset Matrix
open scoped BigOperators

private def pairedColumns : Matrix (Fin 2) (Fin 4) (ZMod 2) :=
  !![1, 1, 0, 0; 0, 0, 1, 1]

-- The four nonzero columns and row support two force rank at least two, over characteristic two.
example : pairedColumns.rank = 2 := by
  have h := pairedColumns.card_nonzero_columns_le_rank_mul 2 (by decide)
  have hcols : ∀ j : Fin 4, ∃ i : Fin 2, pairedColumns i j ≠ 0 := by decide
  simp only [hcols, filter_true, card_univ, Fintype.card_fin] at h
  have hu := pairedColumns.rank_le_card_height
  simp only [Fintype.card_fin] at hu
  omega

-- Counting four entries with row support two and column support one gives the same sharp bound.
example : 2 ≤ pairedColumns.rank := by
  have h := pairedColumns.card_nonzero_entries_le_rank_mul_mul 2 1 (by decide) (by decide)
  have hc : #{p : Fin 2 × Fin 4 | pairedColumns p.1 p.2 ≠ 0} = 4 := by decide
  rw [hc] at h
  omega

example (M : Matrix (Fin 0) (Fin 3) ℚ) :
    #{j | ∃ i, M i j ≠ 0} ≤ M.rank * 0 :=
  M.card_nonzero_columns_le_rank_mul 0 (fun i ↦ Fin.elim0 i)

private def matching : SimpleGraph (Fin 2 × Bool) where
  Adj u v := u.1 = v.1 ∧ u.2 ≠ v.2
  symm.symm _ _ h := ⟨h.1.symm, h.2.symm⟩
  loopless.irrefl _ h := h.2 rfl

private instance : DecidableRel matching.Adj := fun u v ↦
  inferInstanceAs (Decidable (u.1 = v.1 ∧ u.2 ≠ v.2))

private def leftSide : Set (Fin 2 × Bool) := {u | u.2 = false}

private instance : DecidablePred (· ∈ leftSide) := fun u ↦
  inferInstanceAs (Decidable (u.2 = false))

-- Each of the two exterior vertices has a different incident edge, so the cut has rank two.
example : 2 ≤ (matching.adjMatrix (ZMod 2)).cutRank leftSide := by
  have h := matching.ncard_externalNeighbors_le_cutRank_mul (K := ZMod 2) leftSide 1 (by decide)
  have hc : ({v | v ∉ leftSide ∧ ∃ u ∈ leftSide, matching.Adj u v} :
      Set (Fin 2 × Bool)).ncard = 2 := by
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]
    decide
  rwa [hc, mul_one] at h

-- K₈ has normalized spectral expansion at most 1/7; its four-versus-four cut has positive rank.
example : 1 ≤ ((⊤ : SimpleGraph (Fin 8)).adjMatrix (ZMod 2)).cutRank
    (↑({0, 1, 2, 3} : Finset (Fin 8)) : Set (Fin 8)) := by
  classical
  have hregular : (⊤ : SimpleGraph (Fin 8)).IsRegularOfDegree 7 := by
    simpa using (SimpleGraph.IsRegularOfDegree.top (V := Fin 8))
  obtain ⟨G, hG, hgraph⟩ := Cslib.RotationMap.exists_isSimple_toSimpleGraph_eq hregular
  have hmatrix : G.toSimpleGraph.adjMatrix ℝ = (⊤ : SimpleGraph (Fin 8)).adjMatrix ℝ := by
    ext u v
    simp only [SimpleGraph.adjMatrix_apply, hgraph]
  have hmatrix₂ : G.toSimpleGraph.adjMatrix (ZMod 2) =
      (⊤ : SimpleGraph (Fin 8)).adjMatrix (ZMod 2) := by
    ext u v
    simp only [SimpleGraph.adjMatrix_apply, hgraph]
  have hwalk (f : Fin 8 → ℝ) (hf : 𝔼 v, f v = 0) (v : Fin 8) :
      G.walk f v = -(1 / 7 : ℝ) * f v := by
    rw [hG.walk_apply_eq_adjMatrix_mulVec_div, hmatrix, SimpleGraph.adjMatrix_mulVec_apply]
    simp only [Fintype.card_fin, Nat.cast_ofNat, SimpleGraph.neighborFinset_top]
    have hsum : ∑ w, f w = 0 := by
      simpa only [Fintype.expect_eq_sum_div_card, Fintype.card_fin, Nat.cast_ofNat,
        div_eq_zero_iff, OfNat.ofNat_ne_zero, or_false] using hf
    have heq : f v + ∑ w ∈ ({v}ᶜ : Finset (Fin 8)), f w = 0 := by
      simpa only [sum_singleton, hsum] using (sum_add_sum_compl {v} f)
    linarith
  have hspec : G.spectralExpansion ≤ 1 / 7 := by
    refine G.spectralExpansion_le (by norm_num) fun f hf ↦ ?_
    simp only [hwalk f hf, mul_pow, ← mul_expect]
    norm_num
  let S : Finset (Fin 8) := {0, 1, 2, 3}
  have h := hG.card_le_fortyOne_mul_cutRank (K := ZMod 2) (by simp)
    (hspec.trans (by norm_num)) S (by decide) (by decide)
  simp only [Fintype.card_fin, hmatrix₂] at h
  change 1 ≤ ((⊤ : SimpleGraph (Fin 8)).adjMatrix (ZMod 2)).cutRank (↑S : Set (Fin 8))
  omega

end ComplexityTests.RankSupport
