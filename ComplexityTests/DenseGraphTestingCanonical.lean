/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.PropertyTesting.DenseGraph.Canonical
import Complexity.Computability.PropertyTesting.DenseGraph.TriangleFree
import ComplexityTests.DenseGraphTesting

/-! Concrete instances of canonical testers in the dense graph model: triangle-freeness is a
graph property, the canonical triangle tester obtained from the general theorem, an explicit
canonical tester on three vertices with its exact behaviour on the triangle and the empty graph,
decision properties that are too small or large enough for perfect completeness, and a sample that
is too small for soundness. -/

namespace ComplexityTests.DenseGraphTestingCanonical

open Cslib.DenseGraphTesting SimpleGraph Finset
open ComplexityTests.DenseGraphTesting (top_not_cliqueFree isFar_top)

-- Triangle-freeness is closed under relabelling the vertices.
theorem isInvariant_cliqueFree_three (n : ℕ) :
    IsInvariant (fun G : SimpleGraph (Fin n) => G.CliqueFree 3) :=
  fun π G hG => hG.comap (Embedding.comap π.toEmbedding G).isContained

-- The triangle on three vertices is not an induced subgraph of any triangle-free graph.
theorem not_inducedOf_top {n : ℕ} :
    ¬ InducedOf (fun G : SimpleGraph (Fin n) => G.CliqueFree 3) (⊤ : SimpleGraph (Fin 3)) := by
  rintro ⟨H, hH, ⟨f⟩⟩
  exact top_not_cliqueFree (hH.comap f.isContained)

open Classical in
-- The general theorem gives, for every proximity and every number of vertices, a canonical
-- one-sided triangle tester whose sample size depends only on the proximity.
example (ε : ℝ) (hε : 0 < ε) (n : ℕ) :
    IsOneSidedTester
      (canonicalTester n (min (2 * (3 * ⌈(3 * triangleRemovalBound ε)⁻¹⌉₊)) n)
        (min_le_right _ _) (InducedOf fun G : SimpleGraph (Fin n) => G.CliqueFree 3))
      (fun G => G.CliqueFree 3) ε ((2 * (3 * ⌈(3 * triangleRemovalBound ε)⁻¹⌉₊)).choose 2) :=
  OneSidedTestable.canonical isInvariant_cliqueFree_three oneSidedTestable_cliqueFree_three ε hε n

-- On three vertices five triangle trials form a one-sided tester with `15` queries.
theorem isOneSidedTester_triangleTester_three :
    IsOneSidedTester (triangleTester 3 5) (fun G => G.CliqueFree 3) (1 / 10) 15 where
  queryBounded := isQueryBounded_triangleTester 3 5
  accept G hG := by
    classical
    rw [acceptProb_triangleTester, cliqueFinset_eq_empty_iff.mpr hG]
    simp
  reject G hG := by
    classical
    have hne : (G.cliqueFinset 3).Nonempty := by
      rw [nonempty_iff_ne_empty, Ne, cliqueFinset_eq_empty_iff]
      exact fun h => not_isFar_of h (by norm_num) hG
    have hle : #(G.cliqueFinset 3) ≤ 1 := card_cliqueFinset_le.trans (by simp)
    rw [acceptProb_triangleTester, le_antisymm hle hne.card_pos]
    norm_num

open Classical in
-- Its canonical version samples `min 30 3 = 3` vertices, so it reads the whole graph, and is
-- one-sided with `30.choose 2 = 435` queries.
example :
    IsOneSidedTester
      (canonicalTester 3 (min (2 * 15) 3) (min_le_right _ _)
        (InducedOf fun G : SimpleGraph (Fin 3) => G.CliqueFree 3))
      (fun G => G.CliqueFree 3) (1 / 10) 435 :=
  isOneSidedTester_canonicalTester (isInvariant_cliqueFree_three 3)
    isOneSidedTester_triangleTester_three

open Classical in
-- The canonical tester on all three vertices rejects the triangle with certainty.
example :
    acceptProb (canonicalTester 3 3 le_rfl
      (InducedOf fun G : SimpleGraph (Fin 3) => G.CliqueFree 3)) ⊤ = 0 := by
  rw [acceptProb_canonicalTester]
  have h : {σ : Equiv.Perm (Fin 3) | InducedOf (fun G : SimpleGraph (Fin 3) => G.CliqueFree 3)
      ((⊤ : SimpleGraph (Fin 3)).comap fun i => σ (Fin.castLE le_rfl i))} = ∅ := by
    ext σ
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    have hK : ((⊤ : SimpleGraph (Fin 3)).comap fun i => σ (Fin.castLE le_rfl i)) = ⊤ := by
      ext i j
      simp only [comap_adj, top_adj, ne_eq]
      exact (σ.injective.comp (Fin.castLE_injective le_rfl)).ne_iff
    rw [hK]
    exact not_inducedOf_top
  rw [h]
  simp

open Classical in
-- It accepts the empty graph with certainty, as every canonical tester with decision property
-- `InducedOf P` accepts graphs with property `P`.
example :
    acceptProb (canonicalTester 3 3 le_rfl
      (InducedOf fun G : SimpleGraph (Fin 3) => G.CliqueFree 3)) ⊥ = 1 :=
  (acceptProb_canonicalTester_eq_one_iff le_rfl (fun G : SimpleGraph (Fin 3) => G.CliqueFree 3)
    _).2 (fun _ h => h) ⊥ (cliqueFree_bot (by norm_num))

-- A decision property that rejects everything is not perfectly complete: the empty graph is an
-- induced subgraph of itself.
example :
    ¬ ∀ G : SimpleGraph (Fin 3), G.CliqueFree 3 →
      acceptProb (canonicalTester 3 3 le_rfl fun _ => False) G = 1 := by
  rw [acceptProb_canonicalTester_eq_one_iff]
  intro h
  exact h ⊥ ⟨⊥, cliqueFree_bot (by norm_num), ⟨⟨Fin.castLEEmb le_rfl, by simp⟩⟩⟩

-- A decision property that accepts everything is perfectly complete.
example (G : SimpleGraph (Fin 3)) (hG : G.CliqueFree 3) :
    acceptProb (canonicalTester 3 3 le_rfl fun _ => True) G = 1 :=
  (acceptProb_canonicalTester_eq_one_iff le_rfl (fun G : SimpleGraph (Fin 3) => G.CliqueFree 3)
    _).2 (fun _ _ => trivial) G hG

open Classical in
-- Two sample vertices are too few on three vertices: every pair of vertices of the triangle
-- induces an edge, which is an induced subgraph of a triangle-free graph, so the triangle is
-- accepted with certainty although it is `1/10`-far from triangle-free.
example :
    ¬ IsOneSidedTester
      (canonicalTester 3 2 (by norm_num)
        (InducedOf fun G : SimpleGraph (Fin 3) => G.CliqueFree 3))
      (fun G => G.CliqueFree 3) (1 / 10) 1 := by
  intro hT
  have h₁ := hT.reject ⊤ isFar_top
  have h₂ : acceptProb (canonicalTester 3 2 (by norm_num)
      (InducedOf fun G : SimpleGraph (Fin 3) => G.CliqueFree 3)) ⊤ = 1 := by
    rw [acceptProb_canonicalTester, ENNReal.toReal_eq_one_iff,
      PMF.toOuterMeasure_apply_eq_one_iff]
    intro σ _
    simp only [Set.mem_ofPred_eq]
    have hK : ((⊤ : SimpleGraph (Fin 3)).comap
        fun i : Fin 2 => σ (Fin.castLE (by norm_num) i)) = ⊤ := by
      ext i j
      simp only [comap_adj, top_adj, ne_eq]
      exact (σ.injective.comp (Fin.castLE_injective _)).ne_iff
    rw [hK]
    -- The witness is a single edge on three vertices.
    refine ⟨(⊤ : SimpleGraph (Fin 2)).map (Fin.castLEEmb (by norm_num)), ?_,
      ⟨Embedding.map _ _⟩⟩
    exact cliqueFree_map_iff.mpr (cliqueFree_of_card_lt (by simp))
  rw [h₂] at h₁
  norm_num at h₁

end ComplexityTests.DenseGraphTestingCanonical
