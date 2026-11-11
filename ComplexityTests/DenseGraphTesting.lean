/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.PropertyTesting.DenseGraph.TriangleFree

/-! Concrete instances of the dense graph model and the triangle tester on three vertices: an edit
distance, a far graph, exact acceptance probabilities, a one-sided tester with explicit
parameters, and a number of trials that is too small. -/

namespace ComplexityTests.DenseGraphTesting

open Cslib.DenseGraphTesting SimpleGraph Finset

-- The complete and the empty graph on three vertices differ in all three pairs.
example : editDist (⊤ : SimpleGraph (Fin 3)) ⊥ = 3 := by
  rw [editDist_eq_card]
  decide

-- The complete graph on three vertices is a triangle.
theorem top_not_cliqueFree : ¬ (⊤ : SimpleGraph (Fin 3)).CliqueFree 3 := fun h =>
  h univ ⟨fun _ _ _ _ huv => huv, by simp⟩

theorem card_cliqueFinset_top : #((⊤ : SimpleGraph (Fin 3)).cliqueFinset 3) = 1 := by
  decide

-- The triangle is `1/10`-far from triangle-free: at least one edge must be deleted, and
-- `1/10 · 3² < 1`.
theorem isFar_top : IsFar (⊤ : SimpleGraph (Fin 3)) (fun H => H.CliqueFree 3) (1 / 10) := by
  refine isFar_of_deleteFar (r := 1) (fun H H' hle hH' => hH'.anti hle) (fun s _ hs => ?_)
    (by norm_num)
  rcases s.eq_empty_or_nonempty with rfl | hne
  · rw [coe_empty, deleteEdges_empty] at hs
    exact absurd hs top_not_cliqueFree
  · exact_mod_cast hne.card_pos

-- A triangle-free graph is never far, for any nonnegative proximity.
example : ¬ IsFar (⊥ : SimpleGraph (Fin 3)) (fun H => H.CliqueFree 3) (1 / 10) :=
  not_isFar_of_property (cliqueFree_bot (by norm_num)) (by norm_num)

-- Exact acceptance probabilities: one trial on the triangle hits it with probability
-- `6 / 27 = 2 / 9`, and the empty graph is always accepted.
example : acceptProb (triangleTrial 2) (⊤ : SimpleGraph (Fin 3)) = 7 / 9 := by
  rw [acceptProb_triangleTrial, card_cliqueFinset_top]
  norm_num

example (k : ℕ) : acceptProb (triangleTester 3 k) (⊥ : SimpleGraph (Fin 3)) = 1 := by
  rw [acceptProb_triangleTester, cliqueFinset_eq_empty_iff.mpr (cliqueFree_bot (by norm_num))]
  simp

-- On three vertices five trials form a one-sided tester for triangle-freeness with proximity
-- `1/10` and `15` queries: a far graph contains the unique triangle, and `(7/9)^5 ≤ 1/3`.
example : IsOneSidedTester (triangleTester 3 5) (fun G => G.CliqueFree 3) (1 / 10) 15 where
  queryBounded := isQueryBounded_triangleTester 3 5
  accept G hG := by
    classical
    rw [acceptProb_triangleTester, cliqueFinset_eq_empty_iff.mpr hG]
    simp
  reject G hG := by
    classical
    have hne : (G.cliqueFinset 3).Nonempty := by
      rw [nonempty_iff_ne_empty, Ne, cliqueFinset_eq_empty_iff]
      exact fun h => not_isFar_of_property h (by norm_num) hG
    have hle : #(G.cliqueFinset 3) ≤ 1 := card_cliqueFinset_le.trans (by simp)
    rw [acceptProb_triangleTester, le_antisymm hle hne.card_pos]
    norm_num

-- One trial is too few: the triangle is far from triangle-free but is accepted with
-- probability `7/9 > 1/3`.
example : ¬ IsOneSidedTester (triangleTester 3 1) (fun G => G.CliqueFree 3) (1 / 10) 3 :=
  fun h => by
    have h₁ := h.reject ⊤ isFar_top
    rw [acceptProb_triangleTester, card_cliqueFinset_top] at h₁
    norm_num at h₁

-- The general theorem specializes to any number of vertices with a query bound depending only
-- on the proximity.
example : ∃ T : Tester 1000,
    IsOneSidedTester T (fun G => G.CliqueFree 3) (1 / 4)
      (3 * ⌈(3 * triangleRemovalBound (1 / 4))⁻¹⌉₊) :=
  oneSidedTestable_iff.mp oneSidedTestable_cliqueFree_three (1 / 4) (by norm_num) 1000

end ComplexityTests.DenseGraphTesting
