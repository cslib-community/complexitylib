/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.PropertyTesting.DenseGraph.Bipartite

/-! Concrete instances of the bipartiteness tester in the dense graph model: perfect completeness
on the empty graph, a graph far from bipartite, a one-sided tester with explicit parameters that
rejects it, a parameter choice that accepts everything, and the numeric query bound at
`ε = 1/10`. -/

namespace CslibFrontierTests.DenseGraphTestingBipartite

open Cslib.DenseGraphTesting SimpleGraph Finset

-- The empty graph is bipartite, so every run accepts it.
example (n s m : ℕ) : acceptProb (bipartiteTester n s m) (⊥ : SimpleGraph (Fin n)) = 1 :=
  acceptProb_bipartiteTester_eq_one s m
    ⟨Coloring.mk (fun _ => 0) fun h => ((bot_adj _ _).mp h).elim⟩

-- The triangle is `1/10`-far from bipartite: every bipartite graph on three vertices misses one
-- of its pairs (pigeonhole on a 2-colouring), and `1/10 · 3² < 1`.
theorem isFar_top : IsFar (⊤ : SimpleGraph (Fin 3)) (fun H => H.IsBipartite) (1 / 10) := by
  refine isFar_iff.mpr fun H ⟨C⟩ => ?_
  obtain ⟨a, b, hab, hC⟩ := Fintype.exists_ne_map_eq_of_card_lt C (by simp)
  have hnadj : ¬ H.Adj a b := fun h => C.valid h hC
  classical
  have hmem : s(a, b) ∈ symmDiff (⊤ : SimpleGraph (Fin 3)).edgeFinset H.edgeFinset := by
    rw [Finset.mem_symmDiff]
    exact Or.inl ⟨by simpa using hab, by simpa using hnadj⟩
  have h1 : (1 : ℝ) ≤ #(symmDiff (⊤ : SimpleGraph (Fin 3)).edgeFinset H.edgeFinset) := by
    exact_mod_cast Finset.card_pos.mpr ⟨_, hmem⟩
  rw [editDist_eq_card, Fintype.card_fin]
  push_cast
  linarith

-- Explicit parameters satisfying `12 ≤ ε s` and `s + 3 ≤ ε m` at `ε = 1/10`, for every `n`.
example (n : ℕ) :
    IsOneSidedTester (bipartiteTester n 120 1230) (fun G => G.IsBipartite) (1 / 10)
      (1230 * (2 * 120 + 1)) :=
  isOneSidedTester_bipartiteTester (by norm_num) (by norm_num)

-- With those parameters the triangle is rejected with probability at least `2/3`.
example : acceptProb (bipartiteTester 3 120 1230) ⊤ ≤ 1 / 3 :=
  acceptProb_bipartiteTester_le_one_third (by norm_num) (by norm_num) isFar_top

-- With no samples the tester accepts every graph,
theorem acceptProb_bipartiteTester_zero_zero (G : SimpleGraph (Fin 3)) :
    acceptProb (bipartiteTester 3 0 0) G = 1 := by
  classical
  rw [bipartiteTester_succ 2, acceptProb_bipartiteRun]
  have hacc : ∀ u x y : Fin 0 → Fin 3, bipAccept (fun k i => decide (G.Adj (x k) (u i)))
      (fun k i => decide (G.Adj (y k) (u i))) (fun k => decide (G.Adj (x k) (y k))) = true :=
    fun u x y => (bipAccept_eq_true_iff _ _ _).mpr
      ⟨Fin.elim0, Fin.elim0, Fin.elim0, fun k => k.elim0, fun k => k.elim0, fun k => k.elim0⟩
  simp [hacc]

-- so it is not a one-sided tester for any proximity at which the triangle is far.
example : ¬ IsOneSidedTester (bipartiteTester 3 0 0) (fun G => G.IsBipartite) (1 / 10) 0 :=
  fun h => by
    have h₁ := h.reject ⊤ isFar_top
    rw [acceptProb_bipartiteTester_zero_zero] at h₁
    norm_num at h₁

-- The query bound of `oneSidedTestable_isBipartite` at `ε = 1/10`: `s = 120`, `m = 1230`.
example : ⌈(⌈12 / (1 / 10 : ℝ)⌉₊ + 3 : ℝ) / (1 / 10)⌉₊ * (2 * ⌈12 / (1 / 10 : ℝ)⌉₊ + 1) =
    296430 := by
  norm_num

-- It is below `459 / ε³ = 459000`.
example : ((296430 : ℕ) : ℝ) ≤ 459 / (1 / 10 : ℝ) ^ 3 := by
  norm_num

-- A tester on a thousand vertices with that many queries.
example : ∃ T : Tester 1000, IsOneSidedTester T (fun G => G.IsBipartite) (1 / 10) 296430 := by
  obtain ⟨T, hT⟩ := oneSidedTestable_iff.mp oneSidedTestable_isBipartite (1 / 10) (by norm_num)
    1000
  refine ⟨T, ?_⟩
  convert hT using 1
  norm_num

end CslibFrontierTests.DenseGraphTestingBipartite
