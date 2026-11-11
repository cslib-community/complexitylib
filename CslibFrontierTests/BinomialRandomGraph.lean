/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Foundations.Probability.Combinatorics.BinomialRandomGraph.Clique

/-!
# Binomial random graphs: checked instances

* Degenerate parameters: in `G(V, 1)` every set of vertices is a clique almost surely, and
  `G(V, 0)` contains no triangle almost surely.
* Expected counts: `n (n - 1) p` labelled edges and `C(n, 3) p ^ 3` triangles in `G(n, p)`.
* The second-moment bound is nonvacuous: `G(1000, 1/2)` is triangle-free with probability below
  `1 / 10`, so it contains a triangle with probability above `9 / 10`.
* Both sides of the triangle threshold are instantiated: `p(n) = 1 / (n + 1) ^ 2` lies below it
  (also for the general first-moment statement with `H = K₃`), and constant `p = 1 / 2` above it.
-/

open SimpleGraph MeasureTheory ProbabilityTheory unitInterval Finset Filter
open scoped Topology

/-! ### Degenerate parameters -/

/-- With `p = 1`, every set of vertices is a clique almost surely. -/
example (V : Type) [Countable V] (t : Finset V) :
    G(V, 1).real {G | G.IsClique (t : Set V)} = 1 := by
  rw [binomialRandom_real_isClique, Set.Icc.coe_one, one_pow]

/-- With `p = 0`, a triangle appears with probability zero. -/
example (n : ℕ) : G(Fin n, 0).real {G | ¬G.CliqueFree 3} = 0 := by
  refine le_antisymm ?_ measureReal_nonneg
  refine (binomialRandom_real_not_cliqueFree_three_le n 0).trans_eq ?_
  simp

/-! ### Expected counts -/

/-- `G(n, p)` has `n (n - 1) p` labelled edges in expectation. -/
example (n : ℕ) (p : I) :
    ∫ G, (G.labelledCopyCount (⊤ : SimpleGraph (Fin 2)) : ℝ) ∂G(Fin n, p) =
      n.descFactorial 2 * p := by
  rw [integral_labelledCopyCount, Fintype.card_fin, Fintype.card_fin]
  congr 1
  rw [card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin]
  norm_num

open Classical in
/-- `G(n, p)` has `C(n, 3) p ^ 3` triangles in expectation. -/
example (n : ℕ) (p : I) :
    ∫ G, ((G.cliqueFinset 3).card : ℝ) ∂G(Fin n, p) = n.choose 3 * (p : ℝ) ^ 3 := by
  rw [integral_card_cliqueFinset, Fintype.card_fin]
  rfl

/-! ### Nonvacuity of the second-moment bound -/

/-- `G(1000, 1/2)` is triangle-free with probability below `1 / 10`. -/
example : G(Fin 1000, ⟨1 / 2, by norm_num, by norm_num⟩).real {G | G.CliqueFree 3} < 1 / 10 := by
  refine (binomialRandom_real_cliqueFree_three_le (by norm_num) _ (by norm_num)).trans_lt ?_
  norm_num

/-- `G(1000, 1/2)` contains a triangle with probability above `9 / 10`. -/
example : 9 / 10 < G(Fin 1000, ⟨1 / 2, by norm_num, by norm_num⟩).real {G | ¬G.CliqueFree 3} := by
  rw [← Set.compl_ofPred, probReal_compl_eq_one_sub (measurableSet_cliqueFree 3)]
  have := (binomialRandom_real_cliqueFree_three_le (n := 1000) (by norm_num)
    ⟨1 / 2, by norm_num, by norm_num⟩ (by norm_num))
  norm_num at this ⊢
  linarith

/-! ### The two sides of the threshold -/

/-- The sparse edge probability `1 / (n + 1) ^ 2`. -/
noncomputable def sparseP (n : ℕ) : I :=
  ⟨1 / ((n : ℝ) + 1) ^ 2, by positivity,
    div_le_one_of_le₀ (one_le_pow₀ (by linarith [n.cast_nonneg (α := ℝ)])) (by positivity)⟩

theorem sparseP_coe (n : ℕ) : (sparseP n : ℝ) = 1 / ((n : ℝ) + 1) ^ 2 := rfl

/-- `n / (n + 1) ^ 2 → 0`. -/
theorem tendsto_mul_sparseP : Tendsto (fun n : ℕ => (n : ℝ) * sparseP n) atTop (𝓝 0) := by
  refine squeeze_zero (fun n => by rw [sparseP_coe]; positivity) (fun n => ?_)
    tendsto_one_div_add_atTop_nhds_zero_nat
  rw [sparseP_coe]
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [mul_one_div, div_le_div_iff₀ (by positivity) hn]
  nlinarith [n.cast_nonneg (α := ℝ)]

/-- Below the threshold: `G(n, 1 / (n + 1) ^ 2)` is triangle-free with probability tending to
`1`. -/
example : Tendsto (fun n => G(Fin n, sparseP n).real {G | ¬G.CliqueFree 3}) atTop (𝓝 0) :=
  tendsto_binomialRandom_real_not_cliqueFree_three tendsto_mul_sparseP

/-- The general first-moment statement with `H = K₃`: `n ^ 3 p(n) ^ 3 → 0`. -/
example : Tendsto (fun n => G(Fin n, sparseP n).real {G | (⊤ : SimpleGraph (Fin 3)) ⊑ G}) atTop
    (𝓝 0) := by
  refine tendsto_binomialRandom_real_isContained _ ?_
  have h : #(⊤ : SimpleGraph (Fin 3)).edgeFinset = 3 := by
    rw [card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin]; rfl
  simp_rw [h, Fintype.card_fin, ← mul_pow]
  simpa using tendsto_mul_sparseP.pow 3

/-- Above the threshold: `G(n, 1 / 2)` contains a triangle with probability tending to `1`. -/
example : Tendsto (fun n => G(Fin n, ⟨1 / 2, by norm_num, by norm_num⟩).real
    {G | ¬G.CliqueFree 3}) atTop (𝓝 1) := by
  refine tendsto_binomialRandom_real_not_cliqueFree_three_nhds_one ?_
  exact tendsto_natCast_atTop_atTop.atTop_mul_const (by norm_num)
