/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Foundations.Probability.Combinatorics.BinomialRandomGraph.IsolatedVertices

/-!
# Isolated vertices of binomial random graphs: checked instances

* Degenerate parameters: with `p = 0` every vertex is isolated, and with `p = 1` none is for
  `n ≥ 2`.
* On two vertices both are isolated with probability `1 - p`.
* `G(3, 1/2)` has `3 / 4` isolated vertices on average.
* The second-moment bound is nonvacuous: `G(20, 1/20)` is connected with probability below `1 / 5`.
* `p(n) = 1 / (n + 1)` lies below the connectivity threshold.
-/

open SimpleGraph MeasureTheory ProbabilityTheory unitInterval Finset Filter
open scoped Topology

/-- With `p = 0` every vertex is isolated. -/
example (n : ℕ) (v : Fin n) : G(Fin n, 0).real {G | G.IsIsolated v} = 1 := by
  rw [binomialRandom_real_isIsolated]
  simp

/-- With `p = 1` no vertex is isolated once `n ≥ 2`. -/
example (n : ℕ) (hn : 2 ≤ n) (v : Fin n) : G(Fin n, 1).real {G | G.IsIsolated v} = 0 := by
  rw [binomialRandom_real_isIsolated, Fintype.card_fin]
  simp only [Set.Icc.coe_one, sub_self]
  exact zero_pow (by omega)

/-- On two vertices both are isolated exactly when the single possible edge is absent. -/
example (p : I) : G(Fin 2, p).real {G | G.IsIsolated 0 ∧ G.IsIsolated 1} = 1 - p := by
  rw [binomialRandom_real_isIsolated_and p (by decide)]
  simp

/-- `G(3, 1/2)` has `3/4` isolated vertices on average. -/
example : ∫ G, (Nat.card {v // G.IsIsolated v} : ℝ)
    ∂G(Fin 3, ⟨1 / 2, by norm_num, by norm_num⟩) = 3 / 4 := by
  rw [integral_natCard_isIsolated]
  norm_num

/-- The second-moment bound is nonvacuous: `G(20, 1/20)` is connected with probability below
`1 / 5`. -/
example : G(Fin 20, ⟨1 / 20, by norm_num, by norm_num⟩).real {G | G.Connected} < 1 / 5 := by
  refine (binomialRandom_real_connected_le _ (by norm_num)).trans_lt ?_
  norm_num

/-- `p(n) = 1 / (n + 1)` lies below the threshold, so `G(n, 1 / (n + 1))` is disconnected with
high probability. -/
example : Tendsto (fun n : ℕ => G(Fin n, ⟨1 / (n + 1), by positivity,
    by rw [div_le_one (by positivity)]; linarith [n.cast_nonneg (α := ℝ)]⟩).real
      {G | G.Connected}) atTop (𝓝 0) := by
  refine tendsto_binomialRandom_real_connected_atBot ?_
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  refine tendsto_atBot_mono (fun n => ?_) (tendsto_neg_atTop_atBot.comp hlog |>.atBot_add
    (tendsto_const_nhds (x := (1 : ℝ))))
  have h1 : (n : ℝ) * (1 / (n + 1)) ≤ 1 := by
    rw [mul_one_div, div_le_one (by positivity)]
    linarith
  simp only [Function.comp_apply]
  linarith
