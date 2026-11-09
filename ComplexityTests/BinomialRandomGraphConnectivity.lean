/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.Probability.Combinatorics.BinomialRandomGraph.Connectivity

/-!
# Connectivity of binomial random graphs: checked instances

* Every event about a random graph on finitely many vertices is measurable.
* Degenerate parameters: `G(n, 1)` is connected almost surely for `n ≥ 1`, and `G(n, 0)` is
  disconnected almost surely for `n ≥ 2`.
* The union bound over cuts on two vertices gives `2 (1 - p)`; the true value is `1 - p`.
* The explicit bound is nonvacuous: `G(20, 1/2)` is disconnected with probability below `1 / 20`.
* Constant `p = 1 / 2` lies above the connectivity threshold.
-/

open SimpleGraph MeasureTheory ProbabilityTheory unitInterval Finset Filter
open scoped Topology

/-! ### Measurability and degenerate parameters -/

/-- Every set of graphs on finitely many vertices is measurable. -/
example : DiscreteMeasurableSpace (SimpleGraph (Fin 3)) := inferInstance

/-- With `p = 1`, `G(n, 1)` is connected almost surely for `n ≥ 1`. -/
example (n : ℕ) (hn : 0 < n) : G(Fin n, 1).real {G | G.Connected} = 1 := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [binomialRandom_one, measureReal_def, Measure.dirac_apply_of_mem]
  · rfl
  · exact connected_top_iff.2 ‹_›

/-- With `p = 0`, `G(n, 0)` is disconnected almost surely for `n ≥ 2`. -/
example (n : ℕ) (hn : 2 ≤ n) : G(Fin n, 0).real {G | G.Connected} = 0 := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 hn
  rw [binomialRandom_zero, measureReal_def, Measure.dirac_apply' _ .of_discrete,
    Set.indicator_of_notMem (not_connected_bot (V := Fin n))]
  rfl

/-! ### The union bound and the explicit bound -/

/-- On two vertices the union bound over cuts gives `2 (1 - p)`. This is not exact: the true value
is `1 - p`, and the sum counts both `S` and its complement when `|S| = n / 2`. -/
example (p : I) : G(Fin 2, p).real {G | ¬G.Connected} ≤ 2 * (1 - p) := by
  have := binomialRandom_real_not_connected_le_sum (V := Fin 2) p
  simpa using this

/-- The explicit bound is nonvacuous: `G(20, 1/2)` is disconnected with probability below
`1 / 20`. -/
example : G(Fin 20, ⟨1 / 2, by norm_num, by norm_num⟩).real {G | ¬G.Connected} < 1 / 20 := by
  have hE := Real.exp_one_gt_d9
  have h10 : (20000 : ℝ) < Real.exp 10 := by
    have : Real.exp 10 = Real.exp 1 ^ 10 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    calc (20000 : ℝ) < 2.7 ^ 10 := by norm_num
      _ ≤ Real.exp 1 ^ 10 := by gcongr; linarith
  have he : Real.exp (-((20 : ℕ) * (1 / 2 : ℝ))) = (Real.exp 10)⁻¹ := by
    rw [← Real.exp_neg]; norm_num
  have hy : ((20 : ℕ) : ℝ) * Real.exp (-((20 : ℕ) * (1 / 2 : ℝ))) < 1 / 1000 := by
    rw [he, ← div_eq_mul_inv, div_lt_iff₀ (by positivity)]; push_cast; linarith
  refine (binomialRandom_real_not_connected_le (n := 20) (by norm_num) _ ?_).trans_lt ?_
  · exact hy.le.trans (by norm_num)
  · have := hy; simp only at this ⊢; linarith

/-! ### Above the threshold -/

/-- Constant `p = 1 / 2` lies above the threshold: `n / 2 - log n → ∞`. -/
example : Tendsto (fun n => G(Fin n, ⟨1 / 2, by norm_num, by norm_num⟩).real {G | G.Connected})
    atTop (𝓝 1) := by
  refine tendsto_binomialRandom_real_connected ?_
  have hlog : ∀ n : ℕ, Real.log n ≤ n / Real.exp 1 := fun n => by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    have h := Real.log_le_sub_one_of_pos (x := n / Real.exp 1) (by positivity)
    rw [Real.log_div (by positivity) (Real.exp_pos 1).ne', Real.log_exp] at h
    linarith
  have hE := Real.exp_one_gt_d9
  have hc : (0 : ℝ) < 1 / 2 - 1 / Real.exp 1 := by
    rw [sub_pos, div_lt_div_iff₀ (Real.exp_pos 1) (by norm_num)]; norm_num at hE ⊢; linarith
  refine tendsto_atTop_mono (fun n => ?_)
    ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hc)
  have := hlog n
  simp only
  linear_combination this
