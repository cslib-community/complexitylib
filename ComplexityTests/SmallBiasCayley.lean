/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Probability.SmallBias.Random
import Complexity.Foundations.Combinatorics.Expander.Cayley
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Tests for short `ε`-biased lists and Cayley graphs of the cube. -/

namespace ComplexityTests.SmallBiasCayley

open Finset Cslib Cslib.BitString Cslib.RotationMap Cslib.Probability.PMF
open scoped BigOperators

/-- The list `(1), (0)` has one string of odd parity on `{0}`, so its character sum is
`2 - 2 · 1 = 0`. -/
example : #{j : Fin 2 | parityOn {0} (![![true], ![false]] j) = true} = 1 := by
  decide

example : ∑ j : Fin 2, chi ℝ {(0 : Fin 1)} (![![true], ![false]] j) = 0 := by
  rw [sum_chi_eq, show #{j : Fin 2 | parityOn {0} (![![true], ![false]] j) = true} = 1 by decide]
  norm_num

/-- The hypothesis of the existence theorem is satisfiable: `2 · 2 · exp(-(1/2)² · 64 / 2) < 1`,
so a list of `64` strings of one bit is `1/2`-biased. -/
example : ∃ s : Fin 64 → Fin 1 → Bool,
    IsSmallBias (1 / 2) ((uniformOfFintype (Fin 64)).map s) := by
  refine exists_isSmallBias_map_of_exp_lt (by norm_num) ?_
  have h8 : Real.exp (-((1 / 2 : ℝ) ^ 2 * (64 : ℕ) / 2)) = Real.exp (-1) ^ 8 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [Fintype.card_fin, h8]
  have h := Real.exp_neg_one_lt_half
  have h0 := (Real.exp_pos (-1)).le
  have : Real.exp (-1) ^ 8 < (1 / 2) ^ 8 := pow_lt_pow_left₀ h h0 (by norm_num)
  norm_num at this ⊢
  linarith

/-- The two strings of one bit are unbiased. -/
theorem isSmallBias_zero_pair :
    IsSmallBias 0 ((uniformOfFintype (Fin 2)).map ![![false], ![true]]) := by
  intro S hS
  have hS' : S = {0} := by
    obtain ⟨i, hi⟩ := hS
    ext j
    fin_cases i
    fin_cases j
    simpa using hi
  subst hS'
  rw [bias_uniformOfFintype_map, Fintype.expect_eq_sum_div_card]
  simp [chi, Fin.sum_univ_two]

/-- Its Cayley graph, each vertex of the one-bit cube joined to itself and to the other vertex, has
spectral expansion zero. -/
example : (cubeCayley ![![false], ![true]]).spectralExpansion ≤ 0 :=
  spectralExpansion_cubeCayley_le _ le_rfl isSmallBias_zero_pair

/-- The edge count between the two vertices of that graph matches the mixing bound exactly. -/
example : (#((cubeCayley ![![false], ![true]]).interedges {![false]} {![true]}) : ℝ) ≤ 1 := by
  have h := card_interedges_cubeCayley_le _ le_rfl isSmallBias_zero_pair {![false]} {![true]}
  simpa using h

end ComplexityTests.SmallBiasCayley
