/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.GameTheory.Congestion.PigouBound

/-!
# The Pigou bound

Checked instances of the Pigou bound for nonatomic selfish routing:

* Pigou's ratio for `c(x) = x`, rate `1` and `1/2` unit of traffic on the first link is `4/3`.
* The Pigou bound of constant latencies is `1` and that of affine latencies (`d = 1`) is `4/3`.
* With quadratic latencies the Wardrop equilibrium of Pigou's `x ^ 2` network costs `8/5` times a
  feasible flow, more than the affine bound `4/3`, and the polynomial theorem bounds it.
* Allowing polynomials of every degree makes the Pigou bound infinite, so the finiteness hypothesis
  of the general theorem is not automatic.
* The tightness theorem applies to polynomial latencies, and both directions of
  `pigouBound_le_ofReal_iff` hold for affine latencies: `4/3` bounds every game and `13/10` does
  not.
-/

namespace ComplexityTests.GameTheory.PigouBound

open Cslib.GameTheory NonatomicCongestionGame

/-- Pigou's original ratio: `c(x) = x`, `r = 1`, `x = 1/2`. -/
example : pigouRatio (fun x => x) 1 (1 / 2) = ENNReal.ofReal (4 / 3) := by
  norm_num [pigouRatio]

/-- Constant latencies (`d = 0`) have Pigou bound `1`: selfish routing is optimal. -/
example : pigouBound (polynomialLatencies 0) = 1 := by
  rw [pigouBound_polynomialLatencies]
  norm_num

/-- Affine latencies (`d = 1`) have Pigou bound `4/3`. -/
example : pigouBound (polynomialLatencies 1) = ENNReal.ofReal (4 / 3) :=
  pigouBound_polynomialLatencies_one

/-- Pigou's quadratic network: latency `x ^ 2` and `1`, one unit of traffic. -/
noncomputable abbrev quadratic : NonatomicCongestionGame Unit (Fin 2) (Fin 2) :=
  pigouNetwork (fun x => x ^ 2) 1

theorem quadratic_latency_mem (e : Fin 2) : quadratic.latency e ∈ polynomialLatencies 2 := by
  fin_cases e
  · exact pow_mem_polynomialLatencies 2
  · refine ⟨![1, 0, 0], fun i => by fin_cases i <;> norm_num, fun x => ?_⟩
    simp [quadratic, pigouNetwork, Fin.sum_univ_succ]

/-- In the quadratic network the equilibrium costs `8/5` times the even split, which exceeds the
affine bound `4/3`. -/
example : quadratic.cost ![1, 0] = 8 / 5 * quadratic.cost ![1 / 2, 1 / 2] ∧
    ¬ quadratic.cost ![1, 0] ≤ 4 / 3 * quadratic.cost ![1 / 2, 1 / 2] := by
  rw [pigouNetwork_cost, pigouNetwork_cost]
  norm_num

/-- The polynomial theorem bounds every feasible flow of the quadratic network. -/
example (g : Fin 2 → ℝ) (hg : quadratic.IsFeasible g) :
    quadratic.cost ![1, 0] ≤
      (1 - ((2 : ℕ) : ℝ) * (((2 : ℕ) : ℝ) + 1) ^ (-((((2 : ℕ) : ℝ) + 1) / ((2 : ℕ) : ℝ))))⁻¹ *
        quadratic.cost g :=
  (pigouNetwork_isWardrop _ zero_le_one).cost_le_of_mem_polynomialLatencies quadratic_latency_mem
    hg

/-- Polynomials of unbounded degree have infinite Pigou bound: with `x ^ n` for large `n` and
`1 - 1/k` units on the first link, the ratio exceeds `k / 2`. -/
example : pigouBound (⋃ d, polynomialLatencies d) = ⊤ := by
  refine ENNReal.eq_top_of_forall_nnreal_le fun M => ?_
  set k : ℝ := 2 * M + 2 with hk
  have hk0 : 0 < k := by positivity
  have hk1 : 1 / k < 1 := by rw [div_lt_one hk0]; linarith [M.coe_nonneg]
  have hk1' : 0 < 1 / k := one_div_pos.2 hk0
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hk1' (by linarith : 1 - 1 / k < 1)
  have hx : 0 ≤ 1 - 1 / k := by linarith
  have hD : 0 < (1 - 1 / k) * (1 - 1 / k) ^ n + 1 / k := by positivity
  have hDlt : (1 - 1 / k) * (1 - 1 / k) ^ n + 1 / k < 2 / k := by
    have : (1 - 1 / k) * (1 - 1 / k) ^ n ≤ (1 - 1 / k) ^ n :=
      mul_le_of_le_one_left (pow_nonneg hx _) (by linarith)
    rw [show 2 / k = 1 / k + 1 / k by ring]
    linarith
  have hmem : (fun x : ℝ => x ^ n) ∈ ⋃ d, polynomialLatencies d :=
    Set.mem_iUnion.2 ⟨n, pow_mem_polynomialLatencies n⟩
  refine le_trans ?_ (pigouRatio_le_pigouBound hmem zero_le_one hx)
  rw [← ENNReal.ofReal_coe_nnreal, pigouRatio]
  refine ENNReal.ofReal_le_ofReal ?_
  simp only [one_pow, mul_one, sub_sub_cancel]
  rw [le_div_iff₀ hD]
  have h2k : (M : ℝ) * (2 / k) < 1 := by
    rw [mul_div_assoc', div_lt_one hk0]; linarith
  nlinarith [M.coe_nonneg]

/-- Nonnegative constant functions are affine latencies. -/
theorem const_mem_polynomialLatencies_one (a : ℝ) (ha : 0 ≤ a) :
    (fun _ => a) ∈ polynomialLatencies 1 :=
  ⟨![a, 0], fun i => by fin_cases i <;> simp [ha], fun x => by simp⟩

/-- The tightness theorem: for affine latencies, some Pigou-like network beats every ratio below
`4/3`. -/
example : ∃ (G : NonatomicCongestionGame Unit (Fin 2) (Fin 2)) (f g : Fin 2 → ℝ),
    (∀ e, G.latency e ∈ polynomialLatencies 1) ∧ G.IsWardrop f ∧ G.IsFeasible g ∧
      0 < G.cost g ∧ 13 / 10 * G.cost g < G.cost f := by
  refine exists_lt_cost_of_lt_pigouBound (C := polynomialLatencies 1)
    (fun c hc x hx => nonneg_of_mem_polynomialLatencies hc hx)
    (fun c hc => monotoneOn_of_mem_polynomialLatencies hc) const_mem_polynomialLatencies_one ?_
  rw [pigouBound_polynomialLatencies_one, ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
  norm_num

/-- The exact worst case, `→`: since the Pigou bound of affine latencies is `4/3`, every game with
latencies in `polynomialLatencies 1`, of any topology, has price of anarchy at most `4/3`. -/
example (K P E : Type) [Fintype P] [Finite E] [DecidableEq K] [DecidableEq E]
    (G : NonatomicCongestionGame K P E) (f g : P → ℝ)
    (hG : ∀ e, G.latency e ∈ polynomialLatencies 1)
    (hf : G.IsWardrop f) (hg : G.IsFeasible g) : G.cost f ≤ 4 / 3 * G.cost g :=
  (pigouBound_le_ofReal_iff (fun _ hc _ hx => nonneg_of_mem_polynomialLatencies hc hx)
    (fun _ hc => monotoneOn_of_mem_polynomialLatencies hc) const_mem_polynomialLatencies_one).1
    pigouBound_polynomialLatencies_one.le K P E G f g hG hf hg

/-- The exact worst case, `←`: the ratio `13/10 < 4/3` does not bound the price of anarchy of all
games with affine latencies. -/
example : ¬ ∀ (K P E : Type) [Fintype P] [Finite E] [DecidableEq K] [DecidableEq E]
    (G : NonatomicCongestionGame K P E) (f g : P → ℝ), (∀ e, G.latency e ∈ polynomialLatencies 1) →
      G.IsWardrop f → G.IsFeasible g → G.cost f ≤ 13 / 10 * G.cost g := by
  rw [← pigouBound_le_ofReal_iff (fun _ hc _ hx => nonneg_of_mem_polynomialLatencies hc hx)
    (fun _ hc => monotoneOn_of_mem_polynomialLatencies hc) const_mem_polynomialLatencies_one,
    pigouBound_polynomialLatencies_one, ENNReal.ofReal_le_ofReal_iff (by norm_num)]
  norm_num

end ComplexityTests.GameTheory.PigouBound
