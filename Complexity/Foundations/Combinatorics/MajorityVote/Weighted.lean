/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Majority votes over independent trials

Repeat a trial `2 r` times independently, where each trial has outcome `ω ∈ Ω` with probability
`q ω` and is *good* with probability at least `2 / 3`. Then at most half of the trials are good with
probability at most `(8 / 9) ^ r` (`Cslib.sum_prod_le_of_card_filter_le`). This is the weighted form
of `Cslib.card_filter_card_filter_le_le`, where `q` is uniform, with the same exponential-moment
proof: weight the bad outcomes by `2`, so that the expected weight of a tuple is at most
`(4 / 3) ^ (2 r)` while a tuple with at most `r` good entries has weight at least `2 ^ r`.

## Main results

* `Cslib.sum_prod_le_of_card_filter_le`: the bound.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 7.4][AroraBarak09]
-/

@[expose] public section

namespace Cslib

open Finset

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- The weight of an outcome in the exponential-moment bound: `1` when good, `2` when bad. -/
private def voteWeight (G : Finset Ω) (a : Ω) : ℝ := if a ∈ G then 1 else 2

omit [Fintype Ω] in
private theorem voteWeight_nonneg (G : Finset Ω) (a : Ω) : 0 ≤ voteWeight G a := by
  unfold voteWeight
  split_ifs <;> norm_num

omit [Fintype Ω] in
/-- A tuple with at most `r` of its `2 r` entries good has weight at least `2 ^ r`. -/
private theorem two_pow_le_prod_voteWeight (G : Finset Ω) {r : ℕ} (ω : Fin (2 * r) → Ω)
    (hω : (univ.filter fun i => ω i ∈ G).card ≤ r) : (2 : ℝ) ^ r ≤ ∏ i, voteWeight G (ω i) := by
  simp only [voteWeight]
  rw [prod_ite, prod_const_one, prod_const, one_mul]
  refine pow_le_pow_right₀ (by norm_num) ?_
  have := card_filter_add_card_filter_not (s := (univ : Finset (Fin (2 * r))))
    (fun i => ω i ∈ G)
  rw [card_univ, Fintype.card_fin] at this
  omega

/-- The expected weight of one trial is at most `4 / 3`. -/
private theorem sum_mul_voteWeight_le (q : Ω → ℝ) (hsum : ∑ ω, q ω = 1) (G : Finset Ω)
    (hG : 2 ≤ 3 * ∑ ω ∈ G, q ω) : ∑ a, q a * voteWeight G a ≤ 4 / 3 := by
  have hsplit : ∑ a, q a * voteWeight G a = 2 - ∑ a ∈ G, q a := by
    simp only [voteWeight, mul_ite, mul_one]
    rw [sum_ite, filter_mem_eq_inter, univ_inter, ← sum_mul, mul_comm]
    have h := sum_filter_add_sum_filter_not (univ : Finset Ω) (fun a => a ∈ G) q
    rw [filter_mem_eq_inter, univ_inter, hsum] at h
    linarith
  linarith

/-- **Majority votes over independent trials.** If each trial is good with probability at least
`2 / 3`, then at most half of `2 r` independent trials are good with probability at most
`(8 / 9) ^ r`. -/
theorem sum_prod_le_of_card_filter_le (q : Ω → ℝ) (hq : ∀ ω, 0 ≤ q ω) (hsum : ∑ ω, q ω = 1)
    (G : Finset Ω) (hG : 2 ≤ 3 * ∑ ω ∈ G, q ω) (r : ℕ) :
    ∑ ω : Fin (2 * r) → Ω with (univ.filter fun i => ω i ∈ G).card ≤ r, ∏ i, q (ω i) ≤
      (8 / 9) ^ r := by
  have hmean₀ : 0 ≤ ∑ a, q a * voteWeight G a :=
    sum_nonneg fun a _ => mul_nonneg (hq a) (voteWeight_nonneg G a)
  have h2r : (0 : ℝ) < 2 ^ r := by positivity
  rw [← mul_le_mul_iff_of_pos_left h2r]
  calc 2 ^ r * ∑ ω : Fin (2 * r) → Ω with (univ.filter fun i => ω i ∈ G).card ≤ r,
        ∏ i, q (ω i)
      ≤ ∑ ω : Fin (2 * r) → Ω with (univ.filter fun i => ω i ∈ G).card ≤ r,
          ∏ i, (q (ω i) * voteWeight G (ω i)) := by
        rw [mul_sum]
        refine sum_le_sum fun ω hω => ?_
        rw [prod_mul_distrib, mul_comm]
        exact mul_le_mul_of_nonneg_left (two_pow_le_prod_voteWeight G ω (mem_filter.mp hω).2)
          (prod_nonneg fun i _ => hq _)
    _ ≤ ∑ ω : Fin (2 * r) → Ω, ∏ i, (q (ω i) * voteWeight G (ω i)) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun ω _ _ =>
          prod_nonneg fun i _ => mul_nonneg (hq _) (voteWeight_nonneg G _)
    _ = (∑ a, q a * voteWeight G a) ^ (2 * r) :=
        (Fintype.sum_pow (fun a => q a * voteWeight G a) (2 * r)).symm
    _ ≤ (4 / 3) ^ (2 * r) := pow_le_pow_left₀ hmean₀ (sum_mul_voteWeight_le q hsum G hG) _
    _ = 2 ^ r * (8 / 9) ^ r := by
        rw [pow_mul, ← mul_pow]
        norm_num

end Cslib
