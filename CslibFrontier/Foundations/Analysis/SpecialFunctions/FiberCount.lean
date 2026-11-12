/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate (Mathlib, Mathlib/Analysis/SpecialFunctions/Log/Basic.lean)

public import CslibFrontier.Init
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Mean lower bounds from fiber counts

Let `s : X → ℕ` take values at most `G` on a finite type `X`, and suppose each fiber
`{x | s x = j}` has at most `A * B ^ j` elements. Then the mean of `s` is large:
`|X| (log |X| - log A - log (G + 1)) ≤ log B * ∑ x, s x`.

This is the counting form of an entropy argument. If `x` is uniformly random and can be described
by first giving `s x` and then one of at most `A * B ^ (s x)` descriptions, then
`log |X| ≤ log (G + 1) + log A + E[s] log B`. The proof applies Jensen's inequality to the
convex function `t ↦ B ^ (-t)`, via `1 + t ≤ exp t`, and needs no probability theory.

## Main results

* `Real.card_mul_log_sub_le_of_card_fiber_le`: the mean lower bound.
-/

public section

namespace Real

open Finset

/-- **Mean lower bound from fiber counts.** If `s : X → ℕ` is bounded by `G` and each fiber
`{x | s x = j}` with `j ≤ G` has at most `A * B ^ j` elements, then
`|X| (log |X| - log A - log (G + 1)) ≤ log B * ∑ x, s x`. -/
theorem card_mul_log_sub_le_of_card_fiber_le {X : Type*} [Fintype X] (s : X → ℕ) {G : ℕ}
    (hs : ∀ x, s x ≤ G) {A B : ℝ} (hA : 0 < A) (hB : 1 ≤ B)
    (hfiber : ∀ j ≤ G, (#{x : X | s x = j} : ℝ) ≤ A * B ^ j) :
    (Fintype.card X : ℝ) * (log (Fintype.card X) - log A - log (G + 1)) ≤
      log B * ∑ x, (s x : ℝ) := by
  classical
  have hL : 0 ≤ log B := log_nonneg hB
  have hsum0 : 0 ≤ ∑ x, (s x : ℝ) := sum_nonneg fun _ _ => by positivity
  rcases Nat.eq_zero_or_pos (Fintype.card X) with hc | hc
  · rw [hc, Nat.cast_zero, zero_mul]; positivity
  set L := log B with hLdef
  set c : ℝ := (Fintype.card X : ℝ)
  have hcpos : 0 < c := Nat.cast_pos.mpr hc
  set μ : ℝ := (∑ x, (s x : ℝ)) / c
  -- The exponential sum is at most `A (G + 1)`.
  have hupper : ∑ x, exp (-(s x * L)) ≤ A * (G + 1) := by
    rw [← sum_fiberwise_of_maps_to (s := univ) (t := range (G + 1)) (g := s)
      (fun x _ => mem_range.mpr (Nat.lt_succ_of_le (hs x)))]
    calc ∑ j ∈ range (G + 1), ∑ x with s x = j, exp (-(s x * L))
        = ∑ j ∈ range (G + 1), (#{x : X | s x = j} : ℝ) * (B ^ j)⁻¹ := by
          refine sum_congr rfl fun j _ => ?_
          rw [sum_congr rfl fun x hx => by rw [(mem_filter.mp hx).2], sum_const, nsmul_eq_mul,
            exp_neg, exp_nat_mul, hLdef, exp_log (by linarith)]
      _ ≤ ∑ _j ∈ range (G + 1), A := by
          refine sum_le_sum fun j hj => ?_
          have hBj : 0 < B ^ j := by positivity
          calc (#{x : X | s x = j} : ℝ) * (B ^ j)⁻¹ ≤ A * B ^ j * (B ^ j)⁻¹ :=
                mul_le_mul_of_nonneg_right
                  (hfiber j (Nat.lt_succ_iff.mp (mem_range.mp hj))) (by positivity)
            _ = A := by field_simp
      _ = A * (G + 1) := by rw [sum_const, card_range, nsmul_eq_mul]; push_cast; ring
  -- Jensen's inequality for `t ↦ exp (-t L)` by the tangent line at `μ`.
  have hlower : c * exp (-(μ * L)) ≤ ∑ x, exp (-(s x * L)) := by
    have htangent (x : X) :
        exp (-(μ * L)) * (1 - (s x - μ) * L) ≤ exp (-(s x * L)) := by
      have h := add_one_le_exp (-((s x - μ) * L))
      calc exp (-(μ * L)) * (1 - (s x - μ) * L)
          ≤ exp (-(μ * L)) * exp (-((s x - μ) * L)) :=
            mul_le_mul_of_nonneg_left (by linarith) (exp_pos _).le
        _ = exp (-(s x * L)) := by rw [← exp_add]; ring_nf
    have hmean : ∑ x : X, (1 - ((s x : ℝ) - μ) * L) = c := by
      rw [sum_sub_distrib, ← sum_mul, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul,
        mul_one, sum_const, card_univ, nsmul_eq_mul]
      simp only [μ, c]; field_simp; ring
    calc c * exp (-(μ * L)) = exp (-(μ * L)) * ∑ x : X, (1 - ((s x : ℝ) - μ) * L) := by
          rw [hmean, mul_comm]
      _ ≤ ∑ x, exp (-(s x * L)) := by rw [mul_sum]; exact sum_le_sum fun x _ => htangent x
  have hmain := hlower.trans hupper
  have hlog := log_le_log (by positivity) hmain
  rw [log_mul hcpos.ne' (exp_pos _).ne', log_exp, log_mul hA.ne' (by positivity)] at hlog
  have hμc : c * μ = ∑ x, (s x : ℝ) := by simp only [μ]; field_simp
  nlinarith

end Real
