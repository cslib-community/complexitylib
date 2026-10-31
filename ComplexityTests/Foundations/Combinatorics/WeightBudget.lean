/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexity.Foundations.Combinatorics.WeightBudget

public section

open Finset Real

namespace Cslib.Tests.WeightBudget

/-! ### A concrete budget

Two coordinates of weights `1` and `2` and budget `p = 5`: the tuples with `β₀ + 2 β₁ < 5` are
the five with `β₁ = 0`, the three with `β₁ = 1` and the one with `β₁ = 2`. -/

/-- The weights `1, 2`. -/
def w (i : Fin 2) : ℕ := i.val + 1

/-- The tuples of weight below `5`. -/
def budget : Finset (Fin 2 → ℕ) :=
  {β ∈ Fintype.piFinset fun _ => range 5 | ∑ i, w i * β i < 5}

example : #budget = 9 := by decide

/-- Each weight occurs once, so `m = 1`: the bound is `2 ^ (4 ⌊√5⌋ + 4) = 2 ^ 12`. -/
example : #budget ≤ 2 ^ 12 := by
  have h := card_le_two_pow_of_sum_mul_lt (w := w) (m := 1) (p := 5) (S := budget)
    (fun i => Nat.succ_pos _) (fun j => by
      rw [card_le_one]
      intro a ha b hb
      rw [mem_filter] at ha hb
      exact Fin.ext (by simp only [w] at ha hb; omega))
    (fun β hβ => (mem_filter.1 hβ).2)
  simpa [(Nat.eq_sqrt.2 ⟨by norm_num, by norm_num⟩ : 2 = Nat.sqrt 5).symm] using h

/-- The real form at `θ = 1`. -/
example : (#budget : ℝ) ≤ exp (5 + π ^ 2 / 6) := by
  have h := card_le_exp_of_sum_mul_lt (w := w) (m := 1) (p := 5) (S := budget)
    (fun i => Nat.succ_pos _) (fun j => by
      rw [card_le_one]
      intro a ha b hb
      rw [mem_filter] at ha hb
      exact Fin.ext (by simp only [w] at ha hb; omega))
    (fun β hβ => (mem_filter.1 hβ).2) one_pos
  simpa using h

/-! ### The logarithmic sum -/

example : -log (1 - exp (-(1 * ((1 : ℕ) : ℝ)))) + -log (1 - exp (-(1 * ((2 : ℕ) : ℝ)))) ≤
    π ^ 2 / (6 * 1) := by
  have h := sum_neg_log_one_sub_exp_le one_pos {1, 2} (by decide)
  rwa [sum_pair (by decide)] at h

end Cslib.Tests.WeightBudget
