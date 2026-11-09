/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.Randomized
import CslibFrontier.Computability.DecisionTree.Leaves

/-!
# Counting lower bounds for randomized decision trees

A decision tree of depth `q` has at most `2 ^ q` leaves, so it takes at most `2 ^ q` values
(`Cslib.DecisionTree.card_le_two_pow_depth_of_injOn`). A randomized decision tree that recovers a
function `F`, injective on a finite set `S` of inputs, with error at most `ε` on every input of
`S`, therefore satisfies `|S| (1 - ε) ≤ 2 ^ q`
(`Cslib.RandomizedDecisionTree.card_mul_one_sub_le_two_pow_depth`): each tree it can draw is right
on at most `2 ^ q` inputs of `S`, while averaged over the trees it is right on at least
`|S| (1 - ε)` of them. This is the information-theoretic lower bound for search problems with
`|S|` distinct answers.

## Main results

* `Cslib.RandomizedDecisionTree.card_mul_one_sub_le_two_pow_depth`: `|S| (1 - ε) ≤ 2 ^ depth`.
-/

public section

namespace Cslib.RandomizedDecisionTree

open Finset

variable {ι β : Type*}

/-- **Counting lower bound for randomized recovery**: a randomized decision tree that recovers a
function `F`, injective on a finite set `S` of inputs, with error at most `ε` on every input of
`S`, has depth `q` with `|S| (1 - ε) ≤ 2 ^ q`. -/
theorem card_mul_one_sub_le_two_pow_depth (μ : RandomizedDecisionTree ι β)
    {F : (ι → Bool) → β} {S : Finset (ι → Bool)} (hF : Set.InjOn F S) {ε : ℝ}
    (hμ : ∀ x ∈ S, μ.errorProb F x ≤ ε) : (S.card : ℝ) * (1 - ε) ≤ 2 ^ μ.depth := by
  classical
  have hw : ∑ t ∈ μ.weights.support, μ.weights t = 1 := μ.total
  have hsucc : ∀ x, 1 - μ.errorProb F x =
      ∑ t ∈ μ.weights.support, μ.weights t * if t.eval x = F x then 1 else 0 := by
    intro x
    rw [errorProb_eq_sum, Finsupp.sum, sub_eq_iff_eq_add, ← sum_add_distrib]
    refine hw.symm.trans (sum_congr rfl fun t _ => ?_)
    split_ifs <;> ring
  have htree : ∀ t ∈ μ.weights.support,
      (∑ x ∈ S, if t.eval x = F x then (1 : ℝ) else 0) ≤ 2 ^ μ.depth := by
    intro t ht
    rw [← natCast_card_filter]
    have hcard := DecisionTree.card_le_two_pow_depth_of_injOn t
      (S := S.filter fun x => t.eval x = F x) (hF.mono fun x hx => (mem_filter.mp hx).1)
      (fun x hx => (mem_filter.mp hx).2)
    have hpow : 2 ^ t.depth ≤ 2 ^ μ.depth := Nat.pow_le_pow_right two_pos (depth_le_depth ht)
    exact_mod_cast hcard.trans hpow
  calc (S.card : ℝ) * (1 - ε) = ∑ x ∈ S, (1 - ε) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ ∑ x ∈ S, (1 - μ.errorProb F x) := sum_le_sum fun x hx => by linarith [hμ x hx]
    _ = ∑ t ∈ μ.weights.support, μ.weights t * ∑ x ∈ S, if t.eval x = F x then 1 else 0 := by
      simp only [hsucc, mul_sum]
      exact sum_comm
    _ ≤ ∑ t ∈ μ.weights.support, μ.weights t * 2 ^ μ.depth :=
      sum_le_sum fun t ht => mul_le_mul_of_nonneg_left (htree t ht) (μ.weights_nonneg t)
    _ = 2 ^ μ.depth := by rw [← sum_mul, hw, one_mul]

end Cslib.RandomizedDecisionTree
