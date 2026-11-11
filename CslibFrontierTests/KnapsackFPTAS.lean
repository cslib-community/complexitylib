/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Algorithms.Lean.Knapsack.FPTAS
public import CslibFrontier.Computability.Complexity.Problems.Knapsack.Unary

/-!
# Knapsack dynamic program and FPTAS examples

These kernel-checked examples (using no `native_decide`) exercise:

1. The profit table and the exact dynamic program on a small instance.
2. The FPTAS: with `k = 2` it is optimal on an instance where `k = 3` is not, and its value meets
   the guarantee `(k - 1) * OPT ≤ k * value`; with `k = 0` it returns nothing.
3. The decider of `Knapsack` with the values in unary, accepting and rejecting.
-/

public section

namespace CslibFrontierTests.KnapsackFPTAS

open Cslib.Algorithms.Lean.Knapsack Cslib.Complexity

/-! ### 1. The dynamic program by profit -/

/-- Entry `q` of the profit table is a lightest selection of profit `q`. -/
example : profitTable Prod.fst Prod.snd [(2, 3), (3, 4)] =
    [some [], none, none, some [(2, 3)], some [(3, 4)], none, none, some [(2, 3), (3, 4)]] := by
  decide

example : profitDP Prod.fst Prod.snd 5 [(2, 3), (3, 4), (4, 5), (5, 6)] = [(2, 3), (3, 4)] := by
  decide

/-- The dynamic program beats every feasible selection, here `[(5, 6)]`. -/
example : ([(5, 6)].map Prod.snd).sum ≤
    ((profitDP Prod.fst Prod.snd 5 [(2, 3), (3, 4), (4, 5), (5, 6)]).map Prod.snd).sum :=
  sum_map_le_profitDP (by decide) (by decide)

/-! ### 2. The FPTAS -/

example : fptas 2 ([(1, 6), (1, 6), (2, 11), (3, 100)], 2) = [(1, 6), (1, 6)] := by decide

/-- With `k = 3` the FPTAS is not optimal: it returns value `11` where `12` is feasible. -/
example : fptas 3 ([(1, 6), (1, 6), (2, 11), (3, 100)], 2) = [(2, 11)] := by decide

/-- The guarantee for `k = 3` and the optimal selection `[(1, 6), (1, 6)]`: `2 * 12 ≤ 3 * 11`. -/
example : (3 - 1) * ([(1, 6), (1, 6)].map Prod.snd).sum ≤
    3 * ((fptas 3 ([(1, 6), (1, 6), (2, 11), (3, 100)], 2)).map Prod.snd).sum :=
  sub_one_mul_value_le_fptas 3 (by decide) (by decide)

/-- With accuracy `k = 0` every value rounds to `0` and the FPTAS returns nothing. -/
example : fptas 0 ([(1, 6), (1, 6), (2, 11), (3, 100)], 2) = [] := by decide

/-- The real form of the guarantee with `ε = 1 / 2`. -/
example : (1 - 1 / 2 : ℝ) * (([(1, 6), (1, 6)] : List (ℕ × ℕ)).map Prod.snd).sum ≤
    ((fptas ⌈(1 / 2 : ℝ)⁻¹⌉₊ ([(1, 6), (1, 6), (2, 11), (3, 100)], 2)).map Prod.snd).sum :=
  one_sub_mul_value_le_fptas (by norm_num) (by decide) (by decide)

/-! ### 3. Knapsack with unary values -/

example : Knapsack.unaryDecider ⟨[⟨2, 3⟩, ⟨3, 4⟩, ⟨4, 5⟩, ⟨5, 6⟩], 5, 7⟩ = true := by decide

example : Knapsack.unaryDecider ⟨[⟨2, 3⟩, ⟨3, 4⟩, ⟨4, 5⟩, ⟨5, 6⟩], 5, 8⟩ = false := by decide

/-- The decider certifies membership in `Knapsack`. -/
example : (⟨[⟨2, 3⟩, ⟨3, 4⟩, ⟨4, 5⟩, ⟨5, 6⟩], 5, 7⟩ : KnapsackInstance) ∈ Knapsack :=
  (Knapsack.unaryDecider_eq_true_iff _).1 (by decide)

/-- The decider certifies non-membership in `Knapsack`. -/
example : (⟨[⟨2, 3⟩, ⟨3, 4⟩, ⟨4, 5⟩, ⟨5, 6⟩], 5, 8⟩ : KnapsackInstance) ∉ Knapsack := fun h => by
  have := (Knapsack.unaryDecider_eq_true_iff _).2 h
  revert this
  decide

example : Turing.MultiTapeTM.ComputableInPolyTime
    (fun x : KnapsackInstance =>
      KnapsackInstance.mk (x.items.map fun i => Knapsack.Item.mk i.weight i.value)
        x.capacity x.goal)
    encKnapsackUnary encKnapsackUnary := by
  fun_prop

end CslibFrontierTests.KnapsackFPTAS
