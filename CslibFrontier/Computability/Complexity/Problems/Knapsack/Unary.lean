/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Knapsack.ProfitDP
public import CslibFrontier.Computability.Complexity.Problems.Knapsack
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
import CslibFrontier.Algorithms.Lean.Knapsack.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Tactic.EncLen

/-!
# Knapsack with unary values is in `P`

`Knapsack` is `NP`-complete with all numbers in binary (`Cslib.Complexity.Knapsack_npComplete`),
but the dynamic program by profit (`Cslib.Algorithms.Lean.Knapsack.profitDP`) decides it in time
polynomial in the number of items and the total value. With the values encoded in unary
(`Cslib.Complexity.Knapsack.encItemUnary`, `Cslib.Complexity.encKnapsackUnary`), and the weights,
capacity and goal still in binary, `Knapsack` is therefore in `P`
(`Cslib.Complexity.Knapsack.unary_mem_P`): `Knapsack` is weakly `NP`-hard, solvable in
pseudo-polynomial time [Garey and Johnson][GareyJohnson1979], [Williamson and Shmoys,
Section 3.1][WilliamsonShmoys2011].

## Main definitions

* `Cslib.Complexity.Knapsack.encItemUnary`: knapsack items with unary values and binary weights.
* `Cslib.Complexity.encKnapsackUnary`: knapsack instances with the values in unary.
* `Cslib.Complexity.Knapsack.unaryDecider`: the decider through the dynamic program by profit.

## Main results

* `Cslib.Complexity.Knapsack.unaryDecider_eq_true_iff`: correctness of the decider.
* `Cslib.Complexity.Knapsack.unary_mem_P`: `Knapsack ∈ P encKnapsackUnary`.

## References

* [M. R. Garey and D. S. Johnson, *Computers and Intractability*][GareyJohnson1979]
* [D. P. Williamson, D. B. Shmoys, *The Design of Approximation Algorithms*][WilliamsonShmoys2011]
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM ComputableInPolyTime Cslib.Algorithms.Lean.Knapsack
open scoped List

namespace Knapsack

/-- Encoding of `Knapsack.Item` with the weight in binary and the value in unary. -/
enc_structure encItemUnary : Item where weight : encNat, value : encUnary

attribute [fun_prop] encItemUnary_weight_polyTime encItemUnary_value_polyTime
  encItemUnary_mk_polyTime

end Knapsack

/-- Encoding of `KnapsackInstance` with the item values in unary and weights, capacity, and goal
in binary. -/
enc_structure encKnapsackUnary : KnapsackInstance where
  items : (encList Knapsack.encItemUnary), capacity : encNat, goal : encNat

attribute [fun_prop] encKnapsackUnary_items_polyTime encKnapsackUnary_capacity_polyTime
  encKnapsackUnary_goal_polyTime encKnapsackUnary_mk_polyTime

namespace Knapsack

/-- The decider for `Knapsack` through the dynamic program by profit: the most valuable selection
within the capacity reaches the goal. -/
@[expose] def unaryDecider (x : KnapsackInstance) : Bool :=
  decide (x.goal ≤ ((profitDP Item.weight Item.value x.capacity x.items).map Item.value).sum)

/-- **Correctness of the dynamic program decider.** -/
theorem unaryDecider_eq_true_iff (x : KnapsackInstance) :
    unaryDecider x = true ↔ x ∈ Knapsack := by
  rw [unaryDecider, decide_eq_true_iff, mem_Knapsack_iff_sublist]
  constructor
  · intro h
    exact ⟨_, profitDP_sublist _ _, sum_map_profitDP_le _ _, h⟩
  · rintro ⟨s, hs, hsw, hsv⟩
    exact hsv.trans (sum_map_le_profitDP hs hsw)

/-- The dynamic program decider is polynomial-time in the instance with the values in unary. -/
@[fun_prop]
theorem computableInPolyTime_unaryDecider :
    ComputableInPolyTime unaryDecider encKnapsackUnary encBool := by
  have hDP : ComputableInPolyTime
      (fun x : KnapsackInstance => profitDP Item.weight Item.value x.capacity x.items)
      encKnapsackUnary (encList encItemUnary) :=
    (computableInPolyTime_profitDP (encItemUnary_weight_polyTime id')
      (encItemUnary_value_polyTime id') fun a => by
        enc_len [encItemUnary_apply]).comp ((encKnapsackUnary_capacity_polyTime id').prod
          (encKnapsackUnary_items_polyTime id'))
  have hval : ComputableInPolyTime Item.value encItemUnary encNat :=
    ComputableInPolyTime.unary_to_binary.comp (encItemUnary_value_polyTime id')
  have hsum : ComputableInPolyTime List.sum (encList encNat) encNat := by fun_prop
  have hv := hsum.comp ((map hval).comp hDP)
  exact binary_le' (encKnapsackUnary_goal_polyTime id') hv

/-- **Knapsack is pseudo-polynomial**: with the values in unary, `Knapsack` is in `P`, decided by
the dynamic program by profit [Williamson and Shmoys, Section 3.1][WilliamsonShmoys2011]. -/
theorem unary_mem_P : Knapsack ∈ P encKnapsackUnary :=
  ⟨unaryDecider, computableInPolyTime_unaryDecider, fun x => (unaryDecider_eq_true_iff x).symm⟩

end Knapsack

end Cslib.Complexity
