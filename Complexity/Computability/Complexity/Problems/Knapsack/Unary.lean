/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.Knapsack.ProfitDP
public import Complexity.Computability.Complexity.Problems.Knapsack
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Unary
import Complexity.Algorithms.Lean.Knapsack.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# Knapsack with unary values is in `P`

`Knapsack` is `NP`-complete with all numbers in binary (`Cslib.Complexity.Knapsack_npComplete`),
but the dynamic program by profit (`Cslib.Algorithms.Lean.Knapsack.profitDP`) decides it in time
polynomial in the number of items and the total value. With the values encoded in unary, and the
weights, capacity and goal still in binary, `Knapsack` is therefore in `P`
(`Cslib.Complexity.Knapsack.unary_mem_P`): `Knapsack` is weakly `NP`-hard, solvable in
pseudo-polynomial time [Garey and Johnson][GareyJohnson1979], [Williamson and Shmoys,
Section 3.1][WilliamsonShmoys2011].

## Main definitions

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

/-- Knapsack instances with the values in unary and the weights, capacity and goal in binary. -/
abbrev encKnapsackUnary : List (ℕ × ℕ) × ℕ × ℕ ↪ List Bool :=
  encPair (encList (encPair encNat encUnary)) (encPair encNat encNat)

namespace Knapsack

/-- The decider for `Knapsack` through the dynamic program by profit: the most valuable selection
within the capacity reaches the goal. -/
@[expose] def unaryDecider (x : List (ℕ × ℕ) × ℕ × ℕ) : Bool :=
  decide (x.2.2 ≤ ((profitDP Prod.fst Prod.snd x.2.1 x.1).map Prod.snd).sum)

/-- **Correctness of the dynamic program decider.** -/
theorem unaryDecider_eq_true_iff (x : List (ℕ × ℕ) × ℕ × ℕ) :
    unaryDecider x = true ↔ x ∈ Knapsack := by
  rw [unaryDecider, decide_eq_true_iff, mem_Knapsack_iff_sublist]
  constructor
  · intro h
    exact ⟨_, profitDP_sublist _ _, sum_map_profitDP_le _ _, h⟩
  · rintro ⟨s, hs, hsw, hsv⟩
    exact hsv.trans (sum_map_le_profitDP hs hsw)

/-- The dynamic program decider is polynomial-time in the instance with the values in unary. -/
theorem computableInPolyTime_unaryDecider :
    ComputableInPolyTime unaryDecider encKnapsackUnary encBool := by
  have hDP := computableInPolyTime_profitDP_unary.comp
    ((snd (encList (encPair encNat encUnary)) (encPair encNat encNat)).fst'.prod
      (fst (encList (encPair encNat encUnary)) (encPair encNat encNat)))
  have hval : ComputableInPolyTime (fun a : ℕ × ℕ => a.2) (encPair encNat encUnary) encNat :=
    ComputableInPolyTime.unary_to_binary.comp (snd _ _)
  have hsum : ComputableInPolyTime List.sum (encList encNat) encNat := by fun_prop
  have hv := hsum.comp ((map hval).comp hDP)
  exact binary_le' (snd (encList (encPair encNat encUnary)) (encPair encNat encNat)).snd' hv

/-- **Knapsack is pseudo-polynomial**: with the values in unary, `Knapsack` is in `P`, decided by
the dynamic program by profit [Williamson and Shmoys, Section 3.1][WilliamsonShmoys2011]. -/
theorem unary_mem_P : Knapsack ∈ P encKnapsackUnary :=
  ⟨unaryDecider, computableInPolyTime_unaryDecider, fun x => (unaryDecider_eq_true_iff x).symm⟩

end Knapsack

end Cslib.Complexity
