/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.MatrixMultiplication.Schonhage.PrunedCounts
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Codes

/-!
# A finite trace weight for the native controller's potential

## Main definitions

* `PrunedQuery.traceWeight`: a weight on the already defined finite mathematical call trace.

## Main results

* `PrunedQuery.traceWeight_le`: a bound from contributing leaves and recursion depth.

This weight is a mathematical potential, not an assumed execution-time certificate. A separate
native execution proof must show that actual instructions decrease it sufficiently.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery

open Cslib.Algorithms.MatrixMultiplication.Schonhage
open Finset

/-- Weighting each call by its request count plus one pays for scans and fixed controller work. -/
def traceWeight {n : ℕ} (S : Finset (OutStr n)) : ℕ :=
  4096 * (Pruned.totalSize (fun _ => 0) (fun _ => 0) S +
    (Pruned.calls n (fun _ => 0) (fun _ => 0) S).card)

/-- A timestamp budget for a node with `n` levels remaining. A leaf scans no children;
an internal node scans ten children, each of which may use its own recursive budget. -/
def epochAllowance (n : ℕ) : ℕ := 2 * (10 ^ n - 1)

/-- A leaf needs no new child-set timestamp. -/
@[simp]
theorem epochAllowance_zero : epochAllowance 0 = 0 := rfl

/-- Ten fresh child scans and all ten recursive budgets fit in the parent's allowance. -/
theorem epochAllowance_succ (n : ℕ) :
    10 * (1 + epochAllowance n) ≤ epochAllowance (n + 1) := by
  have hp : 1 ≤ (10 : ℕ) ^ n := Nat.one_le_pow n _ (by decide)
  unfold epochAllowance
  rw [pow_succ]
  omega

/-- Every partial traversal of the ten children fits the same concrete timestamp allowance. -/
theorem mul_epochAllowance_le {n k : ℕ} (hk : k ≤ 10) :
    k * (1 + epochAllowance n) ≤ epochAllowance (n + 1) :=
  (Nat.mul_le_mul_right _ hk).trans (epochAllowance_succ n)

/-- The timestamp budget is bounded by twice the original leaf-array size. -/
theorem epochAllowance_le (n : ℕ) : epochAllowance n ≤ 2 * 10 ^ n := by
  unfold epochAllowance
  omega

/-- The weight of the zero-depth root, including the empty-query boundary. -/
theorem traceWeight_zero (S : Finset (OutStr 0)) : traceWeight S = 4096 * (S.card + 1) := by
  simp [traceWeight, Pruned.totalSize, Pruned.calls, Pruned.run]

/-- The existing leaf/passed-set theorem bounds this potential without a runtime assumption. -/
theorem traceWeight_le {n : ℕ} (S : Finset (OutStr n)) :
    traceWeight S ≤ 4096 * (2 * (n + 1) * (leaves S).card + 1) := by
  have hc := Pruned.card_calls_le_totalSize_add_one (fun _ => 0) (fun _ => 0) S
  have hs := Pruned.totalSize_le (fun _ => 0) (fun _ => 0) S
  unfold traceWeight
  nlinarith

/-- One root's scan budget and the weights of exactly its nonempty children. -/
theorem traceWeight_succ {n : ℕ} (S : Finset (OutStr (n + 1))) :
    traceWeight S = 4096 * (S.card + 1) + ∑ lam,
      if (childSet S lam).Nonempty then traceWeight (childSet S lam) else 0 := by
  unfold traceWeight
  rw [Pruned.totalSize_succ, Pruned.card_calls_succ]
  calc
    _ = 4096 * (S.card + 1) +
        4096 * ((∑ lam, if (childSet S lam).Nonempty then
          Pruned.totalSize (sliceAt (fun _ => 0) lam) (sliceAt (fun _ => 0) lam)
            (childSet S lam) else 0) +
          ∑ lam, if (childSet S lam).Nonempty then
            (Pruned.calls n (sliceAt (fun _ => 0) lam) (sliceAt (fun _ => 0) lam)
              (childSet S lam)).card else 0) := by ring
    _ = 4096 * (S.card + 1) + ∑ lam,
        4096 * ((if (childSet S lam).Nonempty then
          Pruned.totalSize (sliceAt (fun _ => 0) lam) (sliceAt (fun _ => 0) lam)
            (childSet S lam) else 0) +
          if (childSet S lam).Nonempty then
            (Pruned.calls n (sliceAt (fun _ => 0) lam) (sliceAt (fun _ => 0) lam)
              (childSet S lam)).card else 0) := by
        rw [← sum_add_distrib, mul_sum]
    _ = _ := by
      apply congrArg (Nat.add (4096 * (S.card + 1)))
      apply sum_congr rfl
      intro lam _
      split_ifs
      · rw [Pruned.totalSize_irrel _ _ (fun _ => 0) (fun _ => 0),
          Pruned.calls_irrel _ _ (fun _ => 0) (fun _ => 0)]
      · simp

/-- Potential contributed by the child subtrees with numerical labels below `k`. This is a
finite sum of mathematical trace weights, not an assumed execution-time bound. -/
def childWeightPrefix {n : ℕ} (S : Finset (OutStr (n + 1))) (k : ℕ) : ℕ :=
  ∑ i ∈ range k, if hi : i < 10 then
    if (childSet S (Encoding.termDigits ⟨i, hi⟩)).Nonempty then
      traceWeight (childSet S (Encoding.termDigits ⟨i, hi⟩)) else 0
    else 0

/-- No child potential has been spent before the first term. -/
@[simp]
theorem childWeightPrefix_zero {n : ℕ} (S : Finset (OutStr (n + 1))) :
    childWeightPrefix S 0 = 0 := by simp [childWeightPrefix]

/-- Advancing the native term counter adds exactly the next nonempty child's potential. -/
theorem childWeightPrefix_succ {n : ℕ} (S : Finset (OutStr (n + 1))) (k : Fin 10) :
    childWeightPrefix S (k.val + 1) = childWeightPrefix S k.val +
      if (childSet S (Encoding.termDigits k)).Nonempty then
        traceWeight (childSet S (Encoding.termDigits k)) else 0 := by
  simp only [childWeightPrefix, sum_range_succ, dite_eq_left k.isLt]

/-- After all ten terms, the child-prefix potential is exactly the recursive part of the
existing mathematical trace weight, in the program's unchanged numerical term order. -/
theorem traceWeight_succ_prefix {n : ℕ} (S : Finset (OutStr (n + 1))) :
    traceWeight S = 4096 * (S.card + 1) + childWeightPrefix S 10 := by
  rw [traceWeight_succ]
  congr 1

/-- The complete local controller work fits within the root summand of `traceWeight`.
The terms account for entry, ten scan/push/accumulate pairs, return, and all loop controls.
Empty children use less work than the displayed pair. Child recursive work is separate. -/
theorem node_local_cost_le (N : ℕ) :
    (7 * N + 30) + 10 * ((20 * N + 44) + (31 * N + 31)) + 28 ≤
      4096 * (N + 1) := by omega

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery
