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

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery
