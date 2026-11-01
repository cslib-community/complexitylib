/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Sums of indicators over lists

Indicator sums over `List.range n` reduce to the finite-sum indicator API through
`List.sum_map_range`: the indicator of a single index sums to whether the index is in range
(`List.sum_map_range_ite_eq`). A condition that does not depend on the element comes out of the
sum (`List.sum_map_ite_and`).

## Main results

* `List.sum_map_range_ite_eq`: the indicator of `i₀` sums to `b` over `List.range n` when
  `i₀ < n`, and to `0` otherwise.
* `List.sum_map_ite_and`: a constant conjunct of an indicator comes out of the sum.
-/

public section

namespace List

variable {M : Type*} [AddCommMonoid M]

/-- The indicator of a single index sums over `List.range n` to `b` when the index is below `n`,
and to `0` otherwise. -/
theorem sum_map_range_ite_eq (n i₀ : ℕ) (b : M) :
    ((List.range n).map fun i => if i = i₀ then b else 0).sum = if i₀ < n then b else 0 := by
  rw [List.sum_map_range, ← Finset.sum_range (fun i => if i = i₀ then b else 0),
    Finset.sum_ite_eq']
  simp only [Finset.mem_range]

/-- A conjunct of an indicator that does not depend on the element comes out of the sum. -/
theorem sum_map_ite_and {α : Type*} (l : List α) (P : Prop) [Decidable P] (Q : α → Prop)
    [DecidablePred Q] (b : M) :
    (l.map fun a => if P ∧ Q a then b else 0).sum =
      if P then (l.map fun a => if Q a then b else 0).sum else 0 := by
  by_cases hP : P <;> simp [hP]

end List
