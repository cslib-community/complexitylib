/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Int.Interval
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Cardinality of integer counter grids

The number of configurations of an `ι × κ` grid of integer counters bounded in `[-m, m]`.

## Main results

* `Fintype.card_piFinset_Icc`: the number of states of an `ι × κ` grid of integer counters in
  `[-m, m]`.
-/

public section

namespace Fintype

/-- The number of values of an `ι × κ` grid of integer counters in `[-m, m]`. -/
theorem card_piFinset_Icc {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (m : ℕ) :
    (Fintype.piFinset fun _ : ι => Fintype.piFinset fun _ : κ =>
      Finset.Icc (-(m : ℤ)) m).card = (2 * m + 1) ^ (Fintype.card ι * Fintype.card κ) := by
  have : (↑m + 1 - -(m : ℤ)).toNat = 2 * m + 1 := by omega
  simp only [Fintype.card_piFinset, Int.card_Icc, this, Finset.prod_const, Finset.card_univ]
  rw [← pow_mul, mul_comm (Fintype.card κ)]

end Fintype
