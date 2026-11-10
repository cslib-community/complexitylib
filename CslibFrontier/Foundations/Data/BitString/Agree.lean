/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Foundations.Data.BitString
public import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Fintype.BigOperators

/-!
# Words agreeing off a set of positions

The words `ι → Bool` agreeing with a word `x` outside a set `F` of positions are free exactly on
`F`, so there are `2 ^ |F|` of them (`BitString.card_filter_forall_notMem_eq`).

## Main results

* `Cslib.BitString.card_filter_forall_notMem_eq`: the words agreeing with `x` outside `F` number
  `2 ^ |F|`.
-/

@[expose] public section

namespace Cslib.BitString

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The words agreeing with `x` outside `F` number `2 ^ |F|`. -/
theorem card_filter_forall_notMem_eq (F : Finset ι) (x : ι → Bool)
    [DecidablePred fun y : ι → Bool => ∀ i ∉ F, y i = x i] :
    #{y : ι → Bool | ∀ i ∉ F, y i = x i} = 2 ^ #F := by
  have h : ({y : ι → Bool | ∀ i ∉ F, y i = x i} : Finset _) =
      Fintype.piFinset fun i => if i ∈ F then univ else {x i} := by
    ext y
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    refine forall_congr' fun i => ?_
    by_cases hi : i ∈ F <;> simp [hi]
  rw [h, Fintype.card_piFinset]
  simp only [apply_ite card, card_univ, Fintype.card_bool, card_singleton]
  rw [prod_ite, prod_const, prod_const_one, mul_one, filter_mem_eq_inter, univ_inter]

end Cslib.BitString
