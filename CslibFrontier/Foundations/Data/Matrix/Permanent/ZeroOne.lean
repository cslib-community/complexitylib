/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, next to `LinearAlgebra/Matrix/Permanent`)

public import CslibFrontier.Init
public import Mathlib.LinearAlgebra.Matrix.Permanent

/-!
# The permanent of a 0/1 matrix

The permanent of a matrix `A : Matrix n n ℕ` whose entries are all at most `1` is the number of
permutations `σ` with `A i (σ i) = 1` for every `i`, that is, the number of perfect matchings of
the bipartite graph whose edges are the one-entries of `A`.

## Main results

* `Matrix.permanent_eq_card_filter_of_le_one`: the permanent of a 0/1 matrix counts permutations.
-/

public section

open Finset

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The permanent of a 0/1 matrix counts the permutations along its one-entries. -/
theorem permanent_eq_card_filter_of_le_one {A : Matrix n n ℕ} (hA : ∀ i j, A i j ≤ 1) :
    A.permanent = #{σ : Equiv.Perm n | ∀ i, A i (σ i) = 1} := by
  rw [← permanent_transpose, permanent, card_eq_sum_ones, sum_filter]
  refine sum_congr rfl fun σ _ => ?_
  split_ifs with h
  · exact prod_eq_one fun i _ => h i
  · obtain ⟨i, hi⟩ := not_forall.1 h
    exact prod_eq_zero (mem_univ i) (by have := hA i (σ i); simp only [transpose_apply]; omega)

end Matrix
