/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Algorithms.Lean.Query.Select.MinMax.LowerBound
import Mathlib.Algebra.Order.Floor.Div

/-!
# Tests for the minimum and the minimum and maximum in the comparison model

Concrete runs of `Cslib.Query.findMin` and `Cslib.Query.findMinMax` with their comparison
counts, the values of the bound `⌈3n/2⌉ - 2` for small `n`, the fooling relations on a concrete
order, and the lower bounds applied: to the two algorithms (where they meet the upper bounds) and
to algorithms that make no comparisons (which the bounds rule out as correct).
-/

namespace ComplexityTests.QueryMinMax

open Cslib Cslib.Query

-- This file checks concrete runs with `#guard`.
set_option linter.hashCommand false

/-- The honest comparison oracle on `ℕ`. -/
def leOracle : {ι : Type} → LEQuery ℕ ι → ι :=
  LEQuery.oracleOf fun a b => decide (a ≤ b)

/-- A list of `2000` distinct values in scrambled order. -/
def scrambled : List ℕ := (List.range 2000).map fun i => i * 7919 % 2003

/-! ### Concrete runs -/

#guard (findMin [5, 1, 4, 1, 5, 9, 2, 6]).eval leOracle == some 1
#guard (findMin [7]).eval leOracle == some 7
#guard (findMin ([] : List ℕ)).eval leOracle == none
#guard (findMin scrambled).eval leOracle == scrambled.min?
-- `n - 1` comparisons.
#guard (findMin [5, 1, 4, 1, 5, 9, 2, 6]).countQueries leOracle == 7
#guard (findMin scrambled).countQueries leOracle == 1999

#guard (findMinMax [5, 1, 4, 1, 5, 9, 2, 6]).eval leOracle == some (1, 9)
#guard (findMinMax [3, 1, 2]).eval leOracle == some (1, 3)
#guard (findMinMax [7]).eval leOracle == some (7, 7)
#guard (findMinMax ([] : List ℕ)).eval leOracle == none
#guard (findMinMax scrambled).eval leOracle ==
  scrambled.min?.bind fun m => scrambled.max?.map fun M => (m, M)
-- `⌈3n/2⌉ - 2` comparisons, for even and odd `n`.
#guard (findMinMax [5, 1, 4, 1, 5, 9, 2, 6]).countQueries leOracle == 10
#guard (findMinMax [3, 1, 2]).countQueries leOracle == 3
#guard (findMinMax scrambled).countQueries leOracle == 2998

/-! ### The bound `⌈3n/2⌉ - 2` -/

#guard (List.range 7).map (fun n => (3 * n + 1) / 2 - 2) == [0, 0, 1, 3, 4, 6, 7]

/-- The bound is `⌈3n/2⌉ - 2`. -/
example (n : ℕ) : (3 * n + 1) / 2 - 2 = (3 * n) ⌈/⌉ 2 - 2 := by
  rw [Nat.ceilDiv_eq_add_pred_div]
  omega

/-! ### The fooling relations -/

/-- Moving `2` to the bottom of `≤` puts it below `0`, and keeps `0 ≤ 1`. -/
example : moveToBot (· ≤ ·) 2 2 0 ∧ ¬ moveToBot (· ≤ ·) 2 0 2 ∧ moveToBot (· ≤ ·) 2 0 1 := by
  simp only [moveToBot_iff]
  decide

/-- Moving `0` to the top of `≤` puts it above `2`. -/
example : moveToTop (· ≤ ·) 0 2 0 ∧ ¬ moveToTop (· ≤ ·) 0 0 2 := by
  simp only [moveToTop_iff]
  decide

/-- The comparison `0 ≤ 1`, answered true, finds `1` above and `0` below, and nothing else. -/
example : FoundAbove (· ≤ ·) [(0, 1)] 1 ∧ ¬ FoundAbove (· ≤ ·) [(0, 1)] 0 ∧
    FoundBelow (· ≤ ·) [(0, 1)] 0 ∧ ¬ FoundBelow (· ≤ ·) [(0, 1)] 1 := by
  simp only [foundAbove_iff, foundBelow_iff, List.mem_singleton, Prod.mk.injEq]
  refine ⟨⟨0, 1, by simp⟩, ?_, ⟨0, 1, by simp⟩, ?_⟩ <;>
    rintro ⟨a, b, ⟨rfl, rfl⟩, -, h⟩ <;> simp at h

/-! ### The lower bounds applied -/

/-- `findMin` is a correct algorithm for the minimum. -/
example : IsMinAlg (findMin (α := ℕ)) := findMin_isMinAlg

/-- `findMinMax` is a correct algorithm for the minimum and maximum. -/
example : IsMinMaxAlg (findMinMax (α := ℕ)) := findMinMax_isMinMaxAlg

/-- Every correct algorithm for the minimum makes at least `4` comparisons on five distinct
numbers, against the honest oracle. -/
example {alg : List ℕ → FreeM (LEQuery ℕ) (Option ℕ)} (halg : IsMinAlg alg) :
    4 ≤ (alg [3, 1, 4, 5, 9]).countQueries leOracle :=
  halg.length_sub_one_le_countQueries (· ≤ ·) leOracle (fun _ _ => rfl) (xs := [3, 1, 4, 5, 9])
    (by decide)

/-- Every correct algorithm for the minimum and maximum makes at least `6` comparisons on five
distinct numbers, against some linear order. -/
example {alg : List ℕ → FreeM (LEQuery ℕ) (Option (ℕ × ℕ))} (halg : IsMinMaxAlg alg) :
    ∃ f : ℕ → ℕ → Bool, IsLinearOrder ℕ (fun a b => f a b = true) ∧
      6 ≤ (alg [3, 1, 4, 5, 9]).countQueries (LEQuery.oracleOf f) :=
  halg.exists_le_countQueries (xs := [3, 1, 4, 5, 9]) (by decide)

/-- The lower and upper bounds for the minimum agree. -/
example : LowerBound (findMin (α := ℕ)) List.length (· - 1) ∧
    UpperBound (findMin (α := ℕ)) List.length (· - 1) :=
  ⟨findMin_isMinAlg.lowerBound_infinite, findMin_upperBound⟩

/-- The lower and upper bounds for the minimum and maximum agree. -/
example : LowerBound (findMinMax (α := ℕ)) List.length (fun n => (3 * n + 1) / 2 - 2) ∧
    UpperBound (findMinMax (α := ℕ)) List.length (fun n => (3 * n + 1) / 2 - 2) :=
  ⟨findMinMax_isMinMaxAlg.lowerBound_infinite, findMinMax_upperBound⟩

/-- Returning the head without comparing is not a correct algorithm for the minimum. -/
def headAlg (xs : List ℕ) : FreeM (LEQuery ℕ) (Option ℕ) := pure xs.head?

example : ¬ IsMinAlg headAlg := fun h => by
  have := h.length_sub_one_le_countQueries (· ≤ ·) leOracle (fun _ _ => rfl) (xs := [1, 0])
    (by decide)
  simp [headAlg] at this

/-- Returning the head twice without comparing is not a correct algorithm for the minimum and
maximum. -/
def headPairAlg (xs : List ℕ) : FreeM (LEQuery ℕ) (Option (ℕ × ℕ)) :=
  pure (xs.head?.map fun x => (x, x))

example : ¬ IsMinMaxAlg headPairAlg := fun h => by
  obtain ⟨f, -, hf⟩ := h.exists_le_countQueries (xs := [1, 0]) (by decide)
  simp [headPairAlg] at hf

end ComplexityTests.QueryMinMax
