/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Algorithms.Lean.Query.Select.Cost

/-!
# Tests for deterministic selection by the median of medians

Concrete runs of `Cslib.Query.select` on short lists (sorted directly), on long lists that go
through the median-of-medians recursion, with duplicates, out-of-range ranks and a dishonest
oracle; order statistics that hold and fail, including ties under a total preorder that is not
antisymmetric; and direct applications of the correctness theorems and of the `37 n` comparison
bound.
-/

namespace ComplexityTests.QuerySelect

open Cslib Cslib.Query

-- This file checks concrete runs with `#guard`.
set_option linter.hashCommand false

/-- The honest comparison oracle on `ℕ`. -/
def leOracle : {ι : Type} → LEQuery ℕ ι → ι :=
  LEQuery.oracleOf fun a b => decide (a ≤ b)

/-- A list of `2000` distinct values in scrambled order. -/
def scrambled : List ℕ := (List.range 2000).map fun i => i * 7919 % 2003

/-! ### Short lists -/

-- `[5, 1, 4, 1, 5, 9, 2, 6]` sorts to `[1, 1, 2, 4, 5, 5, 6, 9]`.
#guard (select 0 [5, 1, 4, 1, 5, 9, 2, 6]).eval leOracle == some 1
#guard (select 1 [5, 1, 4, 1, 5, 9, 2, 6]).eval leOracle == some 1
#guard (select 3 [5, 1, 4, 1, 5, 9, 2, 6]).eval leOracle == some 4
#guard (select 7 [5, 1, 4, 1, 5, 9, 2, 6]).eval leOracle == some 9
-- Ranks at or beyond the length give `none`.
#guard (select 8 [5, 1, 4, 1, 5, 9, 2, 6]).eval leOracle == none
#guard (select 0 ([] : List ℕ)).eval leOracle == none

/-! ### Long lists: the median-of-medians recursion -/

-- `1000 > selectCutoff`, so these runs use the medians, the partition and the recursion.
#guard (select 500 (List.range 1000).reverse).eval leOracle == some 500
#guard (select 0 (List.range 1000).reverse).eval leOracle == some 0
#guard (select 999 (List.range 1000).reverse).eval leOracle == some 999
#guard (select 1000 (List.range 1000).reverse).eval leOracle == none
-- Many duplicates: `0, 1, 2, 0, 1, 2, …`.
#guard (select 1500 ((List.range 3000).map (· % 3))).eval leOracle == some 1
-- The result agrees with merge sort at sample ranks of a scrambled list, including both ends and
-- an out-of-range rank.
#guard [0, 777, 1000, 1999, 2000].all fun k =>
  (select k scrambled).eval leOracle == scrambled.mergeSort[k]?

/-! ### The comparison bound on concrete runs -/

-- The counts stay below `37 n`, and are far from trivial.
#guard (select 500 (List.range 1000).reverse).countQueries leOracle ≤ 37 * 1000
#guard 1000 ≤ (select 500 (List.range 1000).reverse).countQueries leOracle
#guard [0, 777, 1000, 1999].all fun k =>
  (select k scrambled).countQueries leOracle ≤ 37 * 2000

-- Under the dishonest oracle answering `false`, every element lands above the pivot, the size
-- check fails, and `select` returns `none`; the comparison bound still holds.
#guard (select 0 (List.range 1000)).eval (LEQuery.oracleOf fun _ _ => false) == none
#guard (select 0 (List.range 1000)).countQueries (LEQuery.oracleOf fun _ _ => false) ≤ 37 * 1000

/-! ### Order statistics -/

/-- `2` has rank `1` in `[3, 1, 2]`. -/
example : [3, 1, 2].IsOrderStatistic (· ≤ ·) 1 2 := ⟨by decide, by decide, by decide⟩

/-- `3` does not have rank `1` in `[3, 1, 2]`: two elements lie strictly below it. -/
example : ¬ [3, 1, 2].IsOrderStatistic (· ≤ ·) 1 3 := fun h => absurd h.countP_lt_le (by decide)

/-- Pairs compared by their first coordinate: a total preorder that is not antisymmetric. -/
def FstLE (p q : ℕ × ℕ) : Prop := p.1 ≤ q.1

instance : DecidableRel FstLE := fun p q => inferInstanceAs (Decidable (p.1 ≤ q.1))
instance : Std.Total FstLE := ⟨fun p q => le_total p.1 q.1⟩
instance : IsTrans (ℕ × ℕ) FstLE := ⟨fun _ _ _ => le_trans⟩

/-- With ties, both tied elements have rank `0` and rank `1`. -/
example : [(1, 0), (1, 1)].IsOrderStatistic FstLE 0 (1, 1) ∧
    [(1, 0), (1, 1)].IsOrderStatistic FstLE 1 (1, 0) :=
  ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide⟩⟩

/-- The comparison oracle of `FstLE`. -/
def fstOracle : {ι : Type} → LEQuery (ℕ × ℕ) ι → ι :=
  LEQuery.oracleOf fun p q => decide (FstLE p q)

/-- `2000` pairs with only seven distinct first coordinates, in scrambled order. -/
def tiedPairs : List (ℕ × ℕ) := (List.range 2000).map fun i => (i * 7919 % 2003 % 7, i)

-- Through the median-of-medians recursion with heavy ties, the first coordinate of the result
-- agrees with merge sort by first coordinate.
#guard [0, 1000, 1999].all fun k =>
  ((select k tiedPairs).eval fstOracle).map Prod.fst ==
    ((tiedPairs.mergeSort fun p q => decide (FstLE p q))[k]?).map Prod.fst
#guard (select 2000 tiedPairs).eval fstOracle == none

-- Under the tie-breaking preorder, `select` returns one of the tied elements.
#guard (select 1 [(2, 0), (1, 0), (1, 1), (0, 0)]).eval fstOracle ∈
  [some (1, 0), some (1, 1)]

/-! ### The theorems applied -/

/-- Correctness against the non-antisymmetric preorder `FstLE`. -/
example (xs : List (ℕ × ℕ)) (k : ℕ) (hk : k < xs.length) :
    ∃ y, (select k xs).eval fstOracle = some y ∧ xs.IsOrderStatistic FstLE k y :=
  select_isOrderStatistic FstLE fstOracle (fun _ _ => rfl) hk

/-- Correctness in a linear order. -/
example (k : ℕ) (xs : List ℕ) : (select k xs).eval leOracle = xs.mergeSort[k]? :=
  eval_select_eq_getElem?_mergeSort leOracle (fun _ _ => rfl) k xs

/-- The comparison bound at a concrete length, for every oracle. -/
example (k : ℕ) (oracle : {ι : Type} → LEQuery ℕ ι → ι) (xs : List ℕ) (hxs : xs.length ≤ 1000) :
    (select k xs).countQueries oracle ≤ 37000 :=
  select_upperBound k oracle 1000 xs hxs

/-- The median-of-medians counting bound at `n = 1000`: each side has at most `702` elements. -/
example : selectSideBound 1000 = 702 := by decide

end ComplexityTests.QuerySelect
