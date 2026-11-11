/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Cslib.Algorithms.Lean.TimeM

/-!
# Dynamic programs over pairs of suffixes

The common skeleton of the Wagner–Fischer edit-distance program
[Wagner and Fischer][WagnerFischer1974] and the longest-common-subsequence program
[CLRS, Section 15.4][CLRS2009]. Both fill a table indexed by pairs of suffixes of two words `x` and
`y`. The entry for two empty suffixes is a constant. An entry with one empty suffix depends on its
neighbour along that border. Every other entry depends on three neighbours: the entry dropping the
first letter of both suffixes, the entry dropping only the first letter of the suffix of `x`, and
the entry dropping only the first letter of the suffix of `y`. (The textbook tables are indexed by
prefixes; indexing by suffixes is the same program run on the reversed words, and it lets the
recursion follow the list structure.)

A `GridDP` records the four rules. `GridDP.value D x y` is the entry for the whole words, computed
row by row: `GridDP.row D y x` lists the entries for `x` against every suffix of `y`, longest
first, and the row for `a :: x` is computed from the row for `x` alone (`GridDP.stepRow`). This is
the usual two-row scheme, in which only the previous row is kept.

## Main definitions

* `Cslib.Algorithms.Lean.EditDistance.GridDP`: the four rules of a table over pairs of suffixes.
* `Cslib.Algorithms.Lean.EditDistance.GridDP.value`: the entry for the whole words.
* `Cslib.Algorithms.Lean.EditDistance.GridDP.valueM`: the same program in `TimeM`, charging one
  unit per table entry.

## Main results

* `Cslib.Algorithms.Lean.EditDistance.GridDP.value_nil_nil`, `value_cons_nil`, `value_nil_cons`,
  `value_cons_cons`: `value` satisfies the four rules.
* `Cslib.Algorithms.Lean.EditDistance.GridDP.ret_valueM`: `valueM` returns `value`.
* `Cslib.Algorithms.Lean.EditDistance.GridDP.time_valueM`: `valueM` costs exactly
  `(|x| + 1) (|y| + 1)`, the number of table entries.

## Cost model

`Cslib.Algorithms.Lean.EditDistance.GridDP.valueM` charges one unit per table entry. An entry is
computed by one application of a rule to at most three neighbouring entries, which sit at the heads
of the current and previous rows, so reading them is a constant-time step. The application of a rule
is counted as one step: for edit distance it is a constant number of cost-function calls, additions
and comparisons, and for the longest common subsequence it is a letter comparison, an addition and a
comparison. `TimeM` does not track space; that only the previous row is kept is a property of the
definition, not a proved bound.

## References

* [R. A. Wagner and M. J. Fischer, *The string-to-string correction problem*][WagnerFischer1974]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009]
-/

public section

namespace Cslib.Algorithms.Lean.EditDistance

/-- The rules of a dynamic program over pairs of suffixes of two words over `α`, with entries in
`β`. The entry for `(a :: x, b :: y)` is `consCons a b d u l`, where `d`, `u` and `l` are the
entries for `(x, y)`, `(x, b :: y)` and `(a :: x, y)`. -/
structure GridDP (α β : Type*) where
  /-- The entry for two empty words. -/
  nilNil : β
  /-- The entry for `(a :: x, [])` from the entry for `(x, [])`. -/
  consNil : α → β → β
  /-- The entry for `([], b :: y)` from the entry for `([], y)`. -/
  nilCons : α → β → β
  /-- The entry for `(a :: x, b :: y)` from the entries for `(x, y)`, `(x, b :: y)` and
  `(a :: x, y)`. -/
  consCons : α → α → β → β → β → β

namespace GridDP

variable {α β : Type*} (D : GridDP α β)

/-- The row of the empty word: the entries for `([], y')`, for every suffix `y'` of `y`, longest
first. -/
@[expose] def nilRow : List α → List β
  | [] => [D.nilNil]
  | b :: y =>
    let r := nilRow y
    D.nilCons b (r.headD D.nilNil) :: r

/-- The row of `a :: x` computed from the row `r` of `x`: the entries for `(a :: x, y')`, for every
suffix `y'` of `y`, longest first. -/
@[expose] def stepRow (a : α) : List α → List β → List β
  | [], r => [D.consNil a (r.headD D.nilNil)]
  | b :: y, r =>
    let s := stepRow a y r.tail
    D.consCons a b (r.tail.headD D.nilNil) (r.headD D.nilNil) (s.headD D.nilNil) :: s

/-- The row of `x`: the entries for `(x, y')`, for every suffix `y'` of `y`, longest first. -/
@[expose] def row (y : List α) : List α → List β
  | [] => D.nilRow y
  | a :: x => D.stepRow a y (row y x)

/-- The entry for the whole words `x` and `y`. -/
@[expose] def value (x y : List α) : β :=
  (D.row y x).headD D.nilNil

theorem tail_nilRow (b : α) (y : List α) : (D.nilRow (b :: y)).tail = D.nilRow y := rfl

theorem tail_stepRow (a b : α) (y : List α) (r : List β) :
    (D.stepRow a (b :: y) r).tail = D.stepRow a y r.tail := rfl

/-- Dropping the head of the row of `x` against `b :: y` gives the row of `x` against `y`. -/
theorem tail_row (b : α) (y : List α) : ∀ x : List α, (D.row (b :: y) x).tail = D.row y x
  | [] => rfl
  | a :: x => by
    rw [row, tail_stepRow, tail_row b y x]
    rfl

@[simp] theorem value_nil_nil : D.value [] [] = D.nilNil := rfl

theorem value_cons_nil (a : α) (x : List α) :
    D.value (a :: x) [] = D.consNil a (D.value x []) := rfl

theorem value_nil_cons (b : α) (y : List α) :
    D.value [] (b :: y) = D.nilCons b (D.value [] y) := rfl

theorem value_cons_cons (a b : α) (x y : List α) :
    D.value (a :: x) (b :: y) =
      D.consCons a b (D.value x y) (D.value x (b :: y)) (D.value (a :: x) y) := by
  simp only [value, row, stepRow, List.headD_cons]
  rw [← tail_row D b y x]

/-! ### Cost -/

open TimeM

/-- `nilRow` in `TimeM`, charging one unit per entry. -/
@[expose] def nilRowM : List α → TimeM ℕ (List β)
  | [] => do ✓ return [D.nilNil]
  | b :: y => do
    let r ← nilRowM y
    ✓ return D.nilCons b (r.headD D.nilNil) :: r

/-- `stepRow` in `TimeM`, charging one unit per entry. -/
@[expose] def stepRowM (a : α) : List α → List β → TimeM ℕ (List β)
  | [], r => do ✓ return [D.consNil a (r.headD D.nilNil)]
  | b :: y, r => do
    let s ← stepRowM a y r.tail
    ✓ return D.consCons a b (r.tail.headD D.nilNil) (r.headD D.nilNil) (s.headD D.nilNil) :: s

/-- `row` in `TimeM`. -/
@[expose] def rowM (y : List α) : List α → TimeM ℕ (List β)
  | [] => D.nilRowM y
  | a :: x => do
    let r ← rowM y x
    D.stepRowM a y r

/-- `value` in `TimeM`. Reading off the head of the last row is not charged. -/
@[expose] def valueM (x y : List α) : TimeM ℕ β := do
  let r ← D.rowM y x
  return r.headD D.nilNil

@[simp] theorem ret_nilRowM : ∀ y : List α, (D.nilRowM y).ret = D.nilRow y
  | [] => rfl
  | b :: y => by
    simp only [nilRowM, ret_bind, ret_pure, ret_nilRowM y]
    rfl

theorem time_nilRowM : ∀ y : List α, (D.nilRowM y).time = y.length + 1
  | [] => rfl
  | b :: y => by
    simp only [nilRowM, time_bind, time_tick, time_pure, time_nilRowM y, List.length_cons]
    omega

@[simp] theorem ret_stepRowM (a : α) :
    ∀ (y : List α) (r : List β), (D.stepRowM a y r).ret = D.stepRow a y r
  | [], _ => rfl
  | b :: y, r => by
    simp only [stepRowM, ret_bind, ret_pure, ret_stepRowM a y r.tail]
    rfl

theorem time_stepRowM (a : α) :
    ∀ (y : List α) (r : List β), (D.stepRowM a y r).time = y.length + 1
  | [], _ => rfl
  | b :: y, r => by
    simp only [stepRowM, time_bind, time_tick, time_pure, time_stepRowM a y r.tail,
      List.length_cons]
    omega

@[simp] theorem ret_rowM (y : List α) : ∀ x : List α, (D.rowM y x).ret = D.row y x
  | [] => ret_nilRowM D y
  | a :: x => by
    simp only [rowM, ret_bind, ret_stepRowM, ret_rowM y x]
    rfl

theorem time_rowM (y : List α) :
    ∀ x : List α, (D.rowM y x).time = (x.length + 1) * (y.length + 1)
  | [] => by rw [rowM, time_nilRowM, List.length_nil, Nat.zero_add, Nat.one_mul]
  | a :: x => by
    rw [rowM, time_bind, time_rowM y x, time_stepRowM, List.length_cons,
      Nat.succ_mul (x.length + 1)]

/-- `valueM` computes `value`. -/
@[simp] theorem ret_valueM (x y : List α) : (D.valueM x y).ret = D.value x y := by
  simp only [valueM, ret_bind, ret_pure, ret_rowM]
  rfl

/-- `valueM` charges one unit per table entry: `(|x| + 1) (|y| + 1)` units. -/
theorem time_valueM (x y : List α) : (D.valueM x y).time = (x.length + 1) * (y.length + 1) := by
  simp only [valueM, time_bind, time_pure, Nat.add_zero, time_rowM]

end GridDP

end Cslib.Algorithms.Lean.EditDistance
