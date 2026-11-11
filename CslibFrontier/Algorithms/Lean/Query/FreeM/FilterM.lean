/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Algorithms.Lean.Query.FreeM
public import Mathlib.Algebra.BigOperators.Group.List.Basic
import all Init.Data.List.Control

/-!
# Query cost of `List.filterM` in query programs

Core `List.filterM p xs` runs the test `p x` once for each `x ∈ xs`, from left to right, whatever
the earlier answers. So in a query program its number of queries is the sum of the numbers of
queries of the tests. Core defines `List.filterM` through the accumulator `List.filterAuxM` without
exposing the body, so this module imports `Init.Data.List.Control` with `import all`, as core's
own `Init.Data.List.Monadic` does.

## Main results

* `Cslib.FreeM.countQueries_filterM`: the number of queries of `xs.filterM p` is
  `(xs.map fun x => (p x).countQueries oracle).sum`.
* `Cslib.FreeM.countQueries_filterM_of_eq_one`: with one-query tests it is `xs.length`.
-/

public section

namespace Cslib.FreeM

variable {F : Type → Type*} {α : Type}

private theorem countQueries_filterAuxM (oracle : {ι : Type} → F ι → ι) (p : α → FreeM F Bool)
    (xs acc : List α) :
    (List.filterAuxM p xs acc).countQueries oracle =
      (xs.map fun x => (p x).countQueries oracle).sum := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.filterAuxM, countQueries_bind, ih, List.map_cons, List.sum_cons]

/-- The number of queries of `xs.filterM p` is the total number of queries of the tests. -/
@[simp] theorem countQueries_filterM (oracle : {ι : Type} → F ι → ι) (p : α → FreeM F Bool)
    (xs : List α) :
    (xs.filterM p).countQueries oracle = (xs.map fun x => (p x).countQueries oracle).sum := by
  simp only [List.filterM, countQueries_bind, countQueries_filterAuxM, countQueries_pure,
    add_zero]

/-- With tests making one query each, `xs.filterM p` makes `xs.length` queries. -/
theorem countQueries_filterM_of_eq_one (oracle : {ι : Type} → F ι → ι) {p : α → FreeM F Bool}
    (hp : ∀ x, (p x).countQueries oracle = 1) (xs : List α) :
    (xs.filterM p).countQueries oracle = xs.length := by
  rw [countQueries_filterM]
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [List.map_cons, List.sum_cons, hp, ih, List.length_cons, Nat.add_comm]

end Cslib.FreeM
