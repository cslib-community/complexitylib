/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexity.Foundations.Combinatorics.BudgetTuples
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.List.FinRange

public section

open Cslib.BudgetTuples

namespace Cslib.Tests.BudgetTuples

/-! With weights `(1, 2)` and budget `4`, the tuples `(b₀, b₁)` with `b₀ + 2 b₁ < 4`, in
lexicographic order. -/

example : budgetTuples [1, 2] 4 = [[0, 0], [0, 1], [1, 0], [1, 1], [2, 0], [3, 0]] := by
  decide +kernel

/-- The successor walks the list from the zero tuple and stops after the last one. -/
example : budgetNext [1, 2] 4 [0, 0] = some [0, 1] ∧ budgetNext [1, 2] 4 [0, 1] = some [1, 0] ∧
    budgetNext [1, 2] 4 [1, 1] = some [2, 0] ∧ budgetNext [1, 2] 4 [2, 0] = some [3, 0] ∧
    budgetNext [1, 2] 4 [3, 0] = none := by
  decide +kernel

/-- The left scan agrees. -/
example : budgetNextScan [1, 2] 4 [1, 1] = some [2, 0] ∧ budgetNextScan [1, 2] 4 [3, 0] = none := by
  decide +kernel

/-- An empty budget has no tuples, and a positive one has the empty tuple for no coordinates. -/
example : budgetTuples [3] 0 = [] ∧ budgetTuples [] 1 = [[]] := by decide +kernel

/-- The six tuples of weight below `4` for the weights `![1, 2]` on `Fin 2`, counted along the
list. -/
example : ∑ _β ∈ ({β ∈ Fintype.piFinset fun _ => Finset.range 4 |
      ∑ Z, ![1, 2] Z * β Z < 4} : Finset (Fin 2 → ℕ)), 1 = 6 := by
  rw [sum_filter_weight_lt_eq (List.nodup_finRange 2) (List.mem_finRange) (by decide) 4]
  decide +kernel

end Cslib.Tests.BudgetTuples
