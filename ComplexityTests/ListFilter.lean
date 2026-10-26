/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Foundations.Data.List.Filter

-- Equal list values still occupy two distinct positions.
example : ∃ (i j : ℕ) (hi : i < ([[7], [7]] : List (List ℕ)).length)
    (hj : j < ([[7], [7]] : List (List ℕ)).length),
    i ≠ j ∧ 7 ∈ ([[7], [7]] : List (List ℕ))[i] ∧
      7 ∈ ([[7], [7]] : List (List ℕ))[j] :=
  (List.two_le_filter_contains_iff [[7], [7]] 7).1 (by decide)

example : ¬ 2 ≤ (([[7], []] : List (List ℕ)).filter fun r => r.contains 7).length := by
  decide

-- The excluded index need not itself be in bounds.
example : ∃ j, ∃ hj : j < ([[7], [7]] : List (List ℕ)).length,
    j ≠ 100 ∧ 7 ∈ ([[7], [7]] : List (List ℕ))[j] :=
  List.exists_other_index_of_two_le_filter_contains [[7], [7]] 7 100 (by decide)

example : ¬ 2 ≤ (([] : List (List ℕ)).filter fun r => r.contains 7).length := by
  decide
