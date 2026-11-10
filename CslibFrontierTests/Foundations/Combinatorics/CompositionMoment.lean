/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.CompositionMoment

/-!
# Factorial moments of weak compositions

The weak compositions of `2` into two parts are `(2, 0)`, `(1, 1)` and `(0, 2)`, so the first
parts add up to `3`. The upper comparison bounds this by `3 * (2 / 2) = 3`, which is sharp here.
-/

public section

namespace CslibFrontierTests.CompositionMoment

open Finset

/-- The first parts of the weak compositions of `2` into two parts add up to `3`. -/
theorem sum_first_part :
    ∑ M ∈ (univ : Finset (Fin 2)).finsuppAntidiag 2, ∏ i, (M i).descFactorial (![1, 0] i) = 3 := by
  rw [sum_finsuppAntidiag_prod_descFactorial]
  simp [Fin.prod_univ_two, Fin.sum_univ_two]

example (t : ℕ) (d : Fin 2 → ℕ) :
    ((∑ M ∈ (univ : Finset (Fin 2)).finsuppAntidiag t, ∏ i, (M i).descFactorial (d i) : ℕ) : ℝ) ≤
      (Fintype.card (Fin 2)).multichoose t *
        ∏ i, (((d i).factorial : ℝ) * ((t : ℝ) / Fintype.card (Fin 2)) ^ d i) :=
  sum_finsuppAntidiag_prod_descFactorial_le t d

end CslibFrontierTests.CompositionMoment
