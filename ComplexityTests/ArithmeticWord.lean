/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

import Complexity.Computability.Circuit.Arithmetic.Word

/-!
# Words

The positive and negative blocks of the word `(2, -1, 1)`, which are complementary. The greedy
word over `{7, -10}` is computed, `7, -10, 7`, and is `10`-unbiased; the greedy word over `{0, 0}`
is `0`-unbiased.
-/

namespace ComplexityTests.ArithmeticWord

open Cslib.Circuits.Arithmetic

/-- The word `(2, -1, 1)`. -/
private def w : Fin 3 → ℤ := ![2, -1, 1]

example : wordPos w = {0, 2} ∧ wordNeg w = {1} := by decide

/-- The complement of the positive blocks `{0, 2}` of `(2, -1, 1)` is the negative block `{1}`. -/
example : (wordPos w)ᶜ = {1} := by
  rw [compl_wordPos]
  decide

/-- `(2, -1, 1)` is `2`-unbiased: its prefix sums are `0, 2, 1, 2`. -/
example : IsUnbiased w 2 := by
  unfold IsUnbiased
  decide

example : greedyWord 7 10 3 0 = 7 ∧ greedyWord 7 10 3 1 = -10 ∧ greedyWord 7 10 3 2 = 7 := by
  decide

/-- The greedy word over `{7, -10}` is `10`-unbiased. -/
example (d : ℕ) : IsUnbiased (greedyWord 7 (10 : ℕ) d) 10 :=
  isUnbiased_greedyWord (by decide) (by decide)

/-- The degenerate alphabet `{0, 0}`. -/
example (d : ℕ) : IsUnbiased (greedyWord 0 (0 : ℕ) d) 0 :=
  isUnbiased_greedyWord le_rfl (by decide)

end ComplexityTests.ArithmeticWord
