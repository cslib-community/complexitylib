/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.List.OfFnPad
public import Mathlib.Data.Fin.VecNotation

/-!
# Products of lists padded by ones

Padding the pair `(2, 3)` by two ones gives the list `[2, 3, 1, 1]`, whose product is `6`.
-/

public section

namespace CslibFrontierTests.OfFnPad

/-- The product of `(2, 3)` padded to length four is `6`. -/
theorem prod_padded :
    (List.ofFn fun i : Fin 4 => if hi : (i : ℕ) < 2 then (![2, 3] : Fin 2 → ℕ) ⟨i, hi⟩ else 1).prod
      = 6 := by
  rw [List.prod_ofFn_dite_lt (by omega)]
  rfl

end CslibFrontierTests.OfFnPad
