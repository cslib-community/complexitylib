/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Algebra/BigOperators/Expect.lean`)

public import Complexity.Init
public import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fintype.BigOperators

/-!
# Products of uniform averages

A product of uniform averages is the uniform average of the products over the whole (dependent)
function space (`Fintype.prod_expect`), the counterpart for `𝔼` of `Fintype.prod_sum`: the
coordinates of a uniformly random function `∀ j, α j` are independent and uniform. Its special
case for a function of a single coordinate is `Finset.expect_pi_eval`
(`Complexity.Foundations.Probability.CoordinateExpectation`).

## Main results

- `Fintype.prod_expect`: `∏ j, 𝔼 a, g j a = 𝔼 y : ∀ j, α j, ∏ j, g j (y j)`.
-/

public section

open Finset
open scoped BigOperators

namespace Fintype

/-- **Independence of the coordinates of a uniform function**: a product of uniform averages is
the uniform average of the products over the dependent function space, the counterpart for `𝔼` of
`Fintype.prod_sum`. -/
theorem prod_expect {κ 𝕜 : Type*} {α : κ → Type*} [Fintype κ] [DecidableEq κ]
    [∀ j, Fintype (α j)] [Semifield 𝕜] [CharZero 𝕜] (g : ∀ j, α j → 𝕜) :
    ∏ j, 𝔼 a, g j a = 𝔼 y : (∀ j, α j), ∏ j, g j (y j) := by
  simp only [Finset.expect_eq_sum_div_card, Finset.card_univ, Fintype.card_pi]
  rw [Finset.prod_div_distrib, ← Fintype.prod_sum g]
  simp

end Fintype
