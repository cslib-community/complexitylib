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

A product of uniform averages is the uniform average of the products over the whole function
space (`Fintype.prod_expect`), the counterpart for `𝔼` of `Fintype.prod_sum`: the coordinates of a
uniformly random function `κ → α` are independent and uniform.

## Main results

- `Fintype.prod_expect`: `∏ j, 𝔼 a, g j a = 𝔼 y : κ → α, ∏ j, g j (y j)`.
-/

public section

open Finset
open scoped BigOperators

namespace Fintype

/-- **Independence of the coordinates of a uniform function**: a product of uniform averages is
the uniform average of the products over the function space, the counterpart for `𝔼` of
`Fintype.prod_sum`. -/
theorem prod_expect {κ α 𝕜 : Type*} [Fintype κ] [DecidableEq κ] [Fintype α] [Semifield 𝕜]
    [CharZero 𝕜] (g : κ → α → 𝕜) :
    ∏ j, 𝔼 a, g j a = 𝔼 y : κ → α, ∏ j, g j (y j) := by
  simp only [Finset.expect_eq_sum_div_card, Finset.card_univ, Fintype.card_fun]
  rw [Finset.prod_div_distrib, ← Fintype.prod_sum (fun j a => g j a)]
  simp

end Fintype
