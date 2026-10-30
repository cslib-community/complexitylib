/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import Complexity.Probability.KWiseIndependent.Polynomial
import Complexity.Probability.PairwiseIndependentHash.Retention
import Mathlib.Algebra.Field.ZMod

/-!
# Retention by polynomial hashing

Polynomial hashing `x ↦ c₀ + c₁ x` over `𝔽₅`, retaining a point when its hash lies in the box
`{0, 1}`: a point is retained at rate `2 / 5`, as a direct count over the `25` seeds confirms;
two distinct points are retained jointly at rate `4 / 25`; and all five points have `2` retained
on average.
-/

namespace ComplexityTests.PairwiseRetention

open Cslib Cslib.Probability Finset
open scoped BigOperators

private instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

private theorem hp :
    IsPairwiseIndependentHash (polynomialHash : (Fin 2 → ZMod 5) → ZMod 5 → ZMod 5) :=
  (isKWiseIndependentHash_polynomialHash 2).isPairwiseIndependentHash le_rfl

-- Each point is retained at rate `2 / 5`.
example (x : ZMod 5) : dens {c : Fin 2 → ZMod 5 | polynomialHash c x ∈ ({0, 1} : Finset _)} =
    2 / 5 := by
  rw [hp.dens_filter_apply_mem, show #({0, 1} : Finset (ZMod 5)) = 2 by decide]
  norm_num [ZMod.card]

-- The same rate, counted directly: `10` of the `25` seeds retain the point `3`.
example : #{c : Fin 2 → ZMod 5 | polynomialHash c 3 ∈ ({0, 1} : Finset _)} = 10 := by decide

-- Two distinct points are both retained at rate `4 / 25`.
example : dens {c : Fin 2 → ZMod 5 |
    polynomialHash c 0 ∈ ({0, 1} : Finset _) ∧ polynomialHash c 1 ∈ ({0, 1} : Finset _)} =
      4 / 25 := by
  rw [hp.dens_filter_apply_mem_and_apply_mem (by decide),
    show #({0, 1} : Finset (ZMod 5)) = 2 by decide]
  norm_num [ZMod.card]

-- Of all five points, `2` are retained on average.
example : 𝔼 c : Fin 2 → ZMod 5,
    (#{x ∈ (univ : Finset (ZMod 5)) | polynomialHash c x ∈ ({0, 1} : Finset _)} : ℚ) = 2 := by
  rw [hp.expect_card_filter_apply_mem, show #({0, 1} : Finset (ZMod 5)) = 2 by decide]
  norm_num [ZMod.card]

end ComplexityTests.PairwiseRetention
