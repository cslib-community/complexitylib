/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests of Complexity.Foundations.Data.Polynomial.TaperedHermite)

import Complexity.Foundations.Data.Polynomial.TaperedHermite

-- Regression tests intentionally export no declarations.
set_option linter.privateModule false

/-! Tests for the two-adic size of tapered Hermite basis values on the dyadic grid. -/

namespace ComplexityTests.TaperedHermite

open Finset Polynomial

/-! ### Valuations on the grid `[-4, 4)`

The nonzero points `-4, -3, -2, -1, 1, 2, 3` have 2-adic valuations `2, 0, 1, 0, 0, 1, 0`: the
valuation `j ≤ 2` occurs `2 ^ (2 - j)` times. -/

example : ∑ q ∈ (Ico (-(2 : ℤ) ^ 2) (2 ^ 2)).erase 0, (padicValInt 2 q : ℤ) = 4 := by
  rw [sum_Ico_erase_zero_padicValInt_two 2 fun j => (j : ℤ)]
  decide

example : ∑ q ∈ (Ico (-(2 : ℤ) ^ 2) (2 ^ 2)).erase 0, ((padicValInt 2 q : ℤ) - 1) ^ 2 = 5 := by
  rw [sum_Ico_erase_zero_padicValInt_two 2 fun j => ((j : ℤ) - 1) ^ 2]
  decide

/-! ### A tapered basis value

On `[-4, 4)`, give a node of valuation `j` the multiplicity `2 - j` (the taper `h = 1`, `u = 2`).
For the node `t = 1`,
`E_1(0) = (3/4) ^ 2 (2/3) (1/2) ^ 2 (2) (3/2) ^ 2 = 27 / 64`, from the factors
`-q / (1 - q)` at `q = -3, -2, -1, 2, 3` (the node `-4` has multiplicity `0`). So
`v₂ (E_1(0)) = -6`, which the closed form gives as `2 ^ 1 * 1 * (1 - 2) + 2 ^ 0 * 2 * (0 - 2)`. -/

private theorem padicValInt_two_neg_four : padicValInt 2 (-4) = 2 := by
  rw [padicValInt, Int.natAbs_neg, show Int.natAbs 4 = 2 ^ 2 from rfl, padicValNat.prime_pow]

private theorem padicValInt_two_two : padicValInt 2 2 = 1 :=
  padicValInt.self (by norm_num)

private theorem padicValInt_two_neg_two : padicValInt 2 (-2) = 1 := by
  rw [padicValInt, Int.natAbs_neg]
  exact padicValInt_two_two

private theorem padicValInt_two_odd {z : ℤ} (hz : ¬(2 : ℤ) ∣ z) : padicValInt 2 z = 0 :=
  padicValInt.eq_zero_of_not_dvd (p := 2) (by exact_mod_cast hz)

/-- The basis value, computed directly from the product. -/
example : (hermiteBasis ((Ico (-(2 : ℤ) ^ 2) (2 ^ 2)).erase 0) (fun q : ℤ => (q : ℚ))
    (fun q => 2 - padicValInt 2 q) 1).eval 0 = 27 / 64 := by
  rw [eval_hermiteBasis, show ((Ico (-(2 : ℤ) ^ 2) (2 ^ 2)).erase 0).erase 1 =
    {-4, -3, -2, -1, 2, 3} by decide]
  rw [prod_insert (by decide), prod_insert (by decide), prod_insert (by decide),
    prod_insert (by decide), prod_insert (by decide), prod_singleton, padicValInt_two_neg_four,
    padicValInt_two_neg_two, padicValInt_two_two, padicValInt_two_odd (z := -3) (by decide),
    padicValInt_two_odd (z := -1) (by decide), padicValInt_two_odd (z := 3) (by decide)]
  norm_num [Ring.inverse_eq_inv]

example : padicValRat 2 (27 / 64) = -6 := by
  rw [padicValRat.div (by norm_num) (by norm_num), show (27 : ℚ) = ((27 : ℕ) : ℚ) by norm_num,
    show (64 : ℚ) = ((2 ^ 6 : ℕ) : ℚ) by norm_num, padicValRat.of_nat, padicValRat.of_nat,
    padicValNat.eq_zero_of_not_dvd (by decide), padicValNat.prime_pow]
  norm_num

/-- The closed form of (D.10) gives the same valuation. -/
example : padicValRat 2 ((hermiteBasis ((Ico (-(2 : ℤ) ^ 2) (2 ^ 2)).erase 0)
    (fun q : ℤ => (q : ℚ)) (fun q => 2 - padicValInt 2 q) 1).eval 0) = -6 := by
  rw [padicValRat_eval_zero_hermiteBasis_dyadic (fun j => 2 - j) (by decide) one_ne_zero,
    padicValInt.one]
  decide

/-- The bound (D.10) for the taper `h = 1`, `u = 2`: `-6 * 1 * 2 ^ 2 ≤ v₂ (E_1(0)) = -6`. -/
example : -(6 * (1 : ℤ) * 2 ^ 2) ≤
    padicValRat 2 ((hermiteBasis ((Ico (-(2 : ℤ) ^ 2) (2 ^ 2)).erase 0)
      (fun q : ℤ => (q : ℚ)) (fun q => 1 * (2 - padicValInt 2 q)) 1).eval 0) := by
  have := neg_le_padicValRat_eval_zero_hermiteBasis_taper (a := 2) 2 1 (by decide) one_ne_zero
  rwa [padicValInt.one] at this

end ComplexityTests.TaperedHermite
