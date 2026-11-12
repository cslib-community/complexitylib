/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Foundations.Data.BitString.Sign.BigOperators
import CslibFrontier.Foundations.Data.Code.BinaryJohnson

/-!
# Tests: the binary Johnson bound

The even-weight words of length four form a binary code of minimum distance two, half the length.
The binary Johnson bound with `ε = 1 / 4` applies, since `2 ≥ (1 / 2 - 1 / 16) 4`: fewer than
eight codewords lie within distance one of any word. The sign correlation of two words is the
length minus twice their distance.
-/

namespace CslibFrontierTests.Code.BinaryJohnson

open Cslib Cslib.BitString Cslib.Code Finset

/-- The even-weight words of length four. -/
private def evenCode : Finset (Fin 4 → Bool) :=
  {![false, false, false, false], ![false, false, true, true], ![false, true, false, true],
    ![false, true, true, false]}

private theorem two_le_hammingDist_evenCode :
    ∀ c ∈ evenCode, ∀ c' ∈ evenCode, c ≠ c' → 2 ≤ hammingDist c c' := by
  decide

/-- **The binary Johnson bound at radius one**: fewer than eight even-weight words lie within
distance one of any word. -/
example (w : Fin 4 → Bool) :
    (#{c ∈ evenCode | (hammingDist c w : ℝ) ≤ (1 / 2 - 1 / 4) * Fintype.card (Fin 4)} : ℝ) *
      (2 * (1 / 4) ^ 2) < 1 := by
  refine card_filter_hammingDist_le_mul_two_mul_sq_lt_one (by norm_num)
    (fun c hc c' hc' hcc' => ?_) w
  have h : (2 : ℝ) ≤ hammingDist c c' := by
    exact_mod_cast two_le_hammingDist_evenCode c hc c' hc' hcc'
  rw [Fintype.card_fin]
  linarith

/-- The sign correlation of two words at distance one in length four is `4 - 2 = 2`. -/
example :
    ∑ x : Fin 4,
      signVal (![true, false, false, false] x) * signVal (![false, false, false, false] x) = 2 := by
  rw [sum_signVal_mul_signVal_eq_card_sub,
    show hammingDist ![true, false, false, false] ![false, false, false, false] = 1 by decide,
    Fintype.card_fin]
  norm_num

end CslibFrontierTests.Code.BinaryJohnson
