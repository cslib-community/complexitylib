/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Computability.Circuit.Boolean.RandomPredictor
import Mathlib.Tactic

/-! Lemma 6.4 of submission 865 on small instances. -/

namespace CslibFrontierTests.CircuitRandomPredictor
open Cslib Cslib.Circuits Cslib.Circuits.Boolean Finset

open scoped Classical in
/-- Lemma 6.4 applies to the predictor `τ_φ` of any formula with auxiliary variables (the maps
of Lemma 6.1): for `m = 2` rows of `n = 6` bits, at most a `(2/3)^{⌊64/8⌋}` fraction of the
functions on `6` bits are predicted by `τ_φ` on half of the matrices. -/
example (φ : Formula signature (2 * 6 + 2 ^ 2)) :
    ((univ.filter fun g : BitString 6 → Bool =>
        2 * (1 / 2) ^ 2 ≤ agreeFraction (predictor (n := 6) φ) g).card : ℝ) / 2 ^ 2 ^ 6 ≤
      (2 / 3) ^ (2 ^ 6 / (2 * 2 ^ 2)) :=
  card_le_agreeFraction_le_two_thirds_pow (predictor (n := 6) φ)

/-- The exponent there is `⌊64/8⌋ = 8`. -/
example : 2 ^ 6 / (2 * 2 ^ 2) = 8 := by norm_num

open scoped Classical in
/-- At `m = 1` the threshold `2^{1-1} = 1` asks `τ` to predict `g` everywhere. For the map that
always predicts `true`, only the constant function qualifies, a fraction `2^{-16}` of the
functions on `4` bits; the lemma's bound `(2/3)^{⌊16/2⌋} = (2/3)^8` is consistent with it. -/
example : ((univ.filter fun g : BitString 4 → Bool =>
      2 * (1 / 2) ^ 1 ≤ agreeFraction (m := 1) (fun _ => some fun _ => true) g).card : ℝ) /
        2 ^ 2 ^ 4 ≤ (2 / 3) ^ (2 ^ 4 / (2 * 1 ^ 2)) :=
  card_le_agreeFraction_le_two_thirds_pow (n := 4)
    (fun _ : Fin 1 → BitString 4 => some fun _ => true)

/-- The moment bound at `k = 1`: the expected agreement of a fixed predictor with a random
function is at most `2^{-m}` (here with the trivial product factor `1 + 0/N`). -/
example (τ : (Fin 3 → BitString 2) → Option (BitString 3)) :
    (∑ g : BitString 2 → Bool, agreeFraction τ g ^ 1) / 2 ^ 2 ^ 2 ≤
      (1 / 2) ^ (1 * 3) * ∏ r ∈ range (1 * 3), (1 + (r : ℝ) / 2 ^ 2) :=
  sum_agreeFraction_pow_le τ 1

end CslibFrontierTests.CircuitRandomPredictor
