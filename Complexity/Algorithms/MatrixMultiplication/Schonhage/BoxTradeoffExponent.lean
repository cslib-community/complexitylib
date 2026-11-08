/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.MatrixMultiplication.Schonhage.BoxTradeoffEncoding
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum

/-!
# An exact rational certificate for exponent 0.064

The integer inequality `9^125*4^72 ≤ 20^125` implies
`(9/20)^k ≤ (4^(9k))^(-8/125)`. Applied to the checked finite ledger shape, this
converts its rational decay to an inner-dimension power saving of `0.064`.

This is an original algebraic block-parameter proof of a quantitative step used in
[AlmanWilliams2026, proof of Corollary 26]. It uses no logarithm approximation or
source running-time law. Polynomial factors in the depth remain explicit; their
asymptotic absorption and the final ordinary-3SUM exponent are separate obligations.

## Main results

* `BoxTradeoff.decay_le_rpow`: rational decay bounded by an exact real power.
* `BoxTradeoff.nativeShape_ninth_blocks_rpow`: the complete finite shape with that power saving.
-/

public section

namespace Cslib.Algorithms.MatrixMultiplication.Schonhage.BoxTradeoff

open Finset

/-- The common rational decay gives a `D^(-0.064)` saving at the block parameters.
The numerical comparison is certified by exact natural-number computation. -/
theorem decay_le_rpow (k : ℕ) :
    (9 / 20 : ℝ) ^ k ≤ (D (9 * k) : ℝ) ^ (-(8 / 125 : ℝ)) := by
  have hD : (0 : ℝ) < D (9 * k) := by exact_mod_cast Nat.pow_pos (by decide : 0 < 4)
  have hbase : (9 / 20 : ℝ) ^ 125 * (4 : ℝ) ^ 72 ≤ 1 := by
    have hn : (9 : ℕ) ^ 125 * 4 ^ 72 ≤ 20 ^ 125 := by decide +kernel
    rw [div_pow, div_mul_eq_mul_div, div_le_one (by positivity)]
    exact_mod_cast hn
  have hprod : ((9 / 20 : ℝ) ^ k) ^ 125 * (D (9 * k) : ℝ) ^ 8 ≤ 1 := by
    have h := pow_le_pow_left₀ (by positivity) hbase k
    rw [D, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul, ← pow_mul,
      show 9 * k * 8 = 72 * k by omega, show k * 125 = 125 * k by omega]
    simpa only [mul_pow, ← pow_mul, one_pow] using h
  have hright : ((D (9 * k) : ℝ) ^ (-(8 / 125 : ℝ))) ^ 125 =
      ((D (9 * k) : ℝ) ^ 8)⁻¹ := by
    rw [← Real.rpow_mul_natCast hD.le,
      show (-(8 / 125 : ℝ)) * ((125 : ℕ) : ℝ) = -(8 : ℝ) by norm_num,
      Real.rpow_neg hD.le]
    norm_num
  apply le_of_pow_le_pow_left₀ (n := 125) (by decide) (by positivity)
  rw [hright, inv_eq_one_div, le_div_iff₀ (pow_pos hD 8)]
  exact hprod

/-- The complete finite native-ledger shape has an exact `D^(-0.064)` saving,
with its depth factor and original dimension/occurrence hypotheses retained. -/
theorem nativeShape_ninth_blocks_rpow (k N Q : ℕ) (hN : D (9 * k) ^ 18 ≤ N)
    (hQ : Q * 2 ^ (9 * k) ≤ N ^ 2) :
    ((1 + N * D (9 * k) + Q + 2 ^ (189 * k) +
      (numBands (189 * k) (9 * k) N + 1) * 10 ^ (189 * k) +
      numBands (189 * k) (9 * k) N ^ 2 * ((boxes (189 * k) (9 * k) k).card + 1) +
      Q * (∑ d ∈ range (k + 1), alpha (9 * k) d) : ℕ) : ℝ) ≤
      80 * ((9 * k : ℕ) + 1 : ℝ) * (D (9 * k) : ℝ) ^ (-(8 / 125 : ℝ)) *
        (N : ℝ) ^ 2 := by
  exact (nativeShape_ninth_blocks k N Q hN hQ).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (decay_le_rpow k) (by positivity)) (sq_nonneg _))

end Cslib.Algorithms.MatrixMultiplication.Schonhage.BoxTradeoff
