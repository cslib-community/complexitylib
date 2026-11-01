/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.ThreeSum.ChanHe.ShiftedSizes

/-!
# Dimension and magnitude transfer to the actual convolution host

The native host passes side `sqrt(8*mPar²)+1` to its Exact Triangle callee. Lower bounds
on this actual side transfer original polynomial magnitudes to polynomial magnitudes in
that callee dimension. Upper bounds retain the square-root scale and logarithmic factors.
No output lengths or original inputs are replaced by padded values.

## Main results

* `input_lt_mPar_sq`: the candidate window dominates the original square-root dimension.
* `input_lt_packed_side_sq`: the actual callee side is large enough for magnitude transfer.
* `le_packed_side_of_sq_le`: explicit transport of eventual thresholds.
* `packed_side_le`: explicit square-root times squared-logarithm side bound.
* `packed_side_sq_le`: a linear-times-fourth-logarithm bound on squared side.
* `packed_weight_le`: original polynomial filler remains polynomial in the actual side.

These are original elementary consequences of the existing parameter definitions, for use
by the charged ordinary-host composition. They assert no running-time or execution theorem.
-/

public section

namespace Cslib.Algorithms.ThreeSum.ChanHe

/-- Every magnitude parameter gives a candidate window larger than the input square root. -/
theorem input_lt_mPar_sq (n U : ℕ) : n < mPar n U ^ 2 := by
  have hb : 1 ≤ labelBits U := by unfold labelBits; omega
  have hw : Nat.sqrt n + 1 ≤ wPar n U + 1 := by
    unfold wPar
    nlinarith
  have hm : wPar n U + 1 ≤ mPar n U := by
    unfold mPar
    have h : 1 ≤ 2 * Nat.log 2 (wPar n U + 1) + 4 := by omega
    exact Nat.le_mul_of_pos_right _ (by omega)
  exact (Nat.lt_succ_sqrt' n).trans_le (Nat.pow_le_pow_left (hw.trans hm) 2)

/-- The actual packed side, rather than a padded proxy, controls the original length. -/
theorem input_lt_packed_side_sq (n U : ℕ) :
    n < (Nat.sqrt (8 * mPar n U ^ 2) + 1) ^ 2 := by
  have hm : mPar n U ≤ Nat.sqrt (8 * mPar n U ^ 2) :=
    Nat.le_sqrt'.mpr (by omega)
  exact (input_lt_mPar_sq n U).trans_le (Nat.pow_le_pow_left (by omega) 2)

/-- An outer dimension threshold squared admits the same threshold at the actual callee side. -/
theorem le_packed_side_of_sq_le {N n : ℕ} (h : N ^ 2 ≤ n) (U : ℕ) :
    N ≤ Nat.sqrt (8 * mPar n U ^ 2) + 1 := by
  have ht := input_lt_packed_side_sq n U
  nlinarith

/-- The host's actual Exact Triangle dimension is at most three times the candidate window,
plus one, and hence retains its explicit square-root/logarithmic parameter estimate. -/
theorem packed_side_le (κ n : ℕ) :
    Nat.sqrt (8 * mPar n (2 * (n + 2) ^ κ) ^ 2) + 1 ≤
      3 * ((5 * κ + 16) * (10 * κ + 40)) * (Nat.sqrt (n + 2) + 1) *
        (Nat.log 2 (n + 2) + 1) ^ 2 + 1 := by
  have hs : Nat.sqrt (8 * mPar n (2 * (n + 2) ^ κ) ^ 2) ≤
      3 * mPar n (2 * (n + 2) ^ κ) := by
    have h := Nat.sqrt_le' (8 * mPar n (2 * (n + 2) ^ κ) ^ 2)
    nlinarith
  have hm := mPar_shifted_pow_le n κ
  nlinarith only [hs, Nat.mul_le_mul_left 3 hm]

/-- Squaring the actual side removes the square root while preserving only a fixed fourth
power of the logarithm. This is a bound on dimensions, not on any solver's running time. -/
theorem packed_side_sq_le (κ n : ℕ) :
    (Nat.sqrt (8 * mPar n (2 * (n + 2) ^ κ) ^ 2) + 1) ^ 2 ≤
      4 * (3 * ((5 * κ + 16) * (10 * κ + 40)) + 1) ^ 2 * (n + 2) *
        (Nat.log 2 (n + 2) + 1) ^ 4 := by
  let A := (5 * κ + 16) * (10 * κ + 40)
  let S := Nat.sqrt (n + 2) + 1
  let L := Nat.log 2 (n + 2) + 1
  have hunit : 1 ≤ S * L ^ 2 := by
    have : 0 < S * L ^ 2 := by dsimp only [S, L]; positivity
    omega
  have hs := packed_side_le κ n
  have ht : Nat.sqrt (8 * mPar n (2 * (n + 2) ^ κ) ^ 2) + 1 ≤
      (3 * A + 1) * S * L ^ 2 := by
    change _ ≤ 3 * A * S * L ^ 2 + 1 at hs
    nlinarith only [hs, hunit]
  have hS : S ^ 2 ≤ 4 * (n + 2) := by
    have h := Nat.sqrt_le (n + 2)
    have h' := Nat.sqrt_le_self (n + 2)
    dsimp only [S]
    nlinarith
  calc
    _ ≤ ((3 * A + 1) * S * L ^ 2) ^ 2 := Nat.pow_le_pow_left ht 2
    _ = (3 * A + 1) ^ 2 * S ^ 2 * L ^ 4 := by ring
    _ ≤ (3 * A + 1) ^ 2 * (4 * (n + 2)) * L ^ 4 := by gcongr
    _ = _ := by dsimp only [A, L]; ring

/-- The filler sent by the ordinary host is polynomial in its actual callee dimension,
including lengths zero and one. This bridges the caller's original magnitude convention
without a separate runtime magnitude certificate. -/
theorem packed_weight_le (κ E n : ℕ) :
    2 * (n + 2) ^ E + 1 ≤
      (Nat.sqrt (8 * mPar n (2 * (n + 2) ^ κ) ^ 2) + 3) ^ (2 * E + 2) := by
  let t := Nat.sqrt (8 * mPar n (2 * (n + 2) ^ κ) ^ 2) + 1
  have hn : n < t ^ 2 := input_lt_packed_side_sq n _
  have hb : 2 ≤ t + 2 := by omega
  have hp : n + 2 ≤ (t + 2) ^ 2 := by nlinarith
  have hpow : (n + 2) ^ E ≤ (t + 2) ^ (2 * E) :=
    (Nat.pow_le_pow_left hp E).trans_eq (by rw [← pow_mul])
  have hunit : 1 ≤ (t + 2) ^ (2 * E) := Nat.one_le_pow _ _ (by omega)
  change 2 * (n + 2) ^ E + 1 ≤ (t + 2) ^ (2 * E + 2)
  rw [pow_add]
  have hb2 : 3 ≤ (t + 2) ^ 2 := by nlinarith
  nlinarith only [hpow, hunit, Nat.mul_le_mul_left ((t + 2) ^ (2 * E)) hb2]

end Cslib.Algorithms.ThreeSum.ChanHe
