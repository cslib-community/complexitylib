/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.MatrixMultiplication.Schonhage.BoxTradeoffParameters
import Complexity.Algorithms.MatrixMultiplication.Schonhage.BandBounds
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Rational saving for the actual shared encoding count

At `m=9k`, `L=189k`, the size premise `D^18 ≤ N` makes a band fit the original
outer dimension and bounds the total shared encoding length by
`4*N²*(9/20)^k`. Geometry construction happens once and can use this same bound.

This is an original algebraic specialization of the encoding calculation in
[AlmanWilliams2026, proof of Corollary 26]. It replaces the source's entropy-style
binomial lower bound and analytic estimates by `21^m ≤ binom(21m,m) ≤ 64^m`
and one integer base comparison. It proves finite counts, with no source machine,
execution or assumed running time, and does not assert the final 3SUM exponent.

## Main results

* `BoxTradeoff.bandSize_twentyone_le`: the original size bound admits each band.
* `BoxTradeoff.encodings_ninth_blocks`: shared encoding count with a rational saving.
* `BoxTradeoff.nativeShape_ninth_blocks`: the complete finite native-ledger shape.
* `BoxTradeoff.decay_sixteenth`: an integer-power saving relative to the inner dimension.
-/

public section

namespace Cslib.Algorithms.MatrixMultiplication.Schonhage.BoxTradeoff

open Finset

private theorem twentyone_pow_le_choose (m : ℕ) : 21 ^ m ≤ (21 * m).choose m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hterm : (21 * m).choose m * 21 ≤ (21 * m + 21).choose (m + 1) := by
      have h := Finset.single_le_sum (f := fun p : ℕ × ℕ =>
        (21 * m).choose p.1 * Nat.choose 21 p.2)
        (fun _ _ => Nat.zero_le _) (show (m, 1) ∈ Finset.antidiagonal (m + 1) by simp)
      rw [← Nat.add_choose_eq] at h
      simpa using h
    calc 21 ^ (m + 1) = 21 ^ m * 21 := pow_succ _ _
      _ ≤ (21 * m).choose m * 21 := Nat.mul_le_mul_right _ ih
      _ ≤ (21 * (m + 1)).choose (m + 1) := by
        simpa only [Nat.mul_add, Nat.mul_one] using hterm

private theorem choose_twentyone_mul_le (m : ℕ) : (21 * m).choose m ≤ 64 ^ m := by
  have hterm : (21 * m).choose m * 20 ^ (20 * m) ≤ 21 ^ (21 * m) := by
    have h := Finset.single_le_sum
      (f := fun i : ℕ => (1 : ℕ) ^ i * 20 ^ (21 * m - i) * (21 * m).choose i)
      (fun _ _ => Nat.zero_le _) (show m ∈ range (21 * m + 1) by simp; omega)
    have hp := add_pow (1 : ℕ) 20 (21 * m)
    simp only [Nat.cast_id] at hp
    rw [← hp] at h
    rw [show 21 * m - m = 20 * m by omega] at h
    simpa only [one_pow, one_mul, show (1 : ℕ) + 20 = 21 by decide, Nat.mul_comm] using h
  have hbase : 21 ^ 21 ≤ 64 * 20 ^ 20 := by norm_num
  have hpow := Nat.pow_le_pow_left hbase m
  have hbig : 21 ^ (21 * m) ≤ 64 ^ m * 20 ^ (20 * m) := by
    simpa only [pow_mul, mul_pow] using hpow
  exact Nat.le_of_mul_le_mul_right (hterm.trans hbig) (Nat.pow_pos (by decide))

/-- A band at the improved depth `L=21m` fits under the source's original size condition.
The proof uses only integer binomial and power bounds. -/
theorem bandSize_twentyone_le (m : ℕ) :
    K0 (21 * m) m * N0 (21 * m) m ≤ D m ^ 18 := by
  have hK : K0 (21 * m) m ≤ 8 ^ m := by
    have hs := (K0_sq_le_K (21 * m) m).trans (choose_twentyone_mul_le m)
    change K0 (21 * m) m ^ 2 ≤ 64 ^ m at hs
    have heq : 64 ^ m = (8 ^ m) ^ 2 := by rw [← pow_mul, Nat.mul_comm, pow_mul]; norm_num
    rw [heq] at hs
    exact (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp hs
  calc K0 (21 * m) m * N0 (21 * m) m
      ≤ 8 ^ m * N0 (21 * m) m := Nat.mul_le_mul_right _ hK
    _ = (8 * 3 ^ 20) ^ m := by
      rw [N0, show 21 * m - m = 20 * m by omega, pow_mul, mul_pow]
    _ ≤ (4 ^ 18) ^ m := Nat.pow_le_pow_left (by norm_num) _
    _ = D m ^ 18 := by rw [D, ← pow_mul, ← pow_mul, Nat.mul_comm]

/-- The source size premise automatically discharges the finite retained-box band's
admission hypothesis for the block parameters. -/
theorem boxes_ninth_blocks_of_size (k N : ℕ) (hN : D (9 * k) ^ 18 ≤ N) :
    ((tiles (189 * k) (9 * k) N).card : ℝ) *
        ((boxes (189 * k) (9 * k) k).card : ℝ) ≤
      32 * ((9 * k : ℕ) + 1 : ℝ) * (9 / 20 : ℝ) ^ k * (N : ℝ) ^ 2 := by
  apply boxes_ninth_blocks
  have h := (bandSize_twentyone_le (9 * k)).trans hN
  simpa only [show 21 * (9 * k) = 189 * k by omega] using h

/-- All shared band encodings together retain the same finite saving as the boxes and
queries. The size premise is on the original dimensions; no encoding-cost law is supplied. -/
theorem encodings_ninth_blocks (k N : ℕ) (hN : D (9 * k) ^ 18 ≤ N) :
    (numBands (189 * k) (9 * k) N : ℝ) * (10 : ℝ) ^ (189 * k) ≤
      4 * (N : ℝ) ^ 2 * (9 / 20 : ℝ) ^ k := by
  let B := numBands (189 * k) (9 * k) N
  let K0' := K0 (189 * k) (9 * k)
  let N0' := N0 (189 * k) (9 * k)
  have heq : 189 * k = 21 * (9 * k) := by omega
  have hband : K0' * N0' ≤ N := by
    dsimp only [K0', N0']
    simpa only [← heq] using (bandSize_twentyone_le (9 * k)).trans hN
  have hpad : (B : ℝ) * ((K0' : ℝ) * (N0' : ℝ)) ≤ 2 * (N : ℝ) := by
    have h := padN_le_two_mul (189 * k) (9 * k) N hband
    change B * (K0' * N0') ≤ 2 * N at h
    exact_mod_cast h
  have hK : (21 : ℝ) ^ (9 * k) ≤ 4 * (K0' : ℝ) ^ 2 := by
    have h := (twentyone_pow_le_choose (9 * k)).trans (K_le_four_mul_K0_sq (21 * (9 * k)) (9 * k))
    simpa only [K0', heq] using (show (21 : ℝ) ^ (9 * k) ≤
      4 * (K0 (21 * (9 * k)) (9 * k) : ℝ) ^ 2 by exact_mod_cast h)
  have hcount : (B : ℝ) ^ 2 * (21 : ℝ) ^ (9 * k) * (N0' : ℝ) ^ 2 ≤
      16 * (N : ℝ) ^ 2 := by
    calc (B : ℝ) ^ 2 * (21 : ℝ) ^ (9 * k) * (N0' : ℝ) ^ 2
        ≤ (B : ℝ) ^ 2 * (4 * (K0' : ℝ) ^ 2) * (N0' : ℝ) ^ 2 := by gcongr
      _ = 4 * ((B : ℝ) * ((K0' : ℝ) * (N0' : ℝ))) ^ 2 := by ring
      _ ≤ 4 * (2 * (N : ℝ)) ^ 2 := by gcongr
      _ = _ := by ring
  have hbase : (10 : ℝ) ^ 378 ≤
      (21 : ℝ) ^ 9 * (3 : ℝ) ^ 360 * (4 : ℝ) ^ 324 * (9 / 20 : ℝ) ^ 2 := by
    have hn : (10 : ℕ) ^ 378 * 400 ≤ 21 ^ 9 * 3 ^ 360 * 4 ^ 324 * 81 := by
      decide +kernel
    rw [show (9 / 20 : ℝ) ^ 2 = 81 / 400 by norm_num,
      ← mul_div_assoc, le_div_iff₀ (by norm_num)]
    exact_mod_cast hn
  have hpowered : (10 : ℝ) ^ (378 * k) ≤ (21 : ℝ) ^ (9 * k) *
      (3 : ℝ) ^ (360 * k) * (4 : ℝ) ^ (324 * k) * (9 / 20 : ℝ) ^ (2 * k) := by
    simpa only [mul_pow, ← pow_mul] using pow_le_pow_left₀ (by positivity) hbase k
  have hT : ((10 : ℝ) ^ (189 * k)) ^ 2 ≤ (21 : ℝ) ^ (9 * k) *
      (N0' : ℝ) ^ 2 * ((D (9 * k) ^ 18 : ℕ) : ℝ) ^ 2 * ((9 / 20 : ℝ) ^ k) ^ 2 := by
    have eT : ((10 : ℝ) ^ (189 * k)) ^ 2 = (10 : ℝ) ^ (378 * k) := by
      rw [← pow_mul]; congr 1; omega
    have eN0 : (N0' : ℝ) ^ 2 = (3 : ℝ) ^ (360 * k) := by
      dsimp only [N0', N0]
      rw [show 189 * k - 9 * k = 180 * k by omega, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul]
      congr 1
      omega
    have eD : ((D (9 * k) ^ 18 : ℕ) : ℝ) ^ 2 = (4 : ℝ) ^ (324 * k) := by
      rw [D, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul, ← pow_mul]
      congr 1
      omega
    rw [eT, eN0, eD, ← pow_mul, show k * 2 = 2 * k by omega]
    exact hpowered
  have hNr : ((D (9 * k) ^ 18 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hsq : ((B : ℝ) * (10 : ℝ) ^ (189 * k)) ^ 2 ≤
      (4 * (N : ℝ) ^ 2 * (9 / 20 : ℝ) ^ k) ^ 2 := by
    calc ((B : ℝ) * (10 : ℝ) ^ (189 * k)) ^ 2
        = (B : ℝ) ^ 2 * ((10 : ℝ) ^ (189 * k)) ^ 2 := mul_pow _ _ _
      _ ≤ (B : ℝ) ^ 2 * ((21 : ℝ) ^ (9 * k) * (N0' : ℝ) ^ 2 *
          ((D (9 * k) ^ 18 : ℕ) : ℝ) ^ 2 * ((9 / 20 : ℝ) ^ k) ^ 2) :=
        mul_le_mul_of_nonneg_left hT (by positivity)
      _ ≤ (B : ℝ) ^ 2 * ((21 : ℝ) ^ (9 * k) * (N0' : ℝ) ^ 2 *
          (N : ℝ) ^ 2 * ((9 / 20 : ℝ) ^ k) ^ 2) := by gcongr
      _ = ((B : ℝ) ^ 2 * (21 : ℝ) ^ (9 * k) * (N0' : ℝ) ^ 2) *
          ((N : ℝ) ^ 2 * ((9 / 20 : ℝ) ^ k) ^ 2) := by ring
      _ ≤ (16 * (N : ℝ) ^ 2) * ((N : ℝ) ^ 2 * ((9 / 20 : ℝ) ^ k) ^ 2) := by gcongr
      _ = _ := by ring
  exact le_of_sq_le_sq hsq (by positivity)

/-- The common finite decay is stronger than a sixteenth-root saving in the original
inner dimension. This integer-power inequality needs no logarithm approximation. -/
theorem decay_sixteenth (k : ℕ) :
    ((9 / 20 : ℝ) ^ k) ^ 16 * (D (9 * k) : ℝ) ≤ 1 := by
  have hbase : (9 / 20 : ℝ) ^ 16 * (4 : ℝ) ^ 9 ≤ 1 := by norm_num
  have h := pow_le_pow_left₀ (by positivity) hbase k
  rw [D, Nat.cast_pow, Nat.cast_ofNat]
  simpa only [mul_pow, ← pow_mul, Nat.mul_comm, one_pow] using h

private theorem matrix_words_ninth_blocks (k N : ℕ) (hN : D (9 * k) ^ 18 ≤ N) :
    (N : ℝ) * (D (9 * k) : ℝ) ≤ (9 / 20 : ℝ) ^ k * (N : ℝ) ^ 2 := by
  have hbase : (4 : ℝ) ^ 9 ≤ (4 : ℝ) ^ 162 * (9 / 20 : ℝ) := by norm_num
  have hpow := pow_le_pow_left₀ (by positivity) hbase k
  have hD : (D (9 * k) : ℝ) ≤ (9 / 20 : ℝ) ^ k * ((D (9 * k) ^ 18 : ℕ) : ℝ) := by
    dsimp only [D]
    push_cast
    rw [← pow_mul, show 9 * k * 18 = 162 * k by omega]
    simpa only [mul_pow, ← pow_mul, mul_comm] using hpow
  have hNr : ((D (9 * k) ^ 18 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  calc (N : ℝ) * (D (9 * k) : ℝ)
      ≤ (N : ℝ) * ((9 / 20 : ℝ) ^ k * ((D (9 * k) ^ 18 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hD (Nat.cast_nonneg _)
    _ ≤ (N : ℝ) * ((9 / 20 : ℝ) ^ k * (N : ℝ)) := by gcongr
    _ = _ := by ring

/-- Every finite term in the native routed-product ledger has a common rational saving.
The natural expression counts original matrix words, routing occurrences, one shared
geometry span, all retained tables and every query term. Coefficients of an actual
instruction ledger can multiply this estimate; no running-time premise is assumed. -/
theorem nativeShape_ninth_blocks (k N Q : ℕ) (hN : D (9 * k) ^ 18 ≤ N)
    (hQ : Q * 2 ^ (9 * k) ≤ N ^ 2) :
    ((1 + N * D (9 * k) + Q + 2 ^ (189 * k) +
      (numBands (189 * k) (9 * k) N + 1) * 10 ^ (189 * k) +
      numBands (189 * k) (9 * k) N ^ 2 * ((boxes (189 * k) (9 * k) k).card + 1) +
      Q * (∑ d ∈ range (k + 1), alpha (9 * k) d) : ℕ) : ℝ) ≤
      80 * ((9 * k : ℕ) + 1 : ℝ) * (9 / 20 : ℝ) ^ k * (N : ℝ) ^ 2 := by
  let B := numBands (189 * k) (9 * k) N
  let C := (boxes (189 * k) (9 * k) k).card
  let gain := (9 / 20 : ℝ) ^ k * (N : ℝ) ^ 2
  have hNpos : 0 < N := (Nat.pow_pos (Nat.pow_pos (by decide))).trans_le hN
  have hB : 1 ≤ B := numBands_pos (by omega) hNpos
  have hC : (1 : ℝ) ≤ C := by exact_mod_cast card_boxes_pos (189 * k) (9 * k) k
  have hND : (N : ℝ) * (D (9 * k) : ℝ) ≤ gain := matrix_words_ninth_blocks k N hN
  have hunit : 1 ≤ gain := by
    have hpos : 0 < N * D (9 * k) := Nat.mul_pos hNpos (Nat.pow_pos (by decide))
    have hone : (1 : ℝ) ≤ (N : ℝ) * (D (9 * k) : ℝ) := by exact_mod_cast hpos
    exact hone.trans hND
  have hqueries : (Q : ℝ) * ∑ d ∈ range (k + 1), (alpha (9 * k) d : ℝ) ≤ gain :=
    queries_ninth_blocks k N Q hQ
  have hprefix : (1 : ℝ) ≤ ∑ d ∈ range (k + 1), (alpha (9 * k) d : ℝ) := by
    have h := Finset.single_le_sum (f := fun d => (alpha (9 * k) d : ℝ))
      (fun _ _ => Nat.cast_nonneg _) (show 0 ∈ range (k + 1) by simp)
    simpa only [alpha, Nat.choose_zero_right, pow_zero, Nat.mul_one, Nat.cast_one] using h
  have hQ' : (Q : ℝ) ≤ gain := by
    have hstep : (Q : ℝ) ≤ (Q : ℝ) *
        ∑ d ∈ range (k + 1), (alpha (9 * k) d : ℝ) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hprefix (Nat.cast_nonneg Q)
    exact hstep.trans hqueries
  have henc : (B : ℝ) * (10 : ℝ) ^ (189 * k) ≤ 4 * gain := by
    simpa only [B, gain, mul_assoc, mul_left_comm, mul_comm] using encodings_ninth_blocks k N hN
  have hspan : (10 : ℝ) ^ (189 * k) ≤ 4 * gain := by
    have hB' : (1 : ℝ) ≤ B := by exact_mod_cast hB
    have hstep : (10 : ℝ) ^ (189 * k) ≤ (B : ℝ) * (10 : ℝ) ^ (189 * k) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hB'
        (show 0 ≤ (10 : ℝ) ^ (189 * k) by positivity)
    exact hstep.trans henc
  have htwo : (2 : ℝ) ^ (189 * k) ≤ 4 * gain :=
    (pow_le_pow_left₀ (by norm_num) (by norm_num : (2 : ℝ) ≤ 10) _).trans hspan
  have htables : (B : ℝ) ^ 2 * (C : ℝ) ≤ 32 * ((9 * k : ℕ) + 1 : ℝ) * gain := by
    simpa only [card_tiles, Nat.cast_pow, gain, mul_assoc] using boxes_ninth_blocks_of_size k N hN
  have htiles : (B : ℝ) ^ 2 ≤ (B : ℝ) ^ 2 * (C : ℝ) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hC (sq_nonneg (B : ℝ))
  have hnonneg : 0 ≤ gain := by dsimp only [gain]; positivity
  have hm : (0 : ℝ) ≤ (9 * k : ℕ) := Nat.cast_nonneg _
  push_cast
  dsimp only [B, C, gain] at *
  push_cast at htables hm
  nlinarith only [hunit, hND, hQ', henc, hspan, htwo, htables, htiles, hqueries,
    mul_nonneg hm hnonneg]

end Cslib.Algorithms.MatrixMultiplication.Schonhage.BoxTradeoff
