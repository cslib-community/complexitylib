/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct.Charges
public import Complexity.Algorithms.MatrixMultiplication.Schonhage.BoxTradeoffExponent
import Mathlib.Tactic.Linarith

/-!
# Complete finite work bound for the actual routed box-product ledger

The actual charge is polynomial in depth times original matrix/input work, shared
encodings, all retained boxes and every sparse query occurrence. At block parameters
`L=189k`, `m=9k`, `t=k`, finite estimates give the improved geometric saving. The bound
includes the final halt; conversion to an end-to-end 3SUM exponent remains separate.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct

open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Original finite work of input/routing, shared encodings, all retained tiles and queries. -/
@[expose] def workShape (L m t N Q : ℕ) : ℕ :=
  1 + N * D m + Q + 2 ^ L + (numBands L m N + 1) * 10 ^ L +
    numBands L m N ^ 2 * ((boxes L m t).card + 1) +
    Q * (∑ d ∈ Finset.range (t + 1), alpha m d)

private theorem frontTime_le (L m N Q : ℕ) :
    frontTime L m N Q + (9 * Q + 3) + (7 * QueriedProduct.inputEnd m N Q + 12) + 1 ≤
      16384 * (L + 1) *
        (1 + N * D m + Q + 2 ^ L + (numBands L m N + 1) * 10 ^ L + numBands L m N ^ 2) := by
  unfold frontTime thresholdTime QueriedProduct.routingTimeBound Wanted.timeBound
    BandPreparation.timeBound QueriedProduct.inputEnd
  nlinarith only [Nat.zero_le L, Nat.zero_le (2 ^ L), Nat.zero_le (10 ^ L),
    Nat.zero_le (L * 10 ^ L), Nat.zero_le (N * D m), Nat.zero_le (L * (N * D m)),
    Nat.zero_le Q, Nat.zero_le (L * Q), Nat.zero_le (L * 2 ^ L),
    Nat.zero_le (numBands L m N * 10 ^ L), Nat.zero_le (L * (numBands L m N * 10 ^ L)),
    Nat.zero_le (numBands L m N ^ 2), Nat.zero_le (L * numBands L m N ^ 2)]

/-- The complete native ledger, including halt, has one shared preparation term and
occurrence-sensitive sparse work. No source running-time law is assumed. -/
theorem timeBound_le {L m N : ℕ} (hm : m ≤ L) (t : ℕ) (qs : List (Fin N × Fin N)) :
    timeBound L m t qs + 1 ≤ 32768 * (L + 1) ^ 2 * workShape L m t N qs.length := by
  let S := workShape L m t N qs.length
  let G := (L + 1) ^ 2
  have hG : 1 ≤ G := by dsimp only [G]; nlinarith only [Nat.zero_le L]
  have hLG : L + 1 ≤ G := by dsimp only [G]; nlinarith only [Nat.zero_le L]
  have hS : 1 ≤ S := by
    apply Nat.succ_le_of_lt
    dsimp only [S, workShape]
    positivity
  have hF : 1 + N * D m + qs.length + 2 ^ L + (numBands L m N + 1) * 10 ^ L +
      numBands L m N ^ 2 ≤ S := by
    have hmul : numBands L m N ^ 2 ≤
        numBands L m N ^ 2 * ((boxes L m t).card + 1) := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left (numBands L m N ^ 2)
        (show 1 ≤ (boxes L m t).card + 1 by omega)
    exact (Nat.add_le_add_left hmul _).trans (Nat.le_add_right _ _)
  have hT : 10 ^ L ≤ S := by
    have hmul : 10 ^ L ≤ (numBands L m N + 1) * 10 ^ L :=
      Nat.le_mul_of_pos_left _ (by omega)
    exact hmul.trans ((Nat.le_add_left _ _).trans
      ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)))
  have hB : numBands L m N ^ 2 * ((boxes L m t).card + 1) ≤ S :=
    (Nat.le_add_left _ _).trans (Nat.le_add_right _ _)
  have hQ : qs.length ≤ S :=
    (Nat.le_add_left _ _).trans ((Nat.le_add_right _ _).trans
      ((Nat.le_add_right _ _).trans ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))))
  have hA : qs.length * (∑ d ∈ Finset.range (t + 1), alpha m d) ≤ S :=
    Nat.le_add_left _ _
  have hf := (frontTime_le L m N qs.length).trans
    (Nat.mul_le_mul (Nat.mul_le_mul_left _ hLG) hF)
  have hg := (BoxTable.geometryTime_le L m t hm).trans
    (Nat.mul_le_mul_left (64 * G) hT)
  have ht : numBands L m N ^ 2 * (328 * (boxes L m t).card + 65) ≤ 328 * G * S := by
    calc _ ≤ 328 * (numBands L m N ^ 2 * ((boxes L m t).card + 1)) := by
              nlinarith only [Nat.zero_le (numBands L m N ^ 2)]
         _ ≤ 328 * S := Nat.mul_le_mul_left _ hB
         _ ≤ 328 * G * S := by nlinarith only [Nat.mul_le_mul_right (328 * S) hG]
  have hqa : qs.length * (batchUnit L m t + 7) ≤ 299 * G * S := by
    have hA' := Nat.mul_le_mul (Nat.mul_le_mul_left 258 hLG) hA
    have hQ' := Nat.mul_le_mul_left 41 hQ
    have hQS := Nat.mul_le_mul_right (41 * S) hG
    unfold batchUnit
    nlinarith only [hA', hQ', hQS]
  have hunit : 1 ≤ G * S := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul hG hS
  unfold timeBound
  rw [sum_tileCharge hm t qs]
  change _ ≤ 32768 * G * S
  simp only [Nat.mul_assoc] at hf hg ht hqa ⊢
  omega

/-- Complete native work, including halt, at the algebraic block parameters. The saving
charges every original occurrence and includes all routing, encodings and shared preparation. -/
theorem thin_timeBound (k N : ℕ) (qs : List (Fin N × Fin N))
    (hN : D (9 * k) ^ 18 ≤ N) (hQ : qs.length * 2 ^ (9 * k) ≤ N ^ 2) :
    ((timeBound (189 * k) (9 * k) k qs + 1 : ℕ) : ℝ) ≤
      2621440 * ((189 * k + 1 : ℕ) : ℝ) ^ 2 * ((9 * k + 1 : ℕ) : ℝ) *
        (9 / 20 : ℝ) ^ k * (N : ℝ) ^ 2 := by
  have hc : ((timeBound (189 * k) (9 * k) k qs + 1 : ℕ) : ℝ) ≤
      32768 * ((189 * k + 1 : ℕ) : ℝ) ^ 2 *
        (workShape (189 * k) (9 * k) k N qs.length : ℝ) := by
    exact_mod_cast timeBound_le (L := 189 * k) (m := 9 * k) (by omega) k qs
  have hs : (workShape (189 * k) (9 * k) k N qs.length : ℝ) ≤
      80 * ((9 * k + 1 : ℕ) : ℝ) * (9 / 20 : ℝ) ^ k * (N : ℝ) ^ 2 := by
    simpa only [workShape, Nat.cast_add, Nat.cast_one] using
      BoxTradeoff.nativeShape_ninth_blocks k N qs.length hN hQ
  have h := hc.trans (mul_le_mul_of_nonneg_left hs (by positivity))
  convert h using 1; ring

/-- The same actual native ledger has finite thin-dimension exponent `8/125 = 0.064`,
with polynomial depth factors explicit. This is not an end-to-end 3SUM time bound. -/
theorem thin_timeBound_rpow (k N : ℕ) (qs : List (Fin N × Fin N))
    (hN : D (9 * k) ^ 18 ≤ N) (hQ : qs.length * 2 ^ (9 * k) ≤ N ^ 2) :
    ((timeBound (189 * k) (9 * k) k qs + 1 : ℕ) : ℝ) ≤
      2621440 * ((189 * k + 1 : ℕ) : ℝ) ^ 2 * ((9 * k + 1 : ℕ) : ℝ) *
        (D (9 * k) : ℝ) ^ (-(8 / 125 : ℝ)) * (N : ℝ) ^ 2 := by
  have hd := mul_le_mul_of_nonneg_left (BoxTradeoff.decay_le_rpow k)
    (show (0 : ℝ) ≤ 2621440 * ((189 * k + 1 : ℕ) : ℝ) ^ 2 *
      ((9 * k + 1 : ℕ) : ℝ) by positivity)
  exact (thin_timeBound k N qs hN hQ).trans (mul_le_mul_of_nonneg_right hd (by positivity))

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct
