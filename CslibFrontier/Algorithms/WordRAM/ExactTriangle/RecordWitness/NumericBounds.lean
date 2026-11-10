/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.RecordWitness.Width
import CslibFrontier.Foundations.Data.Nat.ClogPow

/-!
# Numerical width and word bounds for candidate recovery

The width threshold and word envelope are logarithmic and polynomial in the original input
size. These numerical facts do not import the initialized record caller; its actual prefix
theorem remains in `RecordWitness.SourceBounds`.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.RecordWitness

open Cslib.WordRAM Cslib.Algorithms.ExactTriangle
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage

/-- Every admitted physical width can be chosen logarithmic in original size. The positive
constant is explicit for each original magnitude exponent; geometry is not weakened. -/
theorem admissionWidth_le_log {n D g p A κ : ℕ} (hn : 1 ≤ n)
    (hD : D ≤ n) (hg : g ≤ n) (hp : p ≤ n) (hA : A ≤ (n + 2) ^ κ) :
    admissionWidth n D g p A ≤ (257 * κ + 5909) * Nat.clog 2 (n + 2) := by
  let b := n + 2
  let E := 2 * κ + 512
  have hb : 2 ≤ b := by dsimp only [b]; omega
  have hb1 : 1 ≤ b := le_trans (by decide : 1 ≤ (2 : ℕ)) hb
  have hP : PreparationInput.wordBound n D g p A ≤ b ^ E := by
    exact (PreparationInput.wordBound_le_pow hn hD hg hp hA).trans
      (Nat.pow_le_pow_right hb1 (by dsimp only [E]; omega))
  have hfour : 2 * (n + n ^ 2 + 3) ≤ b ^ 4 := by
    dsimp only [b]
    nlinarith only [Nat.zero_le (n ^ 4), Nat.zero_le (n ^ 3), Nat.zero_le (n ^ 2),
      Nat.zero_le n]
  have hfour' : 2 * (n + n ^ 2 + 3) ≤ (b ^ 2) ^ 2 := hfour.trans_eq (Nat.pow_mul b 2 2)
  have hM : CallableProduct.windowSize n (n ^ 2) ≤ b ^ E := by
    calc
      _ ≤ (2 * (n + n ^ 2 + 3)) ^ 128 := CallableProduct.windowSize_le n (n ^ 2)
      _ ≤ ((b ^ 2) ^ 2) ^ 128 := Nat.pow_le_pow_left hfour' _
      _ = (b ^ 2) ^ 256 := (Nat.pow_mul (b ^ 2) 2 128).symm
      _ ≤ (b ^ 2) ^ (κ + 256) := Nat.pow_le_pow_right (Nat.pow_pos hb1)
        (Nat.le_add_left 256 κ)
      _ = b ^ E := by
        rw [← Nat.pow_mul]
        exact congrArg (fun j : ℕ => b ^ j)
          (by dsimp only [E]; omega : 2 * (κ + 256) = E)
  have hn2 : n ^ 2 ≤ b ^ E := (Nat.pow_le_pow_left (by dsimp only [b]; omega : n ≤ b) 2).trans
    (Nat.pow_le_pow_right hb1 (by dsimp only [E]; omega))
  have hnE : n ≤ b ^ E := (show n ≤ n ^ 2 by nlinarith only [hn]).trans hn2
  have hprod : n * D ≤ b ^ E := (Nat.mul_le_mul_left n hD).trans
    (by simpa only [pow_two] using hn2)
  have hAE : A ≤ b ^ E := hA.trans
    (Nat.pow_le_pow_right hb1 (by dsimp only [E]; omega))
  have hconst : 4096 ≤ b ^ E := (show 4096 ≤ (2 : ℕ) ^ 12 by decide).trans
    ((Nat.pow_le_pow_left hb 12).trans
      (Nat.pow_le_pow_right hb1 (by dsimp only [E]; omega)))
  have hsum : envelope n D g p A ≤ 576 * b ^ E := by
    unfold envelope
    have hgE := hg.trans hnE
    have hDE := hD.trans hnE
    omega
  have henvelope : envelope n D g p A ≤ b ^ (2 * κ + 522) := by
    calc
      _ ≤ 576 * b ^ E := hsum
      _ ≤ b ^ 10 * b ^ E := Nat.mul_le_mul_right _
        ((show 576 ≤ (2 : ℕ) ^ 10 by decide).trans (Nat.pow_le_pow_left hb 10))
      _ = b ^ (2 * κ + 522) := by
        rw [← Nat.pow_add]
        exact congrArg (fun j : ℕ => b ^ j) (by dsimp only [E]; omega : 10 + E = 2 * κ + 522)
  have hbase := Nat.le_pow_clog (by decide : 1 < (2 : ℕ)) b
  have hlogBound := henvelope.trans (Nat.pow_le_pow_left hbase (2 * κ + 522))
  rw [← Nat.pow_mul] at hlogBound
  have hlog := Nat.clog_le_of_le_pow hlogBound
  change Nat.clog 2 (envelope n D g p A) ≤ Nat.clog 2 b * (2 * κ + 522) at hlog
  have hrecord := RecordProduct.admissionWidth_le_log hn hD hg hp hA
  have hlog' : Nat.clog 2 (envelope n D g p A) ≤ (257 * κ + 5906) * Nat.clog 2 b := by
    nlinarith only [hlog, Nat.zero_le (κ * Nat.clog 2 b)]
  have hmax := max_le hrecord hlog'
  have hpositive : 1 ≤ Nat.clog 2 b := Nat.clog_pos (by decide) (by omega : 1 < b)
  unfold admissionWidth
  dsimp only [b] at hmax hpositive
  nlinarith only [hmax, hpositive]

/-- Original-input prefix word/address envelope, independent of the caller's larger width. -/
@[expose] def wordBound (n D g p A : ℕ) : ℕ := 2 ^ admissionWidth n D g p A

/-- All prefix words and memory support have a fixed polynomial envelope for each κ. -/
theorem wordBound_le_pow {n D g p A κ : ℕ} (hn : 1 ≤ n)
    (hD : D ≤ n) (hg : g ≤ n) (hp : p ≤ n) (hA : A ≤ (n + 2) ^ κ) :
    wordBound n D g p A ≤ (n + 2) ^ (514 * κ + 11818) :=
  (Nat.pow_le_pow_right (by decide) (admissionWidth_le_log hn hD hg hp hA)).trans
    (Nat.two_pow_mul_clog_le_pow (by omega) (by omega))

end Cslib.Algorithms.WordRAM.ExactTriangle.RecordWitness
