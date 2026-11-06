/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.PreparationInput
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Callable.Width

/-!
# Numerical admission and original-size bounds for record products

These width and word envelopes depend on original input bounds and the callable product's
window geometry, without importing a per-record execution or its initialized composition.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.RecordProduct

open Cslib.WordRAM Cslib.Algorithms.ExactTriangle Cslib.Matrix
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage

/-- Original-input physical width covering the actual producer, every dirty producer word
before normalization, and all relocated product addresses. -/
@[expose] def admissionWidth (n D g p A : ℕ) : ℕ :=
  PreparationInput.width n D g p A +
    256 * Nat.clog 2 (2 * PreparationInput.wordBound n D g p A + n + n ^ 2 + 5)

/-- Physical admission is positive, including parameter boundary cases. -/
theorem admissionWidth_pos (n D g p A : ℕ) : 0 < admissionWidth n D g p A := by
  unfold admissionWidth PreparationInput.width
  omega

/-- Actual producer word/address bounds and the computed chunk size discharge the physical
fit numerically; neither a window nor an intermediate arithmetic certificate is an input. -/
theorem physical_fits {W n D g p A b Q : ℕ}
    (hb : b ≤ PreparationInput.wordBound n D g p A) (hQ : Q ≤ n ^ 2)
    (hW : admissionWidth n D g p A ≤ W) :
    Fits W (2 * b + 4 * CallableProduct.windowSize n Q + 1024) := by
  have hw : 256 * Nat.clog 2 (2 * PreparationInput.wordBound n D g p A + n + n ^ 2 + 5) ≤ W :=
    by unfold admissionWidth at hW; omega
  have hfit := CallableProduct.physical_fits hw
  have hM : CallableProduct.windowSize n Q ≤ CallableProduct.windowSize n (n ^ 2) := by
    apply Nat.pow_le_pow_right (by decide)
    exact Nat.mul_le_mul_left 128 (Nat.clog_mono_right 2 (by omega))
  exact hfit.of_le (by omega)

/-- The final threshold is logarithmic in the original outer dimension under the producer's
standard polynomial original-header/weight hypotheses. The constant is positive for every κ. -/
theorem admissionWidth_le_log {n D g p A κ : ℕ} (hn : 1 ≤ n)
    (hD : D ≤ n) (hg : g ≤ n) (hp : p ≤ n) (hA : A ≤ (n + 2) ^ κ) :
    admissionWidth n D g p A ≤ (257 * κ + 5906) * Nat.clog 2 (n + 2) := by
  let b := n + 2
  have hb : 2 ≤ b := by dsimp only [b]; omega
  have hP := PreparationInput.wordBound_le_pow hn hD hg hp hA
  change PreparationInput.wordBound n D g p A ≤ b ^ (κ + 19) at hP
  have hunit : 1 ≤ b ^ (κ + 19) := Nat.one_le_pow _ _ (by omega)
  have hnpow : n ≤ b ^ (κ + 19) := (show n ≤ b by dsimp only [b]; omega).trans
    (Nat.le_self_pow (by omega) b)
  have hn2 : n ^ 2 ≤ b ^ (κ + 19) :=
    (Nat.pow_le_pow_left (by dsimp only [b]; omega : n ≤ b) 2).trans
      (Nat.pow_le_pow_right (by omega : 1 ≤ b) (by omega : 2 ≤ κ + 19))
  have harg : 2 * PreparationInput.wordBound n D g p A + n + n ^ 2 + 5 ≤ b ^ (κ + 23) := by
    have hsum : 2 * PreparationInput.wordBound n D g p A + n + n ^ 2 + 5 ≤
        9 * b ^ (κ + 19) := by omega
    have hc : 9 ≤ b ^ 4 := (show 9 ≤ 2 ^ 4 by decide).trans (Nat.pow_le_pow_left hb 4)
    calc
      _ ≤ 9 * b ^ (κ + 19) := hsum
      _ ≤ b ^ 4 * b ^ (κ + 19) := Nat.mul_le_mul_right _ hc
      _ = b ^ (κ + 23) := by rw [← Nat.pow_add]; congr 1; omega
  have hbase := Nat.le_pow_clog (by decide : 1 < (2 : ℕ)) b
  have hlogBound := harg.trans (Nat.pow_le_pow_left hbase (κ + 23))
  rw [← Nat.pow_mul] at hlogBound
  have hlog := Nat.clog_le_of_le_pow hlogBound
  have hprep := PreparationInput.width_le_log hn hD hg hp hA
  change Nat.clog 2 (2 * PreparationInput.wordBound n D g p A + n + n ^ 2 + 5) ≤
    Nat.clog 2 b * (κ + 23) at hlog
  unfold admissionWidth
  dsimp only [b] at hlog
  nlinarith only [hlog, hprep]

/-- Explicit input-derived bound for all prefix words and the address support, independent
of any larger admitted physical width. This is a reservation, not a bulk initialization. -/
@[expose] def wordBound (n D g p A : ℕ) : ℕ := 2 ^ admissionWidth n D g p A

/-- The prefix bound is polynomial in original size for the usual original scalar/weight
envelopes, with an explicit fixed exponent for each magnitude exponent κ. -/
theorem wordBound_le_pow {n D g p A κ : ℕ} (hn : 1 ≤ n)
    (hD : D ≤ n) (hg : g ≤ n) (hp : p ≤ n) (hA : A ≤ (n + 2) ^ κ) :
    wordBound n D g p A ≤ (n + 2) ^ (514 * κ + 11812) := by
  let b := n + 2
  have hb : 1 < b := by dsimp only [b]; omega
  have hc := Nat.clog_pos (by decide : 1 < (2 : ℕ)) hb
  have hp2 := Nat.pow_pred_clog_lt_self (by decide : 1 < (2 : ℕ)) hb
  have he : Nat.clog 2 b = (Nat.clog 2 b).pred + 1 := (Nat.succ_pred_eq_of_pos hc).symm
  have hbase : 2 ^ Nat.clog 2 b ≤ b ^ 2 := by
    rw [he, pow_succ]
    nlinarith only [hp2, show 2 ≤ b by omega]
  have hw := admissionWidth_le_log hn hD hg hp hA
  have hpow := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hw
  change 2 ^ admissionWidth n D g p A ≤ _
  calc
    _ ≤ 2 ^ ((257 * κ + 5906) * Nat.clog 2 b) := hpow
    _ = (2 ^ Nat.clog 2 b) ^ (257 * κ + 5906) := by rw [← Nat.pow_mul, Nat.mul_comm]
    _ ≤ (b ^ 2) ^ (257 * κ + 5906) := Nat.pow_le_pow_left hbase _
    _ = b ^ (514 * κ + 11812) := by
      rw [← Nat.pow_mul]
      exact congrArg (fun k : ℕ => b ^ k) (by omega : 2 * (257 * κ + 5906) = 514 * κ + 11812)

end Cslib.Algorithms.WordRAM.ExactTriangle.RecordProduct
