/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.RecordProduct.Producer
public import Complexity.Algorithms.WordRAM.ExactTriangle.PreparationInput

/-!
# Input-derived admission and charged adapter overhead

The actual producer supplies a polynomial bound for every pre-adapter word and address.
Its existing `wordBound` determines a sufficient positive logarithmic physical width for the
selected product's computed window. Adaptation is linear in `nD+Q`; this per-record statement
does not sum an ExactTriangle solver or establish its aggregate subcubic bound.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.RecordProduct

open Cslib.WordRAM Cslib.Algorithms.ExactTriangle
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

/-- All real descriptor/log/header/copy/invocation work is linear in original matrices and
occurrences. This includes standalone halt, but not another execution of the producer. -/
theorem timeBound_le {m n : ℕ} (qs : List (Fin n × Fin n)) (hN : D m ^ 18 ≤ n) :
    timeBound (m := m) qs + 1 ≤
      3 * (QueriedProduct.timeBound (show m ≤ 19 * m by omega) qs + 1) +
        4096 * (n * D m + qs.length + 1) := by
  have hn : 1 ≤ n := Nat.pow_pos (Nat.pow_pos (by decide : 0 < (4 : ℕ))) |>.trans_le hN
  have hm : m ≤ D m := by
    have hlog := Nat.log_le_self 2 (4 ^ m)
    rw [log_two_four_pow] at hlog
    change m ≤ 4 ^ m
    omega
  have hND : D m ≤ n * D m := Nat.le_mul_of_pos_left _ hn
  have ht := CallableProduct.timeBound_le (m := m) qs
  unfold timeBound
  omega

/-- The actual callee envelope already dominates a second copy of this linear adaptation.
This comparison reuses its established sparse bounds without a separate polylog oracle. -/
theorem timeBound_le_twice_callable {m n : ℕ} (qs : List (Fin n × Fin n))
    (hN : D m ^ 18 ≤ n) :
    timeBound (m := m) qs + 1 ≤ 2 * (CallableProduct.timeBound (m := m) qs + 3) := by
  have hn : 1 ≤ n := Nat.pow_pos (Nat.pow_pos (by decide : 0 < (4 : ℕ))) |>.trans_le hN
  have hm : m ≤ n * D m := by
    have hlog := Nat.log_le_self 2 (4 ^ m)
    rw [log_two_four_pow] at hlog
    have hmul : D m ≤ n * D m := Nat.le_mul_of_pos_left _ hn
    change 4 ^ m ≤ n * D m at hmul
    omega
  unfold timeBound CallableProduct.timeBound CallableProduct.coreTime QueriedProduct.timeBound
    QueriedProduct.inputEnd
  omega

/-- Distinct-set sparsity retains the actual list-occurrence charge. -/
theorem thin_timeBound {m n : ℕ} (qs : List (Fin n × Fin n)) (hN : D m ^ 18 ≤ n)
    (hQ : qs.toFinset.card * 2 ^ m ≤ n ^ 2) :
    ((timeBound (m := m) qs + 1 : ℕ) : ℝ) ≤
      524288 * ((19 * m + 1 : ℕ) : ℝ) *
        (65 * ((D m : ℝ) ^ (-(1 / 18 : ℝ)) * (n : ℝ) ^ 2) + qs.length) := by
  have ht : ((timeBound (m := m) qs + 1 : ℕ) : ℝ) ≤
      2 * ((CallableProduct.timeBound (m := m) qs + 3 : ℕ) : ℝ) := by
    exact_mod_cast timeBound_le_twice_callable qs hN
  have h := CallableProduct.thin_timeBound qs hN hQ
  calc
    _ ≤ 2 * ((CallableProduct.timeBound (m := m) qs + 3 : ℕ) : ℝ) := ht
    _ ≤ 2 * (262144 * ((19 * m + 1 : ℕ) : ℝ) *
        (65 * ((D m : ℝ) ^ (-(1 / 18 : ℝ)) * (n : ℝ) ^ 2) + qs.length)) := by linarith
    _ = _ := by ring

/-- Occurrence sparsity, which actual producer chunks supply, absorbs every occurrence charge.
The bound includes the adapter's standalone halt; producer execution is charged separately. -/
theorem thin_timeBound_sparse {m n : ℕ} (qs : List (Fin n × Fin n))
    (hN : D m ^ 18 ≤ n) (hQ : qs.length * 2 ^ m ≤ n ^ 2) :
    ((timeBound (m := m) qs + 1 : ℕ) : ℝ) ≤
      34603008 * ((19 * m + 1 : ℕ) : ℝ) * (n : ℝ) ^ 2 / (D m : ℝ) ^ (1 / 18 : ℝ) := by
  have ht : ((timeBound (m := m) qs + 1 : ℕ) : ℝ) ≤
      2 * ((CallableProduct.timeBound (m := m) qs + 3 : ℕ) : ℝ) := by
    exact_mod_cast timeBound_le_twice_callable qs hN
  have h := CallableProduct.thin_timeBound_sparse qs hN hQ
  calc
    _ ≤ 2 * ((CallableProduct.timeBound (m := m) qs + 3 : ℕ) : ℝ) := ht
    _ ≤ 2 * (17301504 * ((19 * m + 1 : ℕ) : ℝ) * (n : ℝ) ^ 2 /
        (D m : ℝ) ^ (1 / 18 : ℝ)) := by linarith
    _ = _ := by ring

end Cslib.Algorithms.WordRAM.ExactTriangle.RecordProduct
