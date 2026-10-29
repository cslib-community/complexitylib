/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Callable.Flat

/-!
# Original-parameter width, space and charge for callable products

The virtual window reservation is polynomial in the original row and occurrence counts. Its
large fixed exponent is explicit; the program does not initialize that whole interval. Actual
setup and return work is linear in original matrix/input size, plus the translated product.
Distinct-set sparsity retains the additive occurrence charge; occurrence sparsity absorbs it.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.CallableProduct

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- The reserved window has a fixed polynomial size in original dimensions and query count. -/
theorem windowSize_le (N Q : ℕ) : windowSize N Q ≤ (2 * (N + Q + 3)) ^ 128 := by
  have hc := Nat.clog_pos (by decide : 1 < (2 : ℕ)) (by omega : 1 < N + Q + 3)
  have hp := Nat.pow_pred_clog_lt_self (by decide : 1 < (2 : ℕ)) (by omega : 1 < N + Q + 3)
  have he : Nat.clog 2 (N + Q + 3) = (Nat.clog 2 (N + Q + 3)).pred + 1 :=
    (Nat.succ_pred_eq_of_pos hc).symm
  have hceil : 2 ^ Nat.clog 2 (N + Q + 3) ≤ 2 * (N + Q + 3) := by
    rw [he, pow_succ]
    omega
  have h := Nat.pow_le_pow_left hceil 128
  simpa only [windowSize, sourceWidth, ← pow_mul, Nat.mul_comm 128] using h

/-- Every physical width at least a positive logarithmic threshold admits the complete runtime
window and all setup/return addresses. No intermediate-fit certificate is needed. -/
theorem physical_fits {W b N Q : ℕ}
    (hW : 256 * Nat.clog 2 (b + N + Q + 5) ≤ W) :
    Fits W (b + 4 * windowSize N Q + 1024) := by
  let c := Nat.clog 2 (b + N + Q + 5)
  have hc : 0 < c := Nat.clog_pos (by decide) (by omega)
  have hceil := Nat.le_pow_clog (by decide : 1 < (2 : ℕ)) (b + N + Q + 5)
  change b + N + Q + 5 ≤ 2 ^ c at hceil
  have hm : windowSize N Q ≤ 2 ^ (128 * c) := by
    apply Nat.pow_le_pow_right (by decide)
    apply Nat.mul_le_mul_left 128
    exact Nat.clog_mono_right 2 (by omega)
  have hb : b ≤ 2 ^ (128 * c) := by
    have he : c ≤ 128 * c := by omega
    exact (show b ≤ 2 ^ c by omega).trans (Nat.pow_le_pow_right (by decide) he)
  have hpos : 1 ≤ 2 ^ (128 * c) := Nat.one_le_pow _ _ (by decide)
  have hsum : b + 4 * windowSize N Q + 1024 < 2 ^ (128 * c + 11) := by
    rw [pow_add]
    norm_num only [Nat.reducePow]
    omega
  exact hsum.trans_le (Nat.pow_le_pow_right (by decide) (by change 256 * c ≤ W at hW; omega))

/-- Full standalone charge (including its base load and halt): constant-factor actual product
cost plus linear adaptation. No bulk-window or caller-catalogue copy is hidden in this bound. -/
theorem timeBound_le {m N : ℕ} (qs : List (Fin N × Fin N)) :
    timeBound (m := m) qs + 3 ≤
      3 * (QueriedProduct.timeBound (show m ≤ 19 * m by omega) qs + 1) +
        2048 * (N * D m + qs.length + 1) := by
  have hlog : Nat.clog 2 (N + qs.length + 3) ≤ N + qs.length + 3 :=
    Nat.clog_le_of_le_pow (Nat.lt_two_pow_self.le)
  have hD : 0 < D m := Nat.pow_pos (by decide)
  have hND : N ≤ N * D m := Nat.le_mul_of_pos_right N hD
  unfold timeBound coreTime QueriedProduct.inputEnd
  omega

/-- Under distinct-position sparsity, every duplicate occurrence retains its additive charge.
This quantitative saving bounds the real callable program, including initialization and halt. -/
theorem thin_timeBound {m N : ℕ} (qs : List (Fin N × Fin N)) (hN : D m ^ 18 ≤ N)
    (hQ : qs.toFinset.card * 2 ^ m ≤ N ^ 2) :
    ((timeBound (m := m) qs + 3 : ℕ) : ℝ) ≤
      262144 * ((19 * m + 1 : ℕ) : ℝ) *
        (65 * ((D m : ℝ) ^ (-(1 / 18 : ℝ)) * (N : ℝ) ^ 2) + qs.length) := by
  have hNpos : 0 < N := (Nat.pow_pos (Nat.pow_pos (by decide : 0 < (4 : ℕ)))).trans_le hN
  have hp := preparation_shape_le (show m ≤ 19 * m by omega) hNpos
  have hpR : ((1 + N * D m : ℕ) : ℝ) ≤
      ((5 * (numBands (19 * m) m N * 10 ^ (19 * m)) : ℕ) : ℝ) := by
    exact_mod_cast ((Nat.le_add_right (1 + N * D m) (2 ^ (19 * m))).trans
      (Nat.le_add_right _ (2 * numBands (19 * m) m N * 10 ^ (19 * m)))).trans hp
  have he := encodings_total_le m N hN
  have hlinear : ((N * D m + qs.length + 1 : ℕ) : ℝ) ≤
      10 * ((D m : ℝ) ^ (-(1 / 18 : ℝ)) * (N : ℝ) ^ 2) + qs.length := by
    push_cast at hpR he ⊢
    nlinarith only [hpR, he]
  have hbase := QueriedProduct.thin_timeBound m N qs hN hQ
  have htime : ((timeBound (m := m) qs + 3 : ℕ) : ℝ) ≤
      3 * ((QueriedProduct.timeBound (show m ≤ 19 * m by omega) qs + 1 : ℕ) : ℝ) +
        2048 * ((N * D m + qs.length + 1 : ℕ) : ℝ) := by exact_mod_cast timeBound_le qs
  have hL : (1 : ℝ) ≤ ((19 * m + 1 : ℕ) : ℝ) := by norm_cast; omega
  have hG : 0 ≤ (D m : ℝ) ^ (-(1 / 18 : ℝ)) * (N : ℝ) ^ 2 := by positivity
  have hQ0 : 0 ≤ (qs.length : ℝ) := Nat.cast_nonneg _
  nlinarith only [htime, hbase, hlinear, mul_nonneg (sub_nonneg.mpr hL) hG,
    mul_nonneg (sub_nonneg.mpr hL) hQ0, hG, hQ0]

/-- Occurrence sparsity absorbs the duplicate charge and yields the complete charged saving. -/
theorem thin_timeBound_sparse {m N : ℕ} (qs : List (Fin N × Fin N)) (hN : D m ^ 18 ≤ N)
    (hQ : qs.length * 2 ^ m ≤ N ^ 2) :
    ((timeBound (m := m) qs + 3 : ℕ) : ℝ) ≤
      17301504 * ((19 * m + 1 : ℕ) : ℝ) * (N : ℝ) ^ 2 / (D m : ℝ) ^ (1 / 18 : ℝ) := by
  have hset : qs.toFinset.card * 2 ^ m ≤ N ^ 2 :=
    (Nat.mul_le_mul_right _ (List.toFinset_card_le qs)).trans hQ
  have h := thin_timeBound qs hN hset
  have hQr : (qs.length : ℝ) * (2 : ℝ) ^ m ≤ (N : ℝ) ^ 2 := by exact_mod_cast hQ
  have hlen := mul_le_mul_of_nonneg_left hQr (saving_pos m).le
  have hpow : 1 ≤ saving m * (2 : ℝ) ^ m := by
    rw [← saving_mul_two_rpow m]
    apply mul_le_mul_of_nonneg_left _ (saving_pos m).le
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have := Nat.cast_nonneg (α := ℝ) m
    linarith
  have hlen' : (qs.length : ℝ) ≤
      (D m : ℝ) ^ (-(1 / 18 : ℝ)) * (N : ℝ) ^ 2 := by
    rw [← saving_eq_D_rpow]
    nlinarith only [hlen, mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg qs.length :
      (0 : ℝ) ≤ qs.length)]
  have hL : 0 ≤ ((19 * m + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hfinal : ((timeBound (m := m) qs + 3 : ℕ) : ℝ) ≤
      17301504 * ((19 * m + 1 : ℕ) : ℝ) *
        ((D m : ℝ) ^ (-(1 / 18 : ℝ)) * (N : ℝ) ^ 2) := by
    nlinarith only [h, mul_nonneg hL (sub_nonneg.mpr hlen')]
  rw [Real.rpow_neg (by positivity)] at hfinal
  simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hfinal

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.CallableProduct
