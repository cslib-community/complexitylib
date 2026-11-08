/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.CallableBox.Exec

/-!
# Complete callable instruction bounds for box products

All source translations, computed setup, the threshold-span adjustment and physical
span normalization are charged. The finite saving counts original occurrences and
keeps polynomial depth factors explicit. No virtual-window clearing is charged or
performed; only original input and exact answer spans are normalized.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.CallableBoxProduct

open Cslib.WordRAM CallableProduct
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- All real adaptation work is linear in original input size, plus source execution. -/
theorem timeBound_le (m t : ℕ) {N : ℕ} (qs : List (Fin N × Fin N)) :
    timeBound m t qs + 3 ≤ 3 * (BoxProduct.timeBound (21 * m) m t qs + 1) +
      2048 * (N * D m + qs.length + 1) := by
  have hlog : Nat.clog 2 (N + qs.length + 3) ≤ N + qs.length + 3 :=
    Nat.clog_le_of_le_pow (Nat.lt_two_pow_self.le)
  have hD : 0 < D m := Nat.pow_pos (by decide)
  have hND : N ≤ N * D m := Nat.le_mul_of_pos_right N hD
  unfold timeBound coreTime QueriedProduct.inputEnd
  omega

/-- The complete standalone charge is controlled by the same finite native work shape. -/
theorem timeBound_le_shape (m t : ℕ) {N : ℕ} (qs : List (Fin N × Fin N)) :
    timeBound m t qs + 3 ≤
      131072 * (21 * m + 1) ^ 2 * BoxProduct.workShape (21 * m) m t N qs.length := by
  let G := (21 * m + 1) ^ 2
  let S := BoxProduct.workShape (21 * m) m t N qs.length
  have hG : 1 ≤ G := by dsimp only [G]; nlinarith only [Nat.zero_le m]
  have hS : N * D m + qs.length + 1 ≤ S := by
    dsimp only [S, BoxProduct.workShape]
    calc N * D m + qs.length + 1 = 1 + N * D m + qs.length := by omega
      _ ≤ _ := (Nat.le_add_right _ _).trans ((Nat.le_add_right _ _).trans
        ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)))
  have hlin := (Nat.mul_le_mul_left 2048 hS).trans
    (Nat.mul_le_mul_right S (show 2048 ≤ 2048 * G by omega))
  have hbase := BoxProduct.timeBound_le (L := 21 * m) (m := m) (by omega) t qs
  have h := timeBound_le m t qs
  change BoxProduct.timeBound (21 * m) m t qs + 1 ≤ 32768 * G * S at hbase
  simp only [Nat.mul_assoc] at hbase hlin ⊢
  change _ ≤ 131072 * (G * S)
  omega

/-- Complete callable finite saving, including base loading and halt. Original occurrences,
shared preparation, all translated source accesses and all normalization work are included. -/
theorem thin_timeBound (k N : ℕ) (qs : List (Fin N × Fin N))
    (hN : D (9 * k) ^ 18 ≤ N) (hQ : qs.length * 2 ^ (9 * k) ≤ N ^ 2) :
    ((timeBound (9 * k) k qs + 3 : ℕ) : ℝ) ≤
      10485760 * ((189 * k + 1 : ℕ) : ℝ) ^ 2 * ((9 * k + 1 : ℕ) : ℝ) *
        (D (9 * k) : ℝ) ^ (-(8 / 125 : ℝ)) * (N : ℝ) ^ 2 := by
  have hc : ((timeBound (9 * k) k qs + 3 : ℕ) : ℝ) ≤
      131072 * ((189 * k + 1 : ℕ) : ℝ) ^ 2 *
        (BoxProduct.workShape (189 * k) (9 * k) k N qs.length : ℝ) := by
    have h := timeBound_le_shape (9 * k) k qs
    rw [show 21 * (9 * k) = 189 * k by omega] at h
    exact_mod_cast h
  have hs : (BoxProduct.workShape (189 * k) (9 * k) k N qs.length : ℝ) ≤
      80 * ((9 * k + 1 : ℕ) : ℝ) * (D (9 * k) : ℝ) ^ (-(8 / 125 : ℝ)) *
        (N : ℝ) ^ 2 := by
    simpa only [BoxProduct.workShape, Nat.cast_add, Nat.cast_one] using
      BoxTradeoff.nativeShape_ninth_blocks_rpow k N qs.length hN hQ
  have h := hc.trans (mul_le_mul_of_nonneg_left hs (by positivity))
  convert h using 1; ring

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.CallableBoxProduct
