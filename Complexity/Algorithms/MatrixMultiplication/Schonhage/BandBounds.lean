/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.MatrixMultiplication.Schonhage.Layout
import Mathlib.Data.Nat.Choose.Bounds
import Complexity.Algorithms.MatrixMultiplication.Schonhage.Tiling

/-!
# Bounds for guarded band addressing

## Main results

* `bandSize_le_seven_pow`: a complete band fits within the tensor input dimension.
* `band_position_bounds`: all padded row/column arithmetic stays below `N+7^L` before
  the native guard. Row-major matrix addresses are computed only after that guard.
-/

@[expose] public section

namespace Cslib.Algorithms.MatrixMultiplication.Schonhage

private theorem mul_add_lt_mul {a b c d : ℕ} (ha : a < b) (hc : c < d) :
    a * d + c < b * d := by
  have h := Nat.mul_le_mul_right d (Nat.succ_le_of_lt ha)
  rw [Nat.succ_mul] at h
  omega

/-- The entire band dimension is bounded by the flat tensor input dimension. -/
theorem bandSize_le_seven_pow (L m : ℕ) : bandSize L m ≤ 7 ^ L := by
  have hK : K0 L m ≤ 2 ^ L := (Nat.sqrt_le_self _).trans (Nat.choose_le_two_pow _ _)
  have hN : N0 L m ≤ 3 ^ L := Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
  calc bandSize L m ≤ 2 ^ L * 3 ^ L := Nat.mul_le_mul hK hN
    _ = 6 ^ L := by rw [← Nat.mul_pow]
    _ ≤ 7 ^ L := Nat.pow_le_pow_left (by decide) _

/-- Even the last padded band has small block arithmetic. This bound precedes the `r<N`
guard; it does not assert that a padded row/column is a real matrix position. -/
theorem band_position_bounds {L m N β q o : ℕ} (hβ : β < numBands L m N)
    (hq : q < K0 L m) (ho : o < N0 L m) :
    β * K0 L m < N + 7 ^ L ∧
      β * K0 L m + q < N + 7 ^ L ∧
      (β * K0 L m + q) * N0 L m < N + 7 ^ L ∧
      (β * K0 L m + q) * N0 L m + o < N + 7 ^ L := by
  have hb : β * K0 L m + q < numBands L m N * K0 L m := mul_add_lt_mul hβ hq
  have hr : (β * K0 L m + q) * N0 L m + o < numBands L m N * K0 L m * N0 L m :=
    mul_add_lt_mul hb ho
  have hpad : numBands L m N * bandSize L m ≤ N + bandSize L m - 1 :=
    Nat.div_mul_le_self _ _
  have hsize := bandSize_le_seven_pow L m
  have hblock : β * K0 L m + q ≤ (β * K0 L m + q) * N0 L m :=
    Nat.le_mul_of_pos_right _ (N0_pos L m)
  have heq : numBands L m N * K0 L m * N0 L m = numBands L m N * bandSize L m := by
    rw [bandSize, Nat.mul_assoc]
  rw [heq] at hr
  omega

/-- Nonempty matrices need at least one shared band. -/
theorem numBands_pos {L m N : ℕ} (hm : m ≤ L) (hN : 0 < N) : 0 < numBands L m N := by
  have hb : 0 < bandSize L m := Nat.mul_pos (K0_pos hm) (N0_pos L m)
  change 0 < (N + bandSize L m - 1) / bandSize L m
  exact Nat.div_pos (by omega) hb

/-- A full band's original matrix entries fit within one encoding-sized block. This bound
is valid for every `m≤L`, without the thin-regime specialization. -/
theorem bandSize_mul_D_le_ten_pow {L m : ℕ} (hm : m ≤ L) :
    bandSize L m * D m ≤ 10 ^ L := by
  have hK : K0 L m ≤ 2 ^ L := (Nat.sqrt_le_self _).trans (Nat.choose_le_two_pow _ _)
  have hN : N0 L m ≤ 4 ^ (L - m) := Nat.pow_le_pow_left (by decide) _
  calc bandSize L m * D m ≤ (2 ^ L * 4 ^ (L - m)) * 4 ^ m :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul hK hN)
    _ = 8 ^ L := by
      rw [Nat.mul_assoc, ← Nat.pow_add, Nat.sub_add_cancel hm, ← Nat.mul_pow]
    _ ≤ 10 ^ L := Nat.pow_le_pow_left (by decide) _

/-- All original matrix entries are dominated by the shared band catalogue size; this
charges input copying/restoration without a separate thin-regime estimate. -/
theorem matrix_entries_le_band_encodings {L m : ℕ} (hm : m ≤ L) (N : ℕ) :
    N * D m ≤ numBands L m N * 10 ^ L := by
  calc N * D m ≤ padN L m N * D m := Nat.mul_le_mul_right _ (le_padN hm N)
    _ = numBands L m N * (bandSize L m * D m) := by rw [padN, Nat.mul_assoc]
    _ ≤ numBands L m N * 10 ^ L := Nat.mul_le_mul_left _ (bandSize_mul_D_le_ten_pow hm)

/-- For nonempty matrices, table initialization and the original matrix input are all
dominated by a constant times the shared encoding entry count. -/
theorem preparation_shape_le {L m N : ℕ} (hm : m ≤ L) (hN : 0 < N) :
    1 + N * D m + 2 ^ L + 2 * numBands L m N * 10 ^ L ≤
      5 * (numBands L m N * 10 ^ L) := by
  have hinput := matrix_entries_le_band_encodings hm N
  have hmask : 2 ^ L ≤ 10 ^ L := Nat.pow_le_pow_left (by decide) _
  have hpos : 1 ≤ 10 ^ L := Nat.one_le_pow L 10 (by decide)
  have hbands : 10 ^ L ≤ numBands L m N * 10 ^ L :=
    Nat.le_mul_of_pos_left _ (numBands_pos hm hN)
  rw [Nat.mul_assoc]
  omega

end Cslib.Algorithms.MatrixMultiplication.Schonhage
