/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Product.Width

/-!
# Quantitative saving for actual native queried products

## Main results

* `QueriedProduct.thin_timeBound`: the native charge, including halt, has the proved thin
  saving plus an explicit term for every original query occurrence.
* `QueriedProduct.thin_timeBound_sparse`: an occurrence-count sparsity condition absorbs
  that term and gives the complete charged `N² / D^(1/18)` bound, with a depth factor.

These results compose the actual native charge with the existing finite encoding/tile/leaf
bounds from [AlmanWilliams2026, Section 2]. The occurrence hypothesis in the second result is
stronger than the source's distinct-position cardinality condition when requests repeat.
No sparse solver or running-time assertion is assumed.
-/

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- The source's distinct-position sparsity condition retains an explicit charge for list
multiplicity. Every actual copy, conversion, producer, tile, epoch and report is included. -/
public theorem thin_timeBound (m N : ℕ) (qs : List (Fin N × Fin N))
    (hN : D m ^ 18 ≤ N) (hW : qs.toFinset.card * 2 ^ m ≤ N ^ 2) :
    ((timeBound (show m ≤ 19 * m by omega) qs + 1 : ℕ) : ℝ) ≤
      65536 * ((19 * m + 1 : ℕ) : ℝ) *
        (65 * ((D m : ℝ) ^ (-(1 / 18 : ℝ)) * (N : ℝ) ^ 2) + qs.length) := by
  have hm : m ≤ 19 * m := by omega
  have hNpos : 0 < N := (Nat.pow_pos (show 0 < D m from Nat.pow_pos (by decide))).trans_le hN
  have hB := numBands_pos hm hNpos
  have hH : 10 ^ (19 * m) ≤ numBands (19 * m) m N * 10 ^ (19 * m) :=
    Nat.le_mul_of_pos_left _ hB
  have hprep := preparation_shape_le hm hNpos
  have henc := encodings_total_le m N hN
  have htiles := minutiae_total_le m N qs.toFinset hN hW
  have hleaves := total_leaves_le (MaskTable.layout hm) qs.toFinset hN hW
  have hc : (Cslib.Algorithms.MatrixMultiplication.Schonhage.tiles (19 * m) m N).card =
      numBands (19 * m) m N ^ 2 := by
    simp only [Cslib.Algorithms.MatrixMultiplication.Schonhage.tiles,
      Finset.card_product, Finset.card_range, pow_two]
  rw [hc] at htiles
  have hprepR : ((1 + N * D m + 2 ^ (19 * m) +
      2 * numBands (19 * m) m N * 10 ^ (19 * m) : ℕ) : ℝ) ≤
      5 * ((numBands (19 * m) m N * 10 ^ (19 * m) : ℕ) : ℝ) := by exact_mod_cast hprep
  have hHR : ((10 ^ (19 * m) : ℕ) : ℝ) ≤
      ((numBands (19 * m) m N * 10 ^ (19 * m) : ℕ) : ℝ) := by exact_mod_cast hH
  have hshape : ((1 + N * D m + qs.length + 2 ^ (19 * m) +
      (numBands (19 * m) m N + 1) * 10 ^ (19 * m) + numBands (19 * m) m N ^ 2 +
        ∑ T ∈ Cslib.Algorithms.MatrixMultiplication.Schonhage.tiles (19 * m) m N,
          (Cslib.Algorithms.MatrixMultiplication.Schonhage.leaves
            (wantedStrings (MaskTable.layout hm) qs.toFinset T.1 T.2)).card : ℕ) : ℝ) ≤
      65 * ((D m : ℝ) ^ (-(1 / 18 : ℝ)) * (N : ℝ) ^ 2) + qs.length := by
    have hnonneg : 0 ≤ (D m : ℝ) ^ (-(1 / 18 : ℝ)) * (N : ℝ) ^ 2 := by positivity
    push_cast at hprepR hHR henc htiles hleaves ⊢
    nlinarith only [hprepR, hHR, henc, htiles, hleaves, hnonneg,
      Nat.cast_nonneg (α := ℝ) (K (19 * m) m), Nat.cast_nonneg (α := ℝ) qs.toFinset.card,
      Nat.cast_nonneg (α := ℝ) (N * D m), Nat.cast_nonneg (α := ℝ) (2 ^ (19 * m))]
  have hcost := timeBound_le hm qs
  have hcostR : ((timeBound hm qs + 1 : ℕ) : ℝ) ≤
      65536 * ((19 * m + 1 : ℕ) : ℝ) *
        ((1 + N * D m + qs.length + 2 ^ (19 * m) +
          (numBands (19 * m) m N + 1) * 10 ^ (19 * m) + numBands (19 * m) m N ^ 2 +
            ∑ T ∈ Cslib.Algorithms.MatrixMultiplication.Schonhage.tiles (19 * m) m N,
              (Cslib.Algorithms.MatrixMultiplication.Schonhage.leaves
                (wantedStrings (MaskTable.layout hm) qs.toFinset T.1 T.2)).card : ℕ) : ℝ) := by
    exact_mod_cast hcost
  exact hcostR.trans (mul_le_mul_of_nonneg_left hshape (by positivity))

/-- A bound on all original occurrences, rather than only distinct coordinates, absorbs
the actual list-input/reporting charge. The final halt is included. -/
public theorem thin_timeBound_sparse (m N : ℕ) (qs : List (Fin N × Fin N))
    (hN : D m ^ 18 ≤ N) (hQ : qs.length * 2 ^ m ≤ N ^ 2) :
    ((timeBound (show m ≤ 19 * m by omega) qs + 1 : ℕ) : ℝ) ≤
      4325376 * ((19 * m + 1 : ℕ) : ℝ) * (N : ℝ) ^ 2 / (D m : ℝ) ^ (1 / 18 : ℝ) := by
  have hW : qs.toFinset.card * 2 ^ m ≤ N ^ 2 :=
    (Nat.mul_le_mul_right _ (List.toFinset_card_le qs)).trans hQ
  have hQ' : (qs.length : ℝ) * (2 : ℝ) ^ m ≤ (N : ℝ) ^ 2 := by exact_mod_cast hQ
  have hp : (2 : ℝ) ^ ((m : ℝ) / 9) ≤ (2 : ℝ) ^ m := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (by have := Nat.cast_nonneg (α := ℝ) m; linarith)
  have hlen : (qs.length : ℝ) ≤ (D m : ℝ) ^ (-(1 / 18 : ℝ)) * (N : ℝ) ^ 2 := by
    rw [← saving_eq_D_rpow]
    calc (qs.length : ℝ) = saving m * (qs.length * (2 : ℝ) ^ ((m : ℝ) / 9)) := by
          rw [mul_left_comm, saving_mul_two_rpow, mul_one]
      _ ≤ saving m * (qs.length * (2 : ℝ) ^ m) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg _))
          (saving_pos m).le
      _ ≤ saving m * (N : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hQ' (saving_pos m).le
  have h := thin_timeBound m N qs hN hW
  have hfinal : ((timeBound (show m ≤ 19 * m by omega) qs + 1 : ℕ) : ℝ) ≤
      4325376 * ((19 * m + 1 : ℕ) : ℝ) *
        ((D m : ℝ) ^ (-(1 / 18 : ℝ)) * (N : ℝ) ^ 2) := by
    have hL : 0 ≤ ((19 * m + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith only [h, hlen, mul_nonneg hL (sub_nonneg.mpr hlen)]
  rw [Real.rpow_neg (by positivity)] at hfinal
  simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hfinal

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct
