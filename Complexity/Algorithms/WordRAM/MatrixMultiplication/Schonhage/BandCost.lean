/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandProgram
public import Complexity.Algorithms.MatrixMultiplication.Schonhage.BandBounds

/-!
# Numerical cost bounds for shared band preparation

## Main definitions

* `BandPreparation.timeBound`: a uniform budget for all setup, tables, input copying,
  band preparation, shared encoder calls and catalogue copies.

## Main results

* `BandPreparation.thin_timeBound`: its explicit finite thin-regime bound. This numerical
  lemma is separate from the theorem connecting the budget to the actual native execution.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandPreparation

open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Generic numerical instruction budget; a final halt is charged separately. -/
def timeBound (L m N : ℕ) : ℕ :=
  4096 * (L + 1) * (1 + N * D m + 2 ^ L + 2 * numBands L m N * 10 ^ L)

/-- At `L=19m`, all original input and table overhead is absorbed by the saving for shared
encodings. The displayed constants and polynomial exponent are fixed and positive. -/
theorem thin_timeBound (m N : ℕ) (hN : D m ^ 18 ≤ N) :
    (timeBound (19 * m) m N : ℝ) ≤
      40960 * ((19 * m + 1 : ℕ) : ℝ) * (D m : ℝ) ^ (-(1 / 18 : ℝ)) * (N : ℝ) ^ 2 := by
  have hNpos : 0 < N := (Nat.pow_pos (show 0 < D m from Nat.pow_pos (by decide))).trans_le hN
  have hs := preparation_shape_le (show m ≤ 19 * m by omega) hNpos
  have hsR : ((1 + N * D m + 2 ^ (19 * m) +
      2 * numBands (19 * m) m N * 10 ^ (19 * m) : ℕ) : ℝ) ≤
      5 * ((numBands (19 * m) m N * 10 ^ (19 * m) : ℕ) : ℝ) := by exact_mod_cast hs
  have he := encodings_total_le m N hN
  have hshape : ((1 + N * D m + 2 ^ (19 * m) +
      2 * numBands (19 * m) m N * 10 ^ (19 * m) : ℕ) : ℝ) ≤
      10 * (D m : ℝ) ^ (-(1 / 18 : ℝ)) * (N : ℝ) ^ 2 := by
    push_cast at hsR he ⊢
    nlinarith only [hsR, he]
  calc (timeBound (19 * m) m N : ℝ)
      = 4096 * ((19 * m + 1 : ℕ) : ℝ) * ((1 + N * D m + 2 ^ (19 * m) +
          2 * numBands (19 * m) m N * 10 ^ (19 * m) : ℕ) : ℝ) := by
        simp only [timeBound, Nat.cast_mul, Nat.cast_ofNat]
    _ ≤ 4096 * ((19 * m + 1 : ℕ) : ℝ) *
        (10 * (D m : ℝ) ^ (-(1 / 18 : ℝ)) * (N : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hshape (by positivity)
    _ = _ := by ring

/-- Equivalent division form of the thin-regime bound requested by the matrix algorithm. -/
theorem thin_timeBound_div (m N : ℕ) (hN : D m ^ 18 ≤ N) :
    (timeBound (19 * m) m N : ℝ) ≤
      40960 * ((19 * m + 1 : ℕ) : ℝ) * (N : ℝ) ^ 2 / (D m : ℝ) ^ (1 / 18 : ℝ) := by
  have h := thin_timeBound m N hN
  rw [Real.rpow_neg (by positivity)] at h
  simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandPreparation
