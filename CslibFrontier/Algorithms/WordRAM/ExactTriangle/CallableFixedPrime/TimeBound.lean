/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime.Exec

/-!
# Aggregate callable box-backed fixed-prime charge

The memory-window compiler multiplies the actual complete source charge by at most three.
Only the original input adaptation and computed-modulus/return overhead are added. The source
producer and all-product saving remain explicit, as does the single global false-positive
reserve. This does not choose parameters or prove the final ExactTriangle/3SUM exponent.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime

open Cslib.WordRAM Cslib.Matrix Cslib.Algorithms.ExactTriangle
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Halt-inclusive complete caller bound. It includes all copies, setup, source instructions,
recursion, index/dispatch, normalization, return copies and exactly one final halt. The box
source's own halt-inclusive bound is retained conservatively inside the factor-three term. -/
theorem timeBound_le {k n g p : ℕ} (hn : 0 < n) (values : List ℤ) (mem : ℕ → ℕ)
    (hD : 16 ≤ D (9 * k)) (hg : 1 ≤ g) (hp : p ∈ Nat.sqrtPrimeWindow (D (9 * k)))
    (hN : D (9 * k) ^ 18 ≤ n) :
    let V := fun q => values.getD q 0
    let F := falsePositiveCount (fun u v : Fin n => V (pairIndex (u, v)))
      (fun u v => V (n * n + pairIndex (u, v)))
      (fun u v => V (2 * (n * n) + pairIndex (u, v))) p
    ((timeBound (m := 9 * k) hn g p values mem + 1 : ℕ) : ℝ) ≤
      24 * (n : ℝ) ^ 2 +
        24669 * (Nat.clog 2 (n + D (9 * k) + g + p + rawTotal n values + 4) : ℕ) + 483 +
        3 * (690 * (n : ℝ) ^ 2 * D (9 * k) * g +
          125829120 * ((189 * k + 1 : ℕ) : ℝ) ^ 2 * ((9 * k + 1 : ℕ) : ℝ) *
            (D (9 * k) : ℝ) ^ (-(8 / 125 : ℝ)) * (n : ℝ) ^ 3 * g +
          (4 * (n : ℝ) * g) *
            ((5 * Nat.sqrt (D (9 * k)) + 8 * queryCap n (D (9 * k)) + 61 : ℕ) : ℝ) +
          (((42 * pieceSize (D (9 * k)) g + 28) * (F + 1) + 7 : ℕ) : ℝ)) := by
  have h := mul_le_mul_of_nonneg_left
    (FixedPrime.timeBound_le hn values mem hD hg hp hN) (by norm_num : (0 : ℝ) ≤ 3)
  calc
    _ = 24 * (n : ℝ) ^ 2 +
        24669 * (Nat.clog 2 (n + D (9 * k) + g + p + rawTotal n values + 4) : ℕ) + 483 +
        3 * (FixedPrime.timeBound (m := 9 * k) hn g p values mem : ℝ) := by
      simp only [timeBound, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, pow_two]
      ring
    _ ≤ _ := add_le_add (le_refl _) h

end Cslib.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime
