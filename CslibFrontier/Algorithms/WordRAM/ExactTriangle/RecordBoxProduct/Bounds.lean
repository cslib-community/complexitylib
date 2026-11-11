/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.RecordBoxProduct.Exec

/-!
# Complete finite saving for an actual prepared-record box call

All descriptor decoding, original matrix/coordinate copies, header/threshold patch,
call setup/return and halt are included. The original native producer is charged
separately by `RecordProduct.preparationTime`. Summing every ET record and selecting
native parameters remain separate obligations.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.RecordBoxProduct

open Cslib.WordRAM RecordProduct
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage

/-- Actual record adaptation is absorbed by a constant times the complete callable ledger.
The original size assumption supplies the depth/input comparison. -/
theorem timeBound_le_three_callable {m n : ℕ} (qs : List (Fin n × Fin n))
    (hN : D m ^ 18 ≤ n) :
    timeBound (m := m) qs + 1 ≤ 3 * (CallableBoxProduct.timeBound m (m / 9) qs + 3) := by
  have hn : 1 ≤ n := (Nat.pow_pos (Nat.pow_pos (by decide : 0 < (4 : ℕ)))).trans_le hN
  have hmD : m ≤ D m := (Nat.lt_pow_self (by decide : 1 < (4 : ℕ))).le
  have hm : m ≤ n * D m := hmD.trans (Nat.le_mul_of_pos_left _ hn)
  unfold timeBound CallableBoxProduct.timeBound CallableBoxProduct.coreTime
    QueriedProduct.inputEnd
  omega

/-- The real record consumer has finite `D^(-0.064)` saving under original-occurrence
sparsity, including standalone halt and every adapter instruction. -/
theorem thin_timeBound {k n : ℕ} (qs : List (Fin n × Fin n))
    (hN : D (9 * k) ^ 18 ≤ n) (hQ : qs.length * 2 ^ (9 * k) ≤ n ^ 2) :
    ((timeBound (m := 9 * k) qs + 1 : ℕ) : ℝ) ≤
      31457280 * ((189 * k + 1 : ℕ) : ℝ) ^ 2 * ((9 * k + 1 : ℕ) : ℝ) *
        (D (9 * k) : ℝ) ^ (-(8 / 125 : ℝ)) * (n : ℝ) ^ 2 := by
  have hnat := timeBound_le_three_callable qs hN
  rw [show 9 * k / 9 = k by omega] at hnat
  have hc : ((timeBound (m := 9 * k) qs + 1 : ℕ) : ℝ) ≤
      3 * ((CallableBoxProduct.timeBound (9 * k) k qs + 3 : ℕ) : ℝ) := by exact_mod_cast hnat
  have h := hc.trans (mul_le_mul_of_nonneg_left
    (CallableBoxProduct.thin_timeBound k n qs hN hQ) (by norm_num))
  convert h using 1; ring

end Cslib.Algorithms.WordRAM.ExactTriangle.RecordBoxProduct
