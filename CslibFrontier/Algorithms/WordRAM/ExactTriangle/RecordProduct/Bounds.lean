/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.RecordProduct.Producer
public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.RecordProduct.NumericBounds

/-!
# Charged adapter overhead and per-record thin bounds

`RecordProduct.timeBound` adds linear preparation and call overhead in `n * D m + qs.length` to
`CallableProduct.timeBound`, so distinct-set and occurrence sparsity bounds transfer from
`CallableProduct`. Input-derived width and word envelopes (`admissionWidth`, `wordBound`) live in
`RecordProduct.NumericBounds`; summing all records for an ExactTriangle solver is separate.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.RecordProduct

open Cslib.WordRAM Cslib.Algorithms.ExactTriangle
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage

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
