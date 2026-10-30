/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.RecordWitness.SourceBounds

/-!
# Charged per-record witness-recovery bound

The actual producer chunk derives the required occurrence sparsity. Preparation and the thin
product retain their already proved charges, and recovery adds actual root/query/control work
plus full interval scans. The scan surplus is the returned native flag, so unsuccessful records
have no additive successful-scan term. This does not sum the outer instance loop or choose a
prime, and it establishes neither aggregate subcubic ET nor the ordinary 3SUM endpoint.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.RecordWitness

open Cslib.WordRAM Cslib.Algorithms.ExactTriangle Cslib.Matrix
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- The quantitative bound applied to the actual initialized execution. Occurrence sparsity
is derived from its computed query count. The scan/count and interval premises are conclusions
of `runs_input`; they are not algorithm inputs or supplied solver/time certificates. -/
theorem initialized_time_le {m n g p length S flag : ℕ} (values : List ℤ)
    (idx : InstanceIndex p) (qs : List (Fin n × Fin n))
    (hcount : qs.length = RecordProduct.recordQueryCount n (D m) p
      (fun q => values.getD q 0) idx)
    (hD : 16 ≤ D m) (hN : D m ^ 18 ≤ n) (hg : 1 ≤ g)
    (hp : p ∈ Nat.sqrtPrimeWindow (D m))
    (hlength : length ≤ pieceSize (D m) g)
    (hS : S ≤ falsePositiveCount
      (fun a b : Fin n => values.getD (pairIndex (a, b)) 0)
      (fun b c : Fin n => values.getD (n * n + pairIndex (b, c)) 0)
      (fun a c : Fin n => values.getD (2 * (n * n) + pairIndex (a, c)) 0) p + flag) :
    let F := falsePositiveCount
      (fun a b : Fin n => values.getD (pairIndex (a, b)) 0)
      (fun b c : Fin n => values.getD (n * n + pairIndex (b, c)) 0)
      (fun a c : Fin n => values.getD (2 * (n * n) + pairIndex (a, c)) 0) p
    ((RecordProduct.preparationTime n (D m) g p values +
      RecordProduct.timeBound (m := m) qs + 5 * Nat.sqrt (D m) + 8 * qs.length +
      (42 * length + 28) * S + 53 : ℕ) : ℝ) ≤
      690 * (n : ℝ) ^ 2 * D m * g +
        34603008 * ((19 * m + 1 : ℕ) : ℝ) * (n : ℝ) ^ 2 /
          (D m : ℝ) ^ (1 / 18 : ℝ) +
        ((5 * Nat.sqrt (D m) + 8 * qs.length +
          (42 * pieceSize (D m) g + 28) * (F + flag) + 52 : ℕ) : ℝ) := by
  let F := falsePositiveCount
    (fun a b : Fin n => values.getD (pairIndex (a, b)) 0)
    (fun b c : Fin n => values.getD (n * n + pairIndex (b, c)) 0)
    (fun a c : Fin n => values.getD (2 * (n * n) + pairIndex (a, c)) 0) p
  change S ≤ F + flag at hS
  have hQ : qs.length * 2 ^ m ≤ n ^ 2 := by
    rw [hcount]
    exact (Nat.mul_le_mul_right (2 ^ m) (min_le_left _ _)).trans
      (RecordProduct.queryCap_mul_two_pow_le n m)
  have hbase := RecordProduct.initialized_time_le values qs hD hN hg hp hQ
  have hscan : (42 * length + 28) * S ≤
      (42 * pieceSize (D m) g + 28) * (F + flag) :=
    Nat.mul_le_mul (by omega) hS
  let extra := 5 * Nat.sqrt (D m) + 8 * qs.length +
    (42 * pieceSize (D m) g + 28) * (F + flag) + 52
  have htotal : RecordProduct.preparationTime n (D m) g p values +
      RecordProduct.timeBound (m := m) qs + 5 * Nat.sqrt (D m) + 8 * qs.length +
      (42 * length + 28) * S + 53 ≤
      RecordProduct.preparationTime n (D m) g p values +
        RecordProduct.timeBound (m := m) qs + 1 + extra := by
    dsimp only [extra]
    omega
  calc
    _ ≤ ((RecordProduct.preparationTime n (D m) g p values +
        RecordProduct.timeBound (m := m) qs + 1 + extra : ℕ) : ℝ) := Nat.cast_le.mpr htotal
    _ = ((RecordProduct.preparationTime n (D m) g p values +
        RecordProduct.timeBound (m := m) qs + 1 : ℕ) : ℝ) + (extra : ℝ) := Nat.cast_add _ _
    _ ≤ _ := add_le_add hbase (le_rfl : (extra : ℝ) ≤ extra)

end Cslib.Algorithms.WordRAM.ExactTriangle.RecordWitness
