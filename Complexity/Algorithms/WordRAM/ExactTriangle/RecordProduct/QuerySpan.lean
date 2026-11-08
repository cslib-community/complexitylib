/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.RecordProduct.RecordData

/-!
# Queries precede the reusable instance slot

An occupied chunk's complete interleaved query occurrence span lies below the first record,
independently of how many records have been materialized. Future pieces may reuse the raw
matrix slot while retaining these coordinates and the original signed matrices.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.RecordProduct

open Cslib.WordRAM Cslib.Matrix Cslib.Algorithms.ExactTriangle

/-- The shared query array is protected below the output slot, not merely below the end of
an all-record allocation. Duplicate occurrences keep their full two-word footprint. -/
theorem query_end_le_output {n D g p : ℕ} (values : ℕ → ℤ)
    (hp : p ≠ 0) (hD : 1 ≤ D) (hDn : D ≤ n) (idx : InstanceIndex p)
    (hidx : idx ∈ instanceIndices (fun a b : Fin n => values (pairIndex (a, b))) D g p) :
    let N := n * n
    let C := fun rho => Nat.count (fun q => (values q % (p : ℤ)).toNat = rho) N
    recordQueries n D p idx + 2 * recordQueryCount n D p values idx ≤
      5 + 6 * N + p + 2 * N * p + 3 * ChunkCatalogue.before C (queryCap n D) p := by
  let N := n * n
  let C := fun rho => Nat.count (fun q => (values q % (p : ℤ)).toNat = rho) N
  have hpositive := recordQueryCount_pos values hp hD hDn idx hidx
  have hcount : C idx.1.val ≤ N := Nat.count_le _
  have hQ : idx.2.1 * queryCap n D + recordQueryCount n D p values idx ≤ N := by
    change 0 < min (queryCap n D) (C idx.1.val - idx.2.1 * queryCap n D) at hpositive
    change idx.2.1 * queryCap n D +
      min (queryCap n D) (C idx.1.val - idx.2.1 * queryCap n D) ≤ N
    omega
  have hrho := Nat.mul_le_mul_right (2 * N) (Nat.succ_le_of_lt idx.1.isLt)
  dsimp only [recordQueries]
  change 5 + 6 * N + p + 2 * idx.1.val * N + 2 * (idx.2.1 * queryCap n D) +
    2 * recordQueryCount n D p values idx ≤
      5 + 6 * N + p + 2 * N * p + 3 * ChunkCatalogue.before C (queryCap n D) p
  nlinarith only [hQ, hrho,
    Nat.zero_le (3 * ChunkCatalogue.before C (queryCap n D) p)]

end Cslib.Algorithms.WordRAM.ExactTriangle.RecordProduct
