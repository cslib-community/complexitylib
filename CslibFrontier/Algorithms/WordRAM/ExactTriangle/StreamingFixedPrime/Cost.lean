/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.FixedPrime.TimeBound

/-!
# Streaming charges fit `FixedPrime.timeBound`

Each record visit uses `40 * (n * D m) + 66` instructions and the heap reset uses one more.
Executing construction and consumption in a single loop fits within the conservative
`FixedPrime.timeBound` envelope, including the final halt. Product and global failure-scan terms
are unchanged.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.StreamingFixedPrime

open Cslib.WordRAM Cslib.Matrix Cslib.Algorithms.ExactTriangle
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open FixedPrime

/-- Charge the catalogue/setup prefix, all streaming iterations, controller overhead and final
halt within `FixedPrime.timeBound`. No extra successful scan is reserved per instance. -/
theorem streamingCharge_le_timeBound {m n g p : ℕ} (hn : 0 < n) (values : List ℤ)
    (initial a : Data 64) (hp : p ≠ 0)
    (hout : Instances.Output n (D m) g p (fun q => values.getD q 0) initial a) :
    let V := fun q => values.getD q 0
    let wAB := fun u v : Fin n => V (pairIndex (u, v))
    let wBC := fun u c : Fin n => V (n * n + pairIndex (u, c))
    let wAC := fun u c : Fin n => V (2 * (n * n) + pairIndex (u, c))
    Catalogue.cost n (D m) p + 26 +
      ((∑ idx ∈ instanceIndices wAB (D m) g p,
        (recordBase (m := m) hn V a.mem idx + (40 * (n * D m) + 67))) +
        (42 * pieceSize (D m) g + 28) * (falsePositiveCount wAB wBC wAC p + 1) + 7) + 1 ≤
      FixedPrime.timeBound (m := m) hn g p values a.mem := by
  let V := fun q => values.getD q 0
  let I := instanceIndices (fun u v : Fin n => V (pairIndex (u, v))) (D m) g p
  let C := fun rho => Nat.count (fun q => (V q % (p : ℤ)).toNat = rho) (n * n)
  let M := ChunkCatalogue.before C (queryCap n (D m)) p * numPieces n (D m) g
  have hc : M = I.card := by
    have hcount := PreparationSpec.count_eq_card V
      (fun u v : Fin n => V (pairIndex (u, v))) hp (by intro u v; rfl) hout
    rw [hout.2.2.2.2.1] at hcount
    exact hcount
  have sum_charge : (∑ idx ∈ I, (recordBase (m := m) hn V a.mem idx + (40 * (n * D m) + 67))) =
      (∑ idx ∈ I, recordBase (m := m) hn V a.mem idx) + I.card * (40 * (n * D m) + 67) := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Nat.mul_add]
    norm_num
  dsimp only
  change Catalogue.cost n (D m) p + 26 +
    ((∑ idx ∈ I, (recordBase (m := m) hn V a.mem idx + (40 * (n * D m) + 67))) + _ + 7) + 1 ≤ _
  rw [sum_charge, ← hc]
  unfold FixedPrime.timeBound RecordProduct.preparationTime Instances.timeBound
  change Catalogue.cost n (D m) p + 26 +
    ((∑ idx ∈ I, recordBase (m := m) hn V a.mem idx) + M * (40 * (n * D m) + 67) + _ + 7) + 1 ≤
      Catalogue.cost n (D m) p + M * (40 * (n * D m) + 68) + 29 +
        (∑ idx ∈ I, recordBase (m := m) hn V a.mem idx) + _ + 7
  nlinarith only [Nat.zero_le M]

end Cslib.Algorithms.WordRAM.ExactTriangle.StreamingFixedPrime
