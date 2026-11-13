/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.StreamingFixedPrime.Cursor

/-!
# Immutable catalogue readback for streaming

A genuine standalone output may index the existing mathematical accounting. Only its immutable
prefix is related to current memory here; no record or matrix block is transferred. The slot
writer itself requires just the current residue words and selected descriptor.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.StreamingFixedPrime

open Cslib.WordRAM Cslib.Matrix Cslib.Algorithms.ExactTriangle

/-- Retain just the actual residue arrays and selected catalogue descriptor below the slot. -/
theorem catalogue_readback {n D g p : ℕ} (values : ℕ → ℤ) (initial a x : Data 64)
    (hout : Instances.Output n D g p values initial a) (hp : p ≠ 0)
    (cursor : Cursor n D g p values x)
    (hmem : Set.EqOn x.mem a.mem (Set.Iio (a.regs Instances.output)))
    (idx : InstanceIndex p)
    (hidx : idx ∈ instanceIndices (fun u v : Fin n => values (pairIndex (u, v))) D g p) :
    (∀ k < 3 * (n * n), x.mem (5 + 3 * (n * n) + k) = (values k % (p : ℤ)).toNat) ∧
    (let C := fun rho => Nat.count (fun k => (values k % (p : ℤ)).toNat = rho) (n * n)
     let chunk := ChunkCatalogue.before C (queryCap n D) idx.residue.val + idx.chunk
     x.mem (chunk * 3 + x.regs Instances.descriptors) = idx.residue.val ∧
     x.mem (chunk * 3 + x.regs Instances.descriptors + 1) =
       RecordProduct.recordQueries n D p idx ∧
     x.mem (chunk * 3 + x.regs Instances.descriptors + 2) =
       RecordProduct.recordQueryCount n D p values idx) := by
  let N := n * n
  let C := fun rho => Nat.count (fun k => (values k % (p : ℤ)).toNat = rho) N
  let K := ChunkCatalogue.before C (queryCap n D) p
  let chunk := ChunkCatalogue.before C (queryCap n D) idx.residue.val + idx.chunk
  let desc := 5 + 6 * N + p + 2 * N * p
  have hcard : (residueClass (fun u v : Fin n => values (pairIndex (u, v))) p idx.residue).card =
      C idx.residue.val := QuerySpec.card_residueClass _ hp _ (by intro pair; rfl) idx.residue
  have hk := ((mem_instanceIndices _ idx).mp hidx).1
  have hk' : idx.chunk < C idx.residue.val ⌈/⌉ queryCap n D := by
    simpa only [numChunks, hcard] using hk
  have hchunk : chunk < K :=
    ChunkCatalogue.before_add_lt C (queryCap n D) idx.residue.isLt hk'
  have ho : a.regs Instances.output = desc + 3 * K := hout.2.2.2.1
  have hd := hout.2.2.2.2.2.2.2.2.2.1 idx.residue.val idx.residue.isLt idx.chunk hk'
  constructor
  · intro k hk
    rw [hmem (show 5 + 3 * N + k < a.regs Instances.output by rw [ho]; omega)]
    exact hout.2.2.2.2.2.2.1 k hk
  · have hdir (j : ℕ) (hj : j < 3) : desc + 3 * chunk + j < a.regs Instances.output := by
      rw [ho]
      omega
    rw [cursor.descriptors]
    change x.mem (chunk * 3 + desc) = _ ∧ x.mem (chunk * 3 + desc + 1) = _ ∧
      x.mem (chunk * 3 + desc + 2) = _
    have eq0 : chunk * 3 + desc = desc + 3 * chunk := by omega
    rw [eq0, hmem (hdir 0 (by decide)), hmem (hdir 1 (by decide)), hmem (hdir 2 (by decide))]
    exact hd

end Cslib.Algorithms.WordRAM.ExactTriangle.StreamingFixedPrime
