/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.RecordProduct.QueryValues
public import Complexity.Algorithms.ExactTriangle.PieceBounds

/-!
# Protected original data for a real record consumer

The original arrays, selected record and original interleaved queries all precede the actual
producer heap. These bounds are derived from `Instances.Output` and membership in the existing
finite instance family. A product execution can therefore preserve the actual words needed
by candidate recovery without copying the catalogue or snapshotting its workspace.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.RecordWitness

open Cslib.WordRAM Cslib.Matrix Cslib.Algorithms.ExactTriangle

/-- Read the real selected record and prove every subsequent read is in the protected prefix.
The native program obtains these fields by loads; this theorem only derives their meaning. -/
theorem record_view {n D g p : ℕ} (values : ℕ → ℤ) (initial y : Data 64)
    (h : Instances.Output n D g p values initial y)
    (hD : 16 ≤ D) (hDn : D ≤ n) (hg : 1 ≤ g) (hp : p ≠ 0)
    (idx : InstanceIndex p)
    (hidx : idx ∈ instanceIndices (fun a b : Fin n => values (pairIndex (a, b))) D g p) :
    let ord := RecordProduct.recordOrdinal n D g p values idx
    let base := y.regs Instances.output + ord * (6 + 2 * (n * D))
    let q := RecordProduct.recordQueries n D p idx
    let Q := RecordProduct.recordQueryCount n D p values idx
    5 + 3 * (n * n) ≤ y.regs Instances.heap ∧
      base + 6 ≤ y.regs Instances.heap ∧ q + 2 * Q ≤ y.regs Instances.heap ∧
      idx.2.2 * pieceSize D g ≤ n ∧
      (∀ j : Fin 6, y.mem (base + j.val) =
        ![idx.1.val, idx.2.2, q, Q, base + 6, base + 6 + n * D] j) ∧
      (∀ j < Q, y.mem (q + 2 * j) < n ∧ y.mem (q + 2 * j + 1) < n) ∧
      (∀ j < 5 + 3 * (n * n), y.mem j = initial.mem j) := by
  let wAB := fun a b : Fin n => values (pairIndex (a, b))
  let N := n * n
  let C := fun rho => Nat.count (fun q => (values q % (p : ℤ)).toNat = rho) N
  let H := numPieces n D g
  let K := ChunkCatalogue.before C (queryCap n D) p
  let ord := RecordProduct.recordOrdinal n D g p values idx
  let base := y.regs Instances.output + ord * (6 + 2 * (n * D))
  let q := RecordProduct.recordQueries n D p idx
  let Q := RecordProduct.recordQueryCount n D p values idx
  obtain ⟨hk, hj⟩ := (mem_instanceIndices wAB idx).mp hidx
  have hcard : (residueClass wAB p idx.1).card = C idx.1.val :=
    QuerySpec.card_residueClass wAB hp _ (by intro pair; rfl) idx.1
  have hchunk : idx.2.1 < C idx.1.val ⌈/⌉ queryCap n D := by
    simpa only [numChunks, hcard] using hk
  have hord := ChunkCatalogue.before_add_lt C (queryCap n D) idx.1.isLt hchunk
  have hiCount : ord < K * H := by
    have hh := Nat.mul_le_mul_right H (Nat.succ_le_of_lt hord)
    change (ChunkCatalogue.before C (queryCap n D) idx.1.val + idx.2.1) * H + idx.2.2 < K * H
    change (ChunkCatalogue.before C (queryCap n D) idx.1.val + idx.2.1 + 1) * H ≤ K * H at hh
    change idx.2.2 < H at hj
    rw [Nat.add_mul, Nat.one_mul] at hh
    omega
  have hout : y.regs Instances.output = 5 + 6 * N + p + 2 * N * p + 3 * K := h.2.2.2.1
  have hheap : y.regs Instances.heap = y.regs Instances.output + K * H * (6 + 2 * (n * D)) :=
    h.2.2.2.2.2.1.trans (congrArg (fun v => v + K * H * (6 + 2 * (n * D))) hout.symm)
  have hbase : base + 6 ≤ y.regs Instances.heap := by
    have hh := Nat.mul_le_mul_right (6 + 2 * (n * D)) (Nat.succ_le_of_lt hiCount)
    rw [hheap]
    dsimp only [base]
    nlinarith only [hh]
  have hQ : idx.2.1 * queryCap n D + Q ≤ N := by
    have hc : C idx.1.val ≤ N := Nat.count_le _
    have hpositive := RecordProduct.recordQueryCount_pos values hp (by omega) hDn idx hidx
    change 0 < min (queryCap n D) (C idx.1.val - idx.2.1 * queryCap n D) at hpositive
    dsimp only [Q, RecordProduct.recordQueryCount]
    change idx.2.1 * queryCap n D +
      min (queryCap n D) (C idx.1.val - idx.2.1 * queryCap n D) ≤ N
    omega
  have hqEnd : q + 2 * Q ≤ y.regs Instances.heap := by
    have hrho := Nat.mul_le_mul_right (2 * N) (Nat.succ_le_of_lt idx.1.isLt)
    dsimp only [q, RecordProduct.recordQueries]
    change 5 + 6 * N + p + 2 * idx.1.val * N +
      2 * (idx.2.1 * queryCap n D) + 2 * Q ≤ _
    rw [hheap, hout]
    nlinarith only [hQ, hrho, Nat.zero_le (3 * K),
      Nat.zero_le (K * H * (6 + 2 * (n * D)))]
  have hfirst : idx.2.2 * pieceSize D g ≤ n := by
    have hB := pieceSize_pos hD hg
    by_contra hh
    have hc : numPieces n D g ≤ idx.2.2 := (Nat.ceilDiv_le_iff hB).mpr (by omega)
    change idx.2.2 < numPieces n D g at hj
    omega
  obtain ⟨hdr, -, -⟩ := PreparationSpec.instance_readback values wAB hp
    (by intro a b; rfl) hD hDn hg h idx hidx
  have hcoord := (RecordProduct.output_query_coordinates values wAB hp (by intro a b; rfl)
    (by omega) hDn h idx.1 idx.2.1 hk).1
  rw [hcard] at hcoord
  dsimp only
  refine ⟨?_, hbase, hqEnd, hfirst, ?_, hcoord, ?_⟩
  · rw [hheap, hout]
    dsimp only [N]
    omega
  · simpa only [base, ord, RecordProduct.recordOrdinal, Q, RecordProduct.recordQueryCount,
      q, RecordProduct.recordQueries, hout, N, K, C, hcard, Block.Realizes, Block.read] using hdr
  · intro j hj
    exact h.2.2.2.2.2.2.2.2.2.2.2 j (Or.inl hj)

end Cslib.Algorithms.WordRAM.ExactTriangle.RecordWitness
