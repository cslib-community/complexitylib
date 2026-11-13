/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.StreamingFixedPrime.Cursor
public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.RecordWitness.Readback
import CslibFrontier.Foundations.Data.Nat.Div

/-!
# Actual record readback after one-slot production

The current residue arrays and selected catalogue descriptor suffice to execute a logical
visit. The new record and both matrices are obtained from the charged native visit at the
current physical heap. No all-record producer Output is a premise or asserted for this state.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.StreamingFixedPrime

open Cslib.WordRAM Cslib.Matrix Cslib.Algorithms.ExactTriangle

-- The proof unfolds only finite delivered argument records and their six descriptor words.
set_option maxRecDepth 4096 in
/-- Write one logical instance at the fixed physical slot from an arbitrary dirty state.
The destination is exactly one six-word descriptor followed by two raw matrices. The frame
protects the shared queries and original weights for every later piece and prime pass. -/
theorem exec_construct {w n D g p : ℕ} (values : ℕ → ℤ)
    (x : Data 64) (hD : 16 ≤ D) (hg : 1 ≤ g) (hp : p ≠ 0)
    (cursor : Cursor n D g p values x)
    (hheap : x.regs Instances.heap = x.regs Instances.output)
    (idx : InstanceIndex p)
    (hidx : idx ∈ instanceIndices (fun u v : Fin n => values (pairIndex (u, v))) D g p)
    (hi : x.regs Instances.produced = RecordProduct.recordOrdinal n D g p values idx)
    (hresidues : ∀ k < 3 * (n * n), x.mem (5 + 3 * (n * n) + k) =
      (values k % (p : ℤ)).toNat)
    (hdescriptor :
      let C := fun rho => Nat.count (fun k => (values k % (p : ℤ)).toNat = rho) (n * n)
      let chunk := ChunkCatalogue.before C (queryCap n D) idx.residue.val + idx.chunk
      x.mem (chunk * 3 + x.regs Instances.descriptors) = idx.residue.val ∧
      x.mem (chunk * 3 + x.regs Instances.descriptors + 1) =
        RecordProduct.recordQueries n D p idx ∧
      x.mem (chunk * 3 + x.regs Instances.descriptors + 2) =
        RecordProduct.recordQueryCount n D p values idx)
    (hfit : Fits w (x.regs Instances.heap + x.regs Instances.stride +
      x.regs Instances.srcLeft + x.regs Instances.srcRight + 2 * (n * n) + 2 * p +
      x.regs Instances.descriptors + 3 * x.regs Instances.chunks + n +
      x.regs Instances.pieces + x.regs Instances.pieces * x.regs Instances.pieceLength +
      x.regs Instances.produced + 16)) :
    let out := x.regs Instances.output
    let q := RecordProduct.recordQueries n D p idx
    let Q := RecordProduct.recordQueryCount n D p values idx
    ∃ y, ExecWithin w Instances.visit x y (40 * (n * D) + 66) ∧
      Cursor n D g p values y ∧ y.regs Instances.produced = x.regs Instances.produced + 1 ∧
      y.regs Instances.heap = out + (6 + 2 * (n * D)) ∧
      (Block.mk out 6).Realizes y.mem
        ![idx.residue.val, idx.piece, q, Q, out + 6, out + 6 + n * D] ∧
      (Block.mk (out + 6) (n * D)).Realizes y.mem (fun j =>
        WriteMatrices.entry false (RecordProduct.matrixArgs n D g p idx.residue.val idx.piece)
          (fun k => (values (2 * (n * n) + k) % (p : ℤ)).toNat) j.val) ∧
      (Block.mk (out + 6 + n * D) (n * D)).Realizes y.mem (fun j =>
        WriteMatrices.entry true (RecordProduct.matrixArgs n D g p idx.residue.val idx.piece)
          (fun k => (values (n * n + k) % (p : ℤ)).toNat) j.val) ∧
      (∀ u, u < out ∨ out + (6 + 2 * (n * D)) ≤ u → y.mem u = x.mem u) := by
  let N := n * n
  let R := fun k => (values k % (p : ℤ)).toNat
  let C := fun rho => Nat.count (fun k => R k = rho) N
  let H := numPieces n D g
  let K := ChunkCatalogue.before C (queryCap n D) p
  let chunk := ChunkCatalogue.before C (queryCap n D) idx.residue.val + idx.chunk
  let desc := 5 + 6 * N + p + 2 * N * p
  let out := x.regs Instances.output
  obtain ⟨hk, hj⟩ := (mem_instanceIndices _ idx).mp hidx
  have hH : 0 < H := lt_of_le_of_lt (Nat.zero_le _) hj
  have hcard : (residueClass (fun u v : Fin n => values (pairIndex (u, v))) p idx.residue).card =
      C idx.residue.val := QuerySpec.card_residueClass _ hp R (by intro pair; rfl) idx.residue
  have hk' : idx.chunk < C idx.residue.val ⌈/⌉ queryCap n D := by
    simpa only [numChunks, hcard] using hk
  have hchunk : chunk < K :=
    ChunkCatalogue.before_add_lt C (queryCap n D) idx.residue.isLt hk'
  have hdiv : x.regs Instances.produced / x.regs Instances.pieces = chunk := by
    rw [hi, cursor.pieces]
    exact Nat.mul_add_div_of_lt chunk hj
  have hmod : x.regs Instances.produced % x.regs Instances.pieces = idx.piece := by
    rw [hi, cursor.pieces]
    exact Nat.mul_add_mod_of_lt hj
  have hdesc :
      x.mem (chunk * 3 + x.regs Instances.descriptors) = idx.residue.val ∧
      x.mem (chunk * 3 + x.regs Instances.descriptors + 1) =
        RecordProduct.recordQueries n D p idx ∧
      x.mem (chunk * 3 + x.regs Instances.descriptors + 2) =
        RecordProduct.recordQueryCount n D p values idx := hdescriptor
  have hfirst : idx.piece * pieceSize D g ≤ n := (piece_start_lt hD hg hj).le
  have hres (k : ℕ) : R k < p := Int.natMod_lt hp
  have hleft (j : ℕ) (hj : j < N) : x.mem (x.regs Instances.srcLeft + j) = R (2 * N + j) := by
    rw [cursor.srcLeft]
    convert hresidues (2 * N + j) (by omega) using 1
    congr 1
    omega
  have hright (j : ℕ) (hj : j < N) : x.mem (x.regs Instances.srcRight + j) = R (N + j) := by
    rw [cursor.srcRight]
    convert hresidues (N + j) (by omega) using 1
    congr 1
    omega
  obtain ⟨y, he, yi, yh, hdr, hl, hr, frame⟩ := Instances.exec_visit x
    (fun k => R (2 * N + k)) (fun k => R (N + k)) cursor.one cursor.three
    (by rw [cursor.pieces]; exact hH)
    (by rw [hi, cursor.chunks, cursor.pieces]
        change chunk * H + idx.piece < K * H
        have hm := Nat.mul_le_mul_right H (Nat.succ_le_of_lt hchunk)
        rw [Nat.succ_mul] at hm
        omega)
    (by rw [cursor.stride, cursor.size, cursor.dimension])
    (by rw [hmod, cursor.pieceLength, cursor.size]; exact hfirst)
    (by rw [hdiv, hdesc.1, cursor.modulus]; exact idx.residue.isLt)
    (by rw [cursor.modulus]; exact fun k _ => hres _)
    (by rw [cursor.modulus]; exact fun k _ => hres _)
    (by simpa only [cursor.size] using hleft)
    (by simpa only [cursor.size] using hright)
    (by rw [cursor.srcLeft, cursor.size, hheap, cursor.output]; omega)
    (by rw [cursor.srcRight, cursor.size, hheap, cursor.output]; omega)
    (by simpa only [cursor.size, cursor.dimension, cursor.modulus] using hfit)
  rw [cursor.size, cursor.dimension] at he hl hr
  have argsL : InstancePair.leftArgs (Instances.pairInput x) =
      { RecordProduct.matrixArgs n D g p idx.residue.val idx.piece with
        src := x.regs Instances.srcLeft, dst := out + 6 } := by
    simp +decide [InstancePair.leftArgs, Instances.pairInput, RecordProduct.matrixArgs,
      cursor.size, cursor.dimension, cursor.modulus, cursor.pieceLength,
      hmod, hdiv, hdesc.1, hheap, out,
      InstancePair.srcLeft, InstancePair.base, InstancePair.size, InstancePair.dimension,
      InstancePair.modulus, InstancePair.first, InstancePair.length, InstancePair.rho]
  have argsR : InstancePair.rightArgs (Instances.pairInput x) =
      { RecordProduct.matrixArgs n D g p idx.residue.val idx.piece with
        src := x.regs Instances.srcRight, dst := out + 6 + n * D } := by
    unfold InstancePair.rightArgs
    rw [argsL]
    simp +decide [Instances.pairInput, hheap, out, cursor.size, cursor.dimension,
      InstancePair.srcRight, InstancePair.base, InstancePair.size, InstancePair.dimension]
  refine ⟨y, he, cursor.after_visit he, yi, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hheap, cursor.stride] using yh
  · rw [InstancePair.recordWords, argsL, argsR] at hdr
    rw [hheap] at hdr
    simpa +decide [Instances.pairInput,
      hmod, hdiv, hdesc.1, hdesc.2.1, hdesc.2.2, InstancePair.rho, InstancePair.piece,
      InstancePair.queries, InstancePair.count, hheap, out] using hdr
  · rw [argsL] at hl
    exact hl
  · rw [argsR] at hr
    exact hr
  · intro u hu
    exact frame u (by rw [hheap, cursor.stride]; omega)

end Cslib.Algorithms.WordRAM.ExactTriangle.StreamingFixedPrime
