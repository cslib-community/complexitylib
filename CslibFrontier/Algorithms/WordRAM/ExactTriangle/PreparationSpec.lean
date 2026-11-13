/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.Instances
public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.QuerySpec
public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.MatrixSpec
import CslibFrontier.Foundations.Data.Nat.Div

/-!
# Exact finite meaning of prepared native instances

The native catalogue enumerates the existing residue classes, chunks and pieces. These results
identify its actual output count and per-instance records with that finite construction. Matrix
meaning and padding reuse `MatrixSpec` and its existing writer-entry formulas.

The [consumer extension](CslibFrontier/Algorithms/WordRAM/ExactTriangle/PreparationAdjacency.html)
connects these cells to finite adjacency, deriving piece coordinates and the padding bound.

## Main results

* `PreparationSpec.count_eq_card`: the actual output counter is the finite instance cardinality.
* `PreparationSpec.index_unique`: unique existing finite coordinates for each output record.
* `PreparationSpec.instance_readback`: exact query slices and matrices at every finite index.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.PreparationSpec

open Cslib.WordRAM Cslib.Algorithms.ExactTriangle Cslib.Matrix

/-- The counter of an actual native output is exactly the existing finite instance count.
The weight-array correspondence concerns only the original A–B input, not supplied classes. -/
theorem count_eq_card {n D g p : ℕ} (values : ℕ → ℤ) (wAB : Fin n → Fin n → ℤ)
    (hp : p ≠ 0) (hAB : ∀ a b, values (Cslib.Matrix.pairIndex (a, b)) = wAB a b)
    {initial y : Data 64} (h : Instances.Output n D g p values initial y) :
    y.regs Instances.produced = (instanceIndices wAB D g p).card := by
  obtain ⟨-, -, -, -, hc, -, -, -, -, -, -, -⟩ := h
  exact hc.trans (QuerySpec.before_mul_numPieces wAB hp
    (fun q => (values q % (p : ℤ)).toNat) (by intro q; rw [hAB]; rfl) D g)

private theorem pieces_pos {n D g : ℕ} (hD : 16 ≤ D) (hDn : D ≤ n) (hg : 1 ≤ g) :
    0 < numPieces n D g := by
  have hcover : n ≤ numPieces n D g * pieceSize D g :=
    Nat.le_ceilDiv_mul (pieceSize_pos hD hg)
  by_contra h
  have hzero : numPieces n D g = 0 := by omega
  rw [hzero, Nat.zero_mul] at hcover
  omega

/-- Every occupied native instance slot has exactly one existing finite class/chunk/piece
index. This uses the standard dependent finite-sum enumeration and ordinary division/remainder;
there is no second definition of a residue class or finite instance. -/
theorem index_unique {n D g p : ℕ} (values : ℕ → ℤ) (wAB : Fin n → Fin n → ℤ)
    (hp : p ≠ 0) (hAB : ∀ a b, values (Cslib.Matrix.pairIndex (a, b)) = wAB a b)
    (hD : 16 ≤ D) (hDn : D ≤ n) (hg : 1 ≤ g) (i : ℕ) :
    let C := fun rho => Nat.count (fun q => (values q % (p : ℤ)).toNat = rho) (n * n)
    let H := numPieces n D g
    i < ChunkCatalogue.before C (queryCap n D) p * H →
      ∃! idx : InstanceIndex p, idx ∈ instanceIndices wAB D g p ∧
        i = (ChunkCatalogue.before C (queryCap n D) idx.residue.val + idx.chunk) * H +
          idx.piece := by
  let C := fun rho => Nat.count (fun q => (values q % (p : ℤ)).toNat = rho) (n * n)
  let H := numPieces n D g
  have hH : 0 < H := pieces_pos hD hDn hg
  have hCount (rho : Fin p) : (residueClass wAB p rho).card = C rho.val :=
    QuerySpec.card_residueClass wAB hp (fun q => (values q % (p : ℤ)).toNat)
      (by intro q; rw [hAB]; rfl) rho
  dsimp only
  intro hi
  change i < ChunkCatalogue.before C (queryCap n D) p * H at hi
  obtain ⟨rc, hrc, huniq⟩ := ChunkCatalogue.before_index C (queryCap n D) p (i / H)
    ((Nat.div_lt_iff_lt_mul hH).mpr hi)
  let out : InstanceIndex p := ⟨rc.1, rc.2.val, i % H⟩
  have hout : out ∈ instanceIndices wAB D g p := by
    rw [mem_instanceIndices]
    refine ⟨?_, Nat.mod_lt _ hH⟩
    change rc.2.val < numChunks (residueClass wAB p rc.1) (queryCap n D)
    rw [numChunks, hCount]
    exact rc.2.isLt
  refine ⟨out, ⟨hout, ?_⟩, ?_⟩
  · change i = (ChunkCatalogue.before C (queryCap n D) rc.1.val + rc.2.val) * H + i % H
    rw [← hrc]
    simpa only [Nat.mul_comm] using (Nat.div_add_mod i H).symm
  · intro other hother
    obtain ⟨hk, hj⟩ := (mem_instanceIndices wAB other).mp hother.1
    have hchunk : other.chunk < C other.residue.val ⌈/⌉ queryCap n D := by
      simpa only [numChunks, hCount] using hk
    let rc' : (rho : Fin p) × Fin (C rho.val ⌈/⌉ queryCap n D) :=
      ⟨other.residue, ⟨other.chunk, hchunk⟩⟩
    have heq : i = (ChunkCatalogue.before C (queryCap n D) other.residue.val + other.chunk) * H +
        other.piece := hother.2
    have hdiv : i / H = ChunkCatalogue.before C (queryCap n D) other.residue.val + other.chunk := by
      rw [heq, Nat.mul_comm _ H, Nat.mul_add_div hH,
        Nat.div_eq_of_lt hj, Nat.add_zero]
    have hmod : i % H = other.piece := by rw [heq, Nat.mul_add_mod_of_lt hj]
    have he : rc' = rc := huniq rc' hdiv
    exact InstanceIndex.ext (congrArg Sigma.fst he) (congrArg (fun q => q.2.val) he) hmod.symm

/-- Each existing finite instance is stored at its computed native ordinal. Its six-word
record contains the exact residue, piece, existing query-chunk pointer/cardinality and both
matrix pointers. The matrix readback reuses the same entry formulas as `MatrixSpec`, including
their modular adjacency and zero-padding results. -/
theorem instance_readback {n D g p : ℕ} (values : ℕ → ℤ) (wAB : Fin n → Fin n → ℤ)
    (hp : p ≠ 0) (hAB : ∀ a b, values (Cslib.Matrix.pairIndex (a, b)) = wAB a b)
    (hD : 16 ≤ D) (hDn : D ≤ n) (hg : 1 ≤ g)
    {initial y : Data 64} (h : Instances.Output n D g p values initial y)
    (idx : InstanceIndex p) (hidx : idx ∈ instanceIndices wAB D g p) :
    let N := n * n
    let R := fun q => (values q % (p : ℤ)).toNat
    let C := fun rho => Nat.count (fun q => R q = rho) N
    let H := numPieces n D g
    let B := pieceSize D g
    let K := ChunkCatalogue.before C (queryCap n D) p
    let ord := ChunkCatalogue.before C (queryCap n D) idx.residue.val + idx.chunk
    let base := 5 + 6 * N + p + 2 * N * p + 3 * K + (ord * H + idx.piece) * (6 + 2 * (n * D))
    let A : WriteMatrices.Args :=
      ⟨5 + 5 * N, base + 6, n, D, p, idx.piece * B, min B (n - idx.piece * B), idx.residue.val⟩
    let A' := { A with src := 5 + 4 * N, dst := base + 6 + n * D }
    (Block.mk base 6).Realizes y.mem
      ![idx.residue.val, idx.piece, 5 + 6 * N + p + 2 * idx.residue.val * N +
        2 * (idx.chunk * queryCap n D),
        min (queryCap n D) ((residueClass wAB p idx.residue).card - idx.chunk * queryCap n D),
        base + 6, base + 6 + n * D] ∧
      (Block.mk A.dst (n * D)).Realizes y.mem
        (fun j => WriteMatrices.entry false A (fun q => R (2 * N + q)) j) ∧
      (Block.mk A'.dst (n * D)).Realizes y.mem
        (fun j => WriteMatrices.entry true A' (fun q => R (N + q)) j) := by
  let N := n * n
  let R := fun q => (values q % (p : ℤ)).toNat
  let C := fun rho => Nat.count (fun q => R q = rho) N
  let H := numPieces n D g
  let K := ChunkCatalogue.before C (queryCap n D) p
  let ord := ChunkCatalogue.before C (queryCap n D) idx.residue.val + idx.chunk
  let i := ord * H + idx.piece
  let desc := 5 + 6 * N + p + 2 * N * p
  have hH : 0 < H := pieces_pos hD hDn hg
  obtain ⟨hk, hj⟩ := (mem_instanceIndices wAB idx).mp hidx
  have hCount : (residueClass wAB p idx.residue).card = C idx.residue.val :=
    QuerySpec.card_residueClass wAB hp R
      (by intro q; dsimp only [R]; rw [hAB]; rfl) idx.residue
  have hchunk : idx.chunk < C idx.residue.val ⌈/⌉ queryCap n D := by
    simpa only [numChunks, hCount] using hk
  have hord : ord < K := ChunkCatalogue.before_add_lt C (queryCap n D) idx.residue.isLt hchunk
  have hbound := Nat.mul_le_mul_right H (Nat.succ_le_of_lt hord)
  rw [Nat.succ_mul] at hbound
  have hi : i < K * H := by dsimp only [i]; omega
  have hdiv : i / H = ord := by dsimp only [i]; exact Nat.mul_add_div_of_lt ord hj
  have hmod : i % H = idx.piece := by dsimp only [i]; exact Nat.mul_add_mod_of_lt hj
  obtain ⟨-, -, -, -, -, -, -, -, -, hdesc, hblocks, -⟩ := h
  have hd := hdesc idx.residue.val idx.residue.isLt idx.chunk hchunk
  have hresidue : y.mem (desc + 3 * ord) = idx.residue.val := hd.1
  have hquery : y.mem (desc + 3 * ord + 1) =
      5 + 6 * N + p + 2 * idx.residue.val * N + 2 * (idx.chunk * queryCap n D) := hd.2.1
  have hcount : y.mem (desc + 3 * ord + 2) =
      min (queryCap n D) ((residueClass wAB p idx.residue).card - idx.chunk * queryCap n D) := by
    rw [hCount]
    exact hd.2.2
  obtain ⟨hr, hL, hR⟩ := hblocks i hi
  dsimp only at hr hL hR
  rw [hdiv, hmod, hresidue, hquery, hcount] at hr
  rw [hdiv, hmod, hresidue] at hL hR
  exact ⟨hr, hL, hR⟩

end Cslib.Algorithms.WordRAM.ExactTriangle.PreparationSpec
