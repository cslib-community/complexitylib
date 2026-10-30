/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.RecordProduct.ProducerQueries

/-!
# Applying the adapter to the actual native producer

The record, source pointers, original zero/one matrices and ordered coordinate occurrences
are derived from `Instances.Output` and the existing native readback theorems. The initialized
client obtains that output from the actual producer execution, not from an algorithm oracle.
Prime selection, global parameters and the outer ExactTriangle host are separate components.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.RecordProduct

open Cslib.WordRAM Cslib.Algorithms.ExactTriangle Cslib.Matrix
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage

/-- The unchanged complete producer occupies the original low register bank. -/
@[expose] def producerBank (i : Fin 64) : Fin 320 := i.castLE (by decide)

/-- Existing native writer arguments, with pointer fields omitted from the value-only view. -/
@[expose] def matrixArgs (n D g p rho piece : ℕ) : WriteMatrices.Args :=
  ⟨0, 0, n, D, p, piece * pieceSize D g,
    min (pieceSize D g) (n - piece * pieceSize D g), rho⟩

/-- Exact raw left adjacency matrix written by the actual producer. -/
@[expose] def leftMatrix (m n g p : ℕ) (values : ℕ → ℤ) (idx : InstanceIndex p) :
    Matrix (Fin n) (Fin (D m)) ℤ := fun a k =>
  (WriteMatrices.entry false (matrixArgs n (D m) g p idx.1.val idx.2.2)
    (fun q => (values (2 * (n * n) + q) % (p : ℤ)).toNat) (a.val * D m + k.val) : ℤ)

/-- Exact raw right adjacency matrix, in its actual `D×n` storage order. -/
@[expose] def rightMatrix (m n g p : ℕ) (values : ℕ → ℤ) (idx : InstanceIndex p) :
    Matrix (Fin (D m)) (Fin n) ℤ := fun k a =>
  (WriteMatrices.entry true (matrixArgs n (D m) g p idx.1.val idx.2.2)
    (fun q => (values (n * n + q) % (p : ℤ)).toNat) (k.val * n + a.val) : ℤ)

/-- The readback matrices satisfy the raw callee's original-entry hypotheses. -/
theorem matrices_zero_one (m n g p : ℕ) (values : ℕ → ℤ) (idx : InstanceIndex p) :
    (∀ a k, 0 ≤ leftMatrix m n g p values idx a k ∧
      leftMatrix m n g p values idx a k ≤ 1) ∧
    (∀ k a, 0 ≤ rightMatrix m n g p values idx k a ∧
      rightMatrix m n g p values idx k a ≤ 1) := by
  constructor <;> intro a k
  · exact ⟨Int.natCast_nonneg _, by
      dsimp only [leftMatrix]
      exact_mod_cast WriteMatrices.entry_le_one false _ _ _⟩
  · exact ⟨Int.natCast_nonneg _, by
      dsimp only [rightMatrix]
      exact_mod_cast WriteMatrices.entry_le_one true _ _ _⟩

/-- The actual computed ordinal of an existing finite class/chunk/piece. This is a value
specification for the caller's selection register, not a table supplied to the adapter. -/
@[expose] def recordOrdinal (n D g p : ℕ) (values : ℕ → ℤ) (idx : InstanceIndex p) : ℕ :=
  let C := fun rho => Nat.count (fun q => (values q % (p : ℤ)).toNat = rho) (n * n)
  (ChunkCatalogue.before C (queryCap n D) idx.1.val + idx.2.1) * numPieces n D g + idx.2.2

/-- Actual descriptor occurrence count, rather than an assumed sparse set size. -/
@[expose] def recordQueryCount (n D p : ℕ) (values : ℕ → ℤ) (idx : InstanceIndex p) : ℕ :=
  min (queryCap n D)
    (Nat.count (fun q => (values q % (p : ℤ)).toNat = idx.1.val) (n * n) -
      idx.2.1 * queryCap n D)

/-- Every occupied finite instance has a nonempty actual descriptor query slice. -/
theorem recordQueryCount_pos {n D g p : ℕ} (values : ℕ → ℤ) (hp : p ≠ 0)
    (hD : 1 ≤ D) (hDn : D ≤ n) (idx : InstanceIndex p)
    (hidx : idx ∈ instanceIndices (fun a b : Fin n => values (pairIndex (a, b))) D g p) :
    0 < recordQueryCount n D p values idx := by
  let wAB := fun a b : Fin n => values (pairIndex (a, b))
  let R := fun q => (values q % (p : ℤ)).toNat
  have hk := ((mem_instanceIndices wAB idx).mp hidx).1
  have hcard := QuerySpec.card_residueClass wAB hp R (by intro q; rfl) idx.1
  have hcap : 0 < queryCap n D := one_le_queryCap hD hDn
  have hkcard : idx.2.1 * queryCap n D < (residueClass wAB p idx.1).card := by
    by_contra h
    have hc := (Nat.ceilDiv_le_iff hcap).mpr
      (by omega : (residueClass wAB p idx.1).card ≤ idx.2.1 * queryCap n D)
    change idx.2.1 < (residueClass wAB p idx.1).card ⌈/⌉ queryCap n D at hk
    omega
  rw [hcard] at hkcard
  unfold recordQueryCount
  change 0 < min (queryCap n D) (Nat.count (fun q => R q = idx.1.val) (n * n) -
    idx.2.1 * queryCap n D)
  omega

/-- Actual query pointer into the protected producer catalogue. -/
@[expose] def recordQueries (n D p : ℕ) (idx : InstanceIndex p) : ℕ :=
  5 + 6 * (n * n) + p + 2 * idx.1.val * (n * n) + 2 * (idx.2.1 * queryCap n D)

-- The composed readback contains nested finite writer-argument structures and vector fields.
set_option maxRecDepth 4096 in
/-- Full adapter execution over a genuine producer output. Every descriptor and source-span
premise of `exec` is derived here from the actual output; none remains an independent caller
certificate. A following initialized client obtains this output by executing the producer. -/
theorem exec_of_output {W m n g p : ℕ} (values : ℕ → ℤ)
    (initial : Data 64) (x : Data 320)
    (h : Instances.Output n (D m) g p values initial (x.comap producerBank))
    (hD : 16 ≤ D m) (hg : 1 ≤ g) (hp : p ≠ 0) (hN : D m ^ 18 ≤ n)
    (hheaderD : initial.mem 1 = D m) (hheaderN : initial.mem 3 = n)
    (idx : InstanceIndex p)
    (hidx : idx ∈ instanceIndices (fun a b : Fin n => values (pairIndex (a, b))) (D m) g p)
    (hi : x.regs Reg.ordinal = recordOrdinal n (D m) g p values idx)
    (hfit : Fits W (2 * x.regs 42 +
      4 * CallableProduct.windowSize n (recordQueryCount n (D m) p values idx) + 1024)) :
    let hn : 0 < n := lt_of_lt_of_le (by omega : 0 < D m)
      ((Nat.le_self_pow (by decide : 18 ≠ 0) (D m)).trans hN)
    let qs := decodedQueries hn x.mem (recordQueries n (D m) p idx)
      (recordQueryCount n (D m) p values idx)
    ∃ y, ExecWithin W program x y (timeBound (m := m) qs) ∧
      y.regs Reg.result = x.regs 42 + QueriedProduct.outputBase (19 * m) m n qs.length ∧
      (∀ j : Fin qs.length,
        y.mem (x.regs 42 + (QueriedProduct.outputBase (19 * m) m n qs.length + j.val)) =
          Signed.encode ((leftMatrix m n g p values idx * rightMatrix m n g p values idx)
            (qs.get j).1 (qs.get j).2)) ∧
      (∀ a, a < x.regs 42 ∨ x.regs 42 + CallableProduct.windowSize n qs.length ≤ a →
        y.mem a = x.mem a) ∧
      (∀ j : Fin 320, j.val < 65 → y.regs j = x.regs j) ∧
      qs.length * 2 ^ m ≤ n ^ 2 := by
  let wAB := fun a b : Fin n => values (pairIndex (a, b))
  let N := n * n
  let R := fun q => (values q % (p : ℤ)).toNat
  let C := fun rho => Nat.count (fun q => R q = rho) N
  let H := numPieces n (D m) g
  let K := ChunkCatalogue.before C (queryCap n (D m)) p
  let out := 5 + 6 * N + p + 2 * N * p + 3 * K
  let ord := recordOrdinal n (D m) g p values idx
  let recordBase := out + ord * (6 + 2 * (n * D m))
  let q := recordQueries n (D m) p idx
  let Q := recordQueryCount n (D m) p values idx
  have hDn : D m ≤ n := (Nat.le_self_pow (by decide : 18 ≠ 0) (D m)).trans hN
  have hn : 0 < n := lt_of_lt_of_le (by omega) hDn
  let qs := decodedQueries hn x.mem q Q
  have hlen : qs.length = Q := decodedQueries_length hn x.mem q Q
  obtain ⟨hk, hj⟩ := (mem_instanceIndices wAB idx).mp hidx
  have hcard : (residueClass wAB p idx.1).card = C idx.1.val :=
    QuerySpec.card_residueClass wAB hp R (by intro pair; rfl) idx.1
  have hchunk : idx.2.1 < C idx.1.val ⌈/⌉ queryCap n (D m) := by
    simpa only [numChunks, hcard] using hk
  have hord := ChunkCatalogue.before_add_lt C (queryCap n (D m)) idx.1.isLt hchunk
  have hiCount : ord < K * H := by
    have hh := Nat.mul_le_mul_right H (Nat.succ_le_of_lt hord)
    change (ChunkCatalogue.before C (queryCap n (D m)) idx.1.val + idx.2.1) * H +
      idx.2.2 < K * H
    change (ChunkCatalogue.before C (queryCap n (D m)) idx.1.val + idx.2.1 + 1) * H ≤
      K * H at hh
    change idx.2.2 < H at hj
    rw [Nat.add_mul, Nat.one_mul] at hh
    omega
  have hfull := h
  obtain ⟨yn, yD, yp, yo, yc, yb, yres, ycnt, yscan, ydesc, yblocks, yframe⟩ := h
  change x.regs 39 = out at yo
  change x.regs 42 = out + (K * H) * (6 + 2 * (n * D m)) at yb
  have hrecEnd : recordBase + 6 + 2 * (n * D m) ≤ x.regs 42 := by
    have ht := Nat.mul_le_mul_right (6 + 2 * (n * D m)) (Nat.succ_le_of_lt hiCount)
    dsimp only [recordBase]
    rw [yb]
    nlinarith only [ht]
  have hcap : 0 < queryCap n (D m) := one_le_queryCap (by omega) hDn
  have hkcard : idx.2.1 * queryCap n (D m) < C idx.1.val := by
    have hpositive := recordQueryCount_pos values hp (by omega) hDn idx hidx
    change 0 < min (queryCap n (D m)) (C idx.1.val - idx.2.1 * queryCap n (D m)) at hpositive
    omega
  have hQ : idx.2.1 * queryCap n (D m) + Q ≤ N := by
    have hc : C idx.1.val ≤ N := Nat.count_le _
    dsimp only [Q, recordQueryCount]
    change idx.2.1 * queryCap n (D m) +
      min (queryCap n (D m)) (C idx.1.val - idx.2.1 * queryCap n (D m)) ≤ N
    omega
  have hqEnd : q + 2 * Q ≤ x.regs 42 := by
    have hrho := Nat.mul_le_mul_right (2 * N) (Nat.succ_le_of_lt idx.1.isLt)
    dsimp only [q, recordQueries]
    change 5 + 6 * N + p + 2 * idx.1.val * N + 2 * (idx.2.1 * queryCap n (D m)) +
      2 * Q ≤ _
    rw [yb]
    dsimp only [out]
    nlinarith only [hQ, hrho, Nat.zero_le (3 * K),
      Nat.zero_le (K * H * (6 + 2 * (n * D m)))]
  obtain ⟨hdr, hleft, hright⟩ := PreparationSpec.instance_readback values wAB hp
    (by intro a b; rfl) hD hDn hg hfull idx hidx
  have hcoord := (output_query_coordinates values wAB hp (by intro a b; rfl)
    (by omega) hDn hfull idx.1 idx.2.1 hk).1
  rw [hcard] at hcoord
  have hc : ∀ j < Q, x.mem (q + 2 * j) < n ∧ x.mem (q + 2 * j + 1) < n := hcoord
  have hvalues := matrices_zero_one m n g p values idx
  obtain ⟨y, hy, yr, yv, yf, yg⟩ := exec (b := x.regs 42) (i := ord) (out := out)
    (rho := idx.1.val) (piece := idx.2.2) (s := recordBase + 6)
    (t := recordBase + 6 + n * D m) (q := q) (leftMatrix m n g p values idx)
    (rightMatrix m n g p values idx) qs x
    ((yframe 1 (Or.inl (by omega))).trans hheaderD)
    ((yframe 3 (Or.inl (by omega))).trans hheaderN) hi yo rfl
    (by change recordBase + 6 ≤ _; omega)
    (by simpa only [hlen, hcard, recordBase, out, ord, recordOrdinal, C, R, N, K, Q,
      recordQueryCount, q, recordQueries, Data.comap_mem] using hdr)
    (by omega) (by omega)
    (by simpa only [hlen] using hqEnd)
    (raw_left_words x.mem _ _ qs (by
      intro a k
      have hflat : a.val * D m + k.val < n * D m := by
        have ht := Nat.mul_le_mul_right (D m) a.isLt
        rw [Nat.succ_mul] at ht
        have := k.isLt
        omega
      simpa +decide only [leftMatrix, matrixArgs, WriteMatrices.entry, Int.toNat_natCast,
        Block.read, Data.comap_mem, recordBase, out, ord, recordOrdinal, K, C, R, N] using
        hleft ⟨a.val * D m + k.val, hflat⟩))
    (raw_right_words hn x.mem _ _ qs (by
      intro k a
      have hflat : k.val * n + a.val < n * D m := by
        have ht := Nat.mul_le_mul_right n k.isLt
        rw [Nat.succ_mul, Nat.mul_comm (D m) n] at ht
        have := a.isLt
        omega
      simpa only [rightMatrix, matrixArgs, WriteMatrices.entry, Int.toNat_natCast,
        Block.read, Data.comap_mem, recordBase, out, ord, recordOrdinal, K, C, R, N] using
        hright ⟨k.val * n + a.val, hflat⟩))
    (by simpa only [hlen] using decodedQueries_words hn x.mem _ _ hc)
    hvalues.1 hvalues.2 hN (by simpa only [hlen] using hfit)
  refine ⟨y, hy, yr, yv, yf, yg, ?_⟩
  rw [hlen]
  exact (Nat.mul_le_mul_right (2 ^ m) (min_le_left _ _)).trans (queryCap_mul_two_pow_le n m)

end Cslib.Algorithms.WordRAM.ExactTriangle.RecordProduct
