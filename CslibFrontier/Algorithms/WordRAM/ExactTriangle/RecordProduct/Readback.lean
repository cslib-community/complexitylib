/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.RecordProduct.RecordData

/-!
# Pure source-span readback for either record product

`producer_readback` derives the six-word record descriptor, raw left and right zero/one matrix
spans, ordered query-coordinate words, heap bounds and occurrence sparsity from a genuine
`Instances.Output`, without importing or executing either per-record product backend.
`raw_left_block` and `raw_right_block` read a record's realized raw matrix blocks as the ordinary
product's original input; `producer_readback` and the box record caller both use them.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.RecordProduct

open Cslib.WordRAM Cslib.Algorithms.ExactTriangle Cslib.Matrix
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage

/-- A record's raw left block, as written by the producer, reads as the original left input of the
ordinary queried product. -/
theorem raw_left_block {m n g p s : ℕ} (values : ℕ → ℤ) (idx : InstanceIndex p)
    (mem : ℕ → ℕ) (qs : List (Fin n × Fin n))
    (hleft : (Block.mk s (n * D m)).Realizes mem (fun j =>
      WriteMatrices.entry false (matrixArgs n (D m) g p idx.1.val idx.2.2)
        (fun q => (values (2 * (n * n) + q) % (p : ℤ)).toNat) j)) :
    ∀ a < n * D m, mem (s + a) =
      (State.init (QueriedProduct.input true (19 * m)
        (leftMatrix m n g p values idx) (rightMatrix m n g p values idx) qs) :
          State 160).data.mem (5 + a) := by
  refine raw_left_words mem _ _ qs fun a k => ?_
  have hflat : a.val * D m + k.val < n * D m := by
    rw [Nat.mul_comm a.val]
    exact Nat.mul_add_lt_mul_of_lt_of_lt a.isLt k.isLt
  simpa only [leftMatrix, Int.toNat_natCast, Block.Realizes, Block.read] using hleft ⟨_, hflat⟩

/-- A record's raw right block, in its `D×n` storage order, reads as the original right input of
the ordinary queried product. -/
theorem raw_right_block {m n g p t : ℕ} (hn : 0 < n) (values : ℕ → ℤ) (idx : InstanceIndex p)
    (mem : ℕ → ℕ) (qs : List (Fin n × Fin n))
    (hright : (Block.mk t (n * D m)).Realizes mem (fun j =>
      WriteMatrices.entry true (matrixArgs n (D m) g p idx.1.val idx.2.2)
        (fun q => (values (n * n + q) % (p : ℤ)).toNat) j)) :
    ∀ a < n * D m, mem (t + a) =
      (State.init (QueriedProduct.input true (19 * m)
        (leftMatrix m n g p values idx) (rightMatrix m n g p values idx) qs) :
          State 160).data.mem (5 + n * D m + a) := by
  refine raw_right_words hn mem _ _ qs fun k a => ?_
  have hflat : k.val * n + a.val < n * D m := by
    rw [Nat.mul_comm k.val, Nat.mul_comm n (D m)]
    exact Nat.mul_add_lt_mul_of_lt_of_lt k.isLt a.isLt
  simpa only [rightMatrix, Int.toNat_natCast, Block.Realizes, Block.read] using hright ⟨_, hflat⟩

/-- Derive both raw source matrices, ordered coordinate words, protected spans and occurrence
sparsity from genuine producer output, without invoking either product backend. -/
theorem producer_readback {m n g p : ℕ} (values : ℕ → ℤ)
    (initial : Data 64) (x : Data 320)
    (h : Instances.Output n (D m) g p values initial (x.comap producerBank))
    (hD : 16 ≤ D m) (hg : 1 ≤ g) (hp : p ≠ 0) (hN : D m ^ 18 ≤ n)
    (hheaderD : initial.mem 1 = D m) (hheaderN : initial.mem 3 = n)
    (idx : InstanceIndex p)
    (hidx : idx ∈ instanceIndices (fun a b : Fin n => values (pairIndex (a, b))) (D m) g p) :
    let hn : 0 < n := lt_of_lt_of_le (by omega : 0 < D m)
      ((Nat.le_self_pow (by decide : 18 ≠ 0) (D m)).trans hN)
    let ord := recordOrdinal n (D m) g p values idx
    let base := x.regs 39 + ord * (6 + 2 * (n * D m))
    let q := recordQueries n (D m) p idx
    let qs := decodedQueries hn x.mem q (recordQueryCount n (D m) p values idx)
    x.mem 1 = D m ∧ x.mem 3 = n ∧
      base + 6 ≤ x.regs 42 ∧
      (Block.mk base 6).Realizes x.mem
        ![idx.1.val, idx.2.2, q, qs.length, base + 6, base + 6 + n * D m] ∧
      base + 6 + n * D m ≤ x.regs 42 ∧
      base + 6 + n * D m + n * D m ≤ x.regs 42 ∧
      q + 2 * qs.length ≤ x.regs 42 ∧
      (∀ a < n * D m, x.mem (base + 6 + a) =
        (State.init (QueriedProduct.input true (19 * m)
          (leftMatrix m n g p values idx) (rightMatrix m n g p values idx) qs) :
            State 160).data.mem (5 + a)) ∧
      (∀ a < n * D m, x.mem (base + 6 + n * D m + a) =
        (State.init (QueriedProduct.input true (19 * m)
          (leftMatrix m n g p values idx) (rightMatrix m n g p values idx) qs) :
            State 160).data.mem (5 + n * D m + a)) ∧
      (∀ a < 2 * qs.length, x.mem (q + a) =
        (State.init (QueriedProduct.input true (19 * m)
          (leftMatrix m n g p values idx) (rightMatrix m n g p values idx) qs) :
            State 160).data.mem (5 + 2 * (n * D m) + a)) ∧
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
  dsimp only
  rw [yo]
  refine ⟨(yframe 1 (Or.inl (by omega))).trans hheaderD,
    (yframe 3 (Or.inl (by omega))).trans hheaderN,
    (by change recordBase + 6 ≤ _; omega),
    (by simpa only [decodedQueries_length, hcard, recordBase, out, ord, recordOrdinal,
      C, R, N, K, Q,
      recordQueryCount, q, recordQueries, Data.comap_mem] using hdr),
    (by change recordBase + 6 + n * D m ≤ _; omega),
    (by change recordBase + 6 + n * D m + n * D m ≤ _; omega),
    (by simpa only [decodedQueries_length] using hqEnd),
    raw_left_block values idx x.mem qs hleft,
    raw_right_block hn values idx x.mem qs hright,
    (by simpa only [decodedQueries_length] using decodedQueries_words hn x.mem _ _ hc), ?_⟩
  rw [decodedQueries_length]
  exact (Nat.mul_le_mul_right (2 ^ m) (min_le_left _ _)).trans (queryCap_mul_two_pow_le n m)

end Cslib.Algorithms.WordRAM.ExactTriangle.RecordProduct
