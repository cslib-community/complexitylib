/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.Instances

/-!
# Prepared catalogue readback after workspace reuse

Every catalogue, query, record and matrix word described by `Instances.Output` lies below its
heap boundary. A consumer may change the workspace above that boundary while preserving all
those words and the producer registers. The readback contract can then be framed against the
current state. This does not assert that the producer ran again, or that its original external
frame survived: the original producer execution and its initial state remain separate facts.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.Instances

open Cslib.WordRAM Cslib.Algorithms.ExactTriangle

/-- Transport the actual prepared readback through changes above the heap. The new frame is
relative to the current state, not to the original producer input. No execution is asserted. -/
theorem Output.reframe {n D g p : ℕ} (values : ℕ → ℤ) {initial y z : Data 64}
    (h : Output n D g p values initial y) (hregs : z.regs = y.regs)
    (hmem : Set.EqOn z.mem y.mem (Set.Iio (y.regs heap))) :
    Output n D g p values z z := by
  let N := n * n
  let R := fun q => (values q % (p : ℤ)).toNat
  let C := fun rho => Nat.count (fun q => R q = rho) N
  let K := ChunkCatalogue.before C (queryCap n D) p
  let H := numPieces n D g
  let B := pieceSize D g
  let desc := 5 + 6 * N + p + 2 * N * p
  let out := desc + 3 * K
  let stop := out + (K * H) * (6 + 2 * (n * D))
  obtain ⟨hn, hD, hp, ho, hc, hh, hr, hcounts, hqueries, hdesc, hblocks, -⟩ := h
  change y.regs heap = stop at hh
  have mem_eq (a : ℕ) (ha : a < stop) : z.mem a = y.mem a :=
    hmem (by simpa only [Set.mem_Iio, hh] using ha)
  have hdescOut : desc ≤ out := by dsimp only [out]; omega
  have houtStop : out ≤ stop := Nat.le_add_right _ _
  have desc_lt (i : ℕ) (hi : i < K) : desc + 3 * i + 2 < stop := by
    have hm := Nat.mul_le_mul_left 3 (Nat.succ_le_of_lt hi)
    rw [Nat.mul_succ] at hm
    dsimp only [out] at houtStop
    omega
  refine ⟨hregs ▸ hn, hregs ▸ hD, hregs ▸ hp, hregs ▸ ho, hregs ▸ hc,
    hregs ▸ hh, ?_, ?_, ?_, ?_, ?_, fun _ _ => rfl⟩
  · intro q hq
    rw [mem_eq _ (by dsimp only [stop, out, desc]; omega)]
    exact hr q hq
  · intro rho hrho
    rw [mem_eq _ (by dsimp only [stop, out, desc]; omega)]
    exact hcounts rho hrho
  · intro rho hrho q hq he
    have hcount : Nat.count (fun k => R k = rho) q ≤ q := Nat.count_le _
    have hm := Nat.mul_le_mul_left (2 * N) (Nat.succ_le_of_lt hrho)
    rw [Nat.mul_succ] at hm
    have hbound : 5 + 6 * N + p + 2 * N * rho +
        2 * Nat.count (fun k => R k = rho) q + 1 < stop := by
      dsimp only [stop, out, desc]
      omega
    rw [mem_eq (5 + 6 * N + p + 2 * N * rho +
        2 * Nat.count (fun k => R k = rho) q) (by omega),
      mem_eq _ hbound]
    exact hqueries rho hrho q hq he
  · intro rho hrho k hk
    have hi := ChunkCatalogue.before_add_lt C (queryCap n D) hrho hk
    have hb := desc_lt (ChunkCatalogue.before C (queryCap n D) rho + k) hi
    rw [mem_eq (desc + 3 * (ChunkCatalogue.before C (queryCap n D) rho + k))
        (by omega),
      mem_eq (desc + 3 * (ChunkCatalogue.before C (queryCap n D) rho + k) + 1)
        (by omega), mem_eq _ hb]
    exact hdesc rho hrho k hk
  · intro i hi
    change i < K * H at hi
    have hH : 0 < H := by
      by_contra hzero
      have hz : H = 0 := by omega
      rw [hz, Nat.mul_zero] at hi
      omega
    have hchunk : i / H < K := (Nat.div_lt_iff_lt_mul hH).mpr hi
    have hd := desc_lt (i / H) hchunk
    have hm := Nat.mul_le_mul_right (6 + 2 * (n * D)) (Nat.succ_le_of_lt hi)
    rw [Nat.succ_mul] at hm
    have hb : out + i * (6 + 2 * (n * D)) + (6 + 2 * (n * D)) ≤ stop := by
      dsimp only [stop]
      omega
    obtain ⟨hrecord, hleft, hright⟩ := hblocks i hi
    dsimp only
    rw [mem_eq _ (by omega : desc + 3 * (i / H) < stop),
      mem_eq _ (by omega : desc + 3 * (i / H) + 1 < stop), mem_eq _ hd]
    refine ⟨?_, ?_, ?_⟩
    · intro j
      change z.mem (out + i * (6 + 2 * (n * D)) + j.val) = _
      rw [mem_eq _ (by have hj : j.val < 6 := j.isLt; omega)]
      exact hrecord j
    · intro j
      change z.mem (out + i * (6 + 2 * (n * D)) + 6 + j.val) = _
      rw [mem_eq _ (by have hj : j.val < n * D := j.isLt; omega)]
      exact hleft j
    · intro j
      change z.mem (out + i * (6 + 2 * (n * D)) + 6 + n * D + j.val) = _
      rw [mem_eq _ (by have hj : j.val < n * D := j.isLt; omega)]
      exact hright j

end Cslib.Algorithms.WordRAM.ExactTriangle.Instances
