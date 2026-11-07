/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.StreamingFixedPrime.Cursor

/-!
# One-slot construction retains original input admission

The original all-record budget also bounds a visit at the reusable slot. No intermediate
allocation or fit certificate is added to the initialized solver's input contract.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.StreamingFixedPrime

open Cslib.WordRAM Cslib.Algorithms.ExactTriangle

/-- A guarded slot visit needs no greater arithmetic/address budget than standalone production. -/
theorem Cursor.visit_budget_le {n D g p : ℕ} {values : ℕ → ℤ} {x : Data 64}
    (h : Cursor n D g p values x) (hD : 16 ≤ D) (hDn : D ≤ n) (hg : 1 ≤ g)
    (hh : x.regs Instances.heap = x.regs Instances.output)
    (hi : x.regs Instances.produced < x.regs Instances.total) :
    x.regs Instances.heap + x.regs Instances.stride + x.regs Instances.srcLeft +
      x.regs Instances.srcRight + 2 * (n * n) + 2 * p + x.regs Instances.descriptors +
      3 * x.regs Instances.chunks + n + x.regs Instances.pieces +
      x.regs Instances.pieces * x.regs Instances.pieceLength + x.regs Instances.produced + 16 ≤
        Instances.budget n D g p := by
  let N := n * n
  let K := x.regs Instances.chunks
  let H := x.regs Instances.pieces
  let B := x.regs Instances.pieceLength
  let S := 6 + 2 * (n * D)
  let out := x.regs Instances.output
  have hK : K ≤ p * N := by
    dsimp only [K]
    rw [h.chunks]
    exact ChunkCatalogue.before_le (one_le_queryCap (by omega) hDn)
      (fun _ _ => Nat.count_le _) le_rfl
  have hBn : B ≤ n := by
    dsimp only [B]
    rw [h.pieceLength]
    exact (pieceSize_le_sOf hg).trans ((Nat.sqrt_le_self D).trans hDn)
  have hHn : H ≤ n := by
    dsimp only [H]
    rw [h.pieces]
    exact (Nat.ceilDiv_le_iff (pieceSize_pos hD hg)).mpr
      (Nat.le_mul_of_pos_right n (pieceSize_pos hD hg))
  have hHB : H * B ≤ N := Nat.mul_le_mul hHn hBn
  have htotal : x.regs Instances.total = K * H := h.total
  have hpos : 1 ≤ K * H := by omega
  have hS : S ≤ K * H * S := by simpa only [Nat.one_mul] using Nat.mul_le_mul_right S hpos
  have bound := Instances.budget_covers_loop (D := D) (g := g) hK hHn hHB
  have hout : out = 5 + 6 * N + p + 2 * N * p + 3 * K := h.output
  rw [hh, h.stride, h.srcLeft, h.srcRight, h.descriptors]
  change out + S + (5 + 5 * N) + (5 + 4 * N) + 2 * N + 2 * p +
    (5 + 6 * N + p + 2 * N * p) + 3 * K + n + H + H * B + x.regs Instances.produced + 16 ≤ _
  calc
    _ = 2 * out + S + 11 * N + 2 * p + n + H + H * B + x.regs Instances.produced + 26 := by
      rw [hout]
      ring
    _ ≤ 2 * out + K * H * S + 11 * N + 2 * p + n + H + H * B + K * H + 26 := by omega
    _ ≤ _ := by
      rw [hout]
      exact bound

end Cslib.Algorithms.WordRAM.ExactTriangle.StreamingFixedPrime
