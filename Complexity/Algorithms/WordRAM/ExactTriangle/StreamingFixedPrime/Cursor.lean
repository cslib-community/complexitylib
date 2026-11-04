/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.RecordProduct.QuerySpan

/-!
# Logical instance cursor independent of physical storage

The native metadata records the computed catalogue and matrix geometry. The logical progress
counter and heap pointer are deliberately separate: a visit increments both, and a charged
reset restores only the heap. This assertion does not describe any materialized record.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.StreamingFixedPrime

open Cslib.WordRAM Cslib.Algorithms.ExactTriangle

/-- Stable metadata shared by consecutive physical-slot visits. Neither the logical counter
nor the heap is fixed by this predicate. -/
structure Cursor (n D g p : ℕ) (values : ℕ → ℤ) (x : Data 64) : Prop where
  size : x.regs Instances.size = n
  dimension : x.regs Instances.dimension = D
  modulus : x.regs Instances.modulus = p
  pieceLength : x.regs Instances.pieceLength = pieceSize D g
  pieces : x.regs Instances.pieces = numPieces n D g
  chunks : x.regs Instances.chunks = ChunkCatalogue.before
    (fun rho => Nat.count (fun q => (values q % (p : ℤ)).toNat = rho) (n * n))
    (queryCap n D) p
  descriptors : x.regs Instances.descriptors = 5 + 6 * (n * n) + p + 2 * (n * n) * p
  output : x.regs Instances.output = 5 + 6 * (n * n) + p + 2 * (n * n) * p +
    3 * x.regs Instances.chunks
  total : x.regs Instances.total = x.regs Instances.chunks * x.regs Instances.pieces
  stride : x.regs Instances.stride = 6 + 2 * (n * D)
  one : x.regs Instances.one = 1
  three : x.regs Instances.three = 3
  srcLeft : x.regs Instances.srcLeft = 5 + 5 * (n * n)
  srcRight : x.regs Instances.srcRight = 5 + 4 * (n * n)

/-- Stable metadata is retained by any change confined outside its native register bank,
and by the two progressing counters. -/
theorem Cursor.transfer {n D g p : ℕ} {values : ℕ → ℤ} {x y : Data 64}
    (h : Cursor n D g p values x)
    (hr : ∀ j : Fin 64, 32 ≤ j.val → j.val < 50 → j ≠ Instances.produced →
      j ≠ Instances.heap → y.regs j = x.regs j) : Cursor n D g p values y := by
  have same (j : Fin 64)
      (hj : 32 ≤ j.val ∧ j.val < 50 ∧ j ≠ Instances.heap ∧ j ≠ Instances.produced) :
      y.regs j = x.regs j := hr j hj.1 hj.2.1 hj.2.2.2 hj.2.2.1
  exact ⟨(same _ (by decide)).trans h.size, (same _ (by decide)).trans h.dimension,
    (same _ (by decide)).trans h.modulus, (same _ (by decide)).trans h.pieceLength,
    (same _ (by decide)).trans h.pieces, (same _ (by decide)).trans h.chunks,
    (same _ (by decide)).trans h.descriptors,
    by rw [same Instances.output (by decide), same Instances.chunks (by decide)]; exact h.output,
    by rw [same Instances.total (by decide), same Instances.chunks (by decide),
      same Instances.pieces (by decide)]; exact h.total,
    (same _ (by decide)).trans h.stride, (same _ (by decide)).trans h.one,
    (same _ (by decide)).trans h.three, (same _ (by decide)).trans h.srcLeft,
    (same _ (by decide)).trans h.srcRight⟩

/-- The existing charged writer advances logical identity and allocation without changing
any stable cursor metadata. It need not preserve earlier physical records. -/
theorem Cursor.after_visit {w T n D g p : ℕ} {values : ℕ → ℤ} {x y : Data 64}
    (h : Cursor n D g p values x) (he : ExecWithin w Instances.visit x y T) :
    Cursor n D g p values y :=
  h.transfer fun j hj hj' hprod hheap =>
    he.regs_eq (Instances.visit_preserves j ⟨hj, hj', hheap, hprod⟩)

end Cslib.Algorithms.WordRAM.ExactTriangle.StreamingFixedPrime
