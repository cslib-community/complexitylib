/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.RecordWitness.AfterRecordProduct
public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.BoxRecordWitness.Program
public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.RecordBoxProduct.Exec
import CslibFrontier.Algorithms.WordRAM.ExactTriangle.RecordProduct.Readback

/-!
# The real box product followed by candidate verification

A physical descriptor, its query span and its raw matrix pair suffice for the complete box
backend and original-weight verifier. The physical ordinal and logical chunk/piece index are
independent. This boundary requires no all-record producer `Output` and permits dirty scratch;
the standalone producer-output specialization is in `BoxRecordWitness.Exec`.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.BoxRecordWitness

open RecordWitness

open Cslib.WordRAM Cslib.Matrix Cslib.Algorithms.ExactTriangle
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage

/-- Execute the complete box backend and original-weight verifier at an arbitrary physical
record ordinal. Only this descriptor and matrix pair are required; the logical index still
identifies the original chunk, piece and ordered query occurrences. Scratch may be dirty. -/
theorem exec_at_record {w U m n g p i : ℕ} (values : ℕ → ℤ)
    (AB BC AC : ℕ → ℕ → ℤ) (x : Data 400)
    (hD : 16 ≤ D m) (hN : D m ^ 18 ≤ n)
    (hheaderD : x.mem 1 = D m) (hheaderG : x.mem 2 = g)
    (hheaderN : x.mem 3 = n)
    (idx : InstanceIndex p)
    (hi : x.regs (productBank RecordProduct.Reg.ordinal) = i)
    (hview :
      let heap := x.regs (productBank 42)
      let base := x.regs (productBank (RecordProduct.producerBank Instances.output)) +
        i * (6 + 2 * (n * D m))
      let q := RecordProduct.recordQueries n (D m) p idx
      let Q := RecordProduct.recordQueryCount n (D m) p values idx
      5 + 3 * (n * n) ≤ heap ∧ base + 6 ≤ heap ∧ q + 2 * Q ≤ heap ∧
        idx.piece * pieceSize (D m) g ≤ n ∧
        (∀ j : Fin 6, x.mem (base + j.val) =
          ![idx.residue.val, idx.piece, q, Q, base + 6, base + 6 + n * D m] j) ∧
        (∀ j < Q, x.mem (q + 2 * j) < n ∧ x.mem (q + 2 * j + 1) < n))
    (hspan : x.regs (productBank 39) + i * (6 + 2 * (n * D m)) +
      6 + 2 * (n * D m) ≤ x.regs (productBank 42))
    (hleft :
      let base := x.regs (productBank 39) + i * (6 + 2 * (n * D m))
      (Block.mk (base + 6) (n * D m)).Realizes x.mem (fun j =>
        WriteMatrices.entry false (RecordProduct.matrixArgs n (D m) g p idx.residue.val idx.piece)
          (fun q => (values (2 * (n * n) + q) % (p : ℤ)).toNat) j.val))
    (hright :
      let base := x.regs (productBank 39) + i * (6 + 2 * (n * D m))
      (Block.mk (base + 6 + n * D m) (n * D m)).Realizes x.mem (fun j =>
        WriteMatrices.entry true (RecordProduct.matrixArgs n (D m) g p idx.residue.val idx.piece)
          (fun q => (values (n * n + q) % (p : ℤ)).toNat) j.val))
    (hmem : ∀ a < n, ∀ b < n,
      x.mem (5 + (a * n + b)) = Signed.encode (AB a b) ∧
      x.mem (5 + n * n + (a * n + b)) = Signed.encode (BC a b) ∧
      x.mem (5 + n * n + n * n + (a * n + b)) = Signed.encode (AC a b))
    (hmag : ∀ a < n, ∀ b < n,
      (AB a b).natAbs ≤ U ∧ (BC a b).natAbs ≤ U ∧ (AC a b).natAbs ≤ U)
    (hU : GenericRAM.Signed.Fits w (2 * U : ℕ))
    (hfit : Fits (w + 2)
      (4 * x.regs (productBank 42) +
        4 * CallableProduct.windowSize n (RecordProduct.recordQueryCount n (D m) p values idx) +
        QueriedProduct.outputBase (21 * m) m n
          (RecordProduct.recordQueryCount n (D m) p values idx) +
        4 * RecordProduct.recordQueryCount n (D m) p values idx + 4 * D m +
        2 * (n * D m) + 9 * (n * n) + 4 * n + g + 4096)) :
    let hn : 0 < n := lt_of_lt_of_le (by omega : 0 < D m)
      ((Nat.le_self_pow (by decide : 18 ≠ 0) (D m)).trans hN)
    let q := RecordProduct.recordQueries n (D m) p idx
    let Q := RecordProduct.recordQueryCount n (D m) p values idx
    let qs := RecordProduct.decodedQueries hn x.mem q Q
    let first := idx.piece * pieceSize (D m) g
    let length := min (pieceSize (D m) g) (n - first)
    ∃ y S, ExecWithin (w + 2) program x y
        (RecordBoxProduct.timeBound (m := m) qs + 5 * Nat.sqrt (D m) + 8 * Q +
          (42 * length + 28) * S + 52) ∧
      y.regs Reg.scans = S ∧ (y.regs Reg.found = 0 ∨ y.regs Reg.found = 1) ∧
      S ≤ Nat.count (fun j => y.mem (y.regs (productBank RecordProduct.Reg.result) + j) ≠ 0 ∧
        ∀ c : Fin length,
          AB (x.mem (q + 2 * j)) (x.mem (q + 2 * j + 1)) +
            BC (x.mem (q + 2 * j + 1)) (first + c.val) +
            AC (x.mem (q + 2 * j)) (first + c.val) ≠ 0) Q + y.regs Reg.found ∧
      (y.regs Reg.found = 1 ↔ ∃ j < Q,
        y.mem (y.regs (productBank RecordProduct.Reg.result) + j) ≠ 0 ∧
        ∃ c, first ≤ c ∧ c < first + length ∧
          AB (x.mem (q + 2 * j)) (x.mem (q + 2 * j + 1)) +
            BC (x.mem (q + 2 * j + 1)) c + AC (x.mem (q + 2 * j)) c = 0) ∧
      (∀ j : Fin qs.length,
        y.mem (y.regs (productBank RecordProduct.Reg.result) + j.val) = Signed.encode
          ((RecordProduct.leftMatrix m n g p values idx *
            RecordProduct.rightMatrix m n g p values idx) (qs.get j).1 (qs.get j).2)) ∧
      (y.regs Reg.found = 1 →
        y.regs Reg.witnessA < n ∧ y.regs Reg.witnessB < n ∧
        first ≤ y.regs Reg.witnessC ∧ y.regs Reg.witnessC < first + length ∧
        AB (y.regs Reg.witnessA) (y.regs Reg.witnessB) +
          BC (y.regs Reg.witnessB) (y.regs Reg.witnessC) +
          AC (y.regs Reg.witnessA) (y.regs Reg.witnessC) = 0 ∧
        ∃ j < Q, y.regs Reg.witnessA = x.mem (q + 2 * j) ∧
          y.regs Reg.witnessB = x.mem (q + 2 * j + 1)) ∧
      (∀ u, u < x.regs (productBank 42) ∨
        x.regs (productBank 42) + CallableProduct.windowSize n Q ≤ u → y.mem u = x.mem u) ∧
      (∀ j : Fin 320, j.val < 65 → y.regs (productBank j) = x.regs (productBank j)) := by
  apply RecordWitness.exec_after_record_product values AB BC AC x hD hN
    hheaderD hheaderG hheaderN idx hi hview hmem hmag hU
    RecordBoxProduct.program _ (QueriedProduct.outputBase (21 * m) m n
      (RecordProduct.recordQueryCount n (D m) p values idx)) ?_ hfit
  let hn : 0 < n := lt_of_lt_of_le (by omega : 0 < D m)
    ((Nat.le_self_pow (by decide : 18 ≠ 0) (D m)).trans hN)
  let base := x.regs (productBank 39) + i * (6 + 2 * (n * D m))
  let q := RecordProduct.recordQueries n (D m) p idx
  let Q := RecordProduct.recordQueryCount n (D m) p values idx
  let qs := RecordProduct.decodedQueries hn x.mem q Q
  obtain ⟨_, hrec, hq, _, hdr, hcoords⟩ := hview
  have hbank : RecordProduct.producerBank Instances.output = (39 : Fin 320) := by decide
  rw [hbank] at hdr
  have hlen : qs.length = Q := RecordProduct.decodedQueries_length hn x.mem q Q
  have hl := RecordProduct.raw_left_block values idx x.mem qs hleft
  have hr := RecordProduct.raw_right_block hn values idx x.mem qs hright
  obtain ⟨r, he, rr, rv, rm, rg⟩ := RecordBoxProduct.exec
    (b := x.regs (productBank 42)) (i := i) (out := x.regs (productBank 39))
    (rho := idx.residue.val) (piece := idx.piece)
    (RecordProduct.leftMatrix m n g p values idx)
    (RecordProduct.rightMatrix m n g p values idx) qs (x.comap productBank)
    hheaderD hheaderN hi rfl rfl hrec
    (by simpa only [hlen, Block.Realizes, Block.read, Data.comap_mem, Q] using hdr)
    (by omega)
    (by omega)
    (by simpa only [hlen] using hq) hl hr
    (by simpa only [hlen, qs, Q, q, Data.comap_mem] using
      (RecordProduct.decodedQueries_words hn x.mem
      (RecordProduct.leftMatrix m n g p values idx)
      (RecordProduct.rightMatrix m n g p values idx) hcoords))
    (RecordProduct.matrices_zero_one m n g p values idx).1
    (RecordProduct.matrices_zero_one m n g p values idx).2 hN
    (hfit.of_le (by simp only [hlen, Q]; omega))
  refine ⟨r, he, ?_, ?_, ?_, rg⟩
  · simpa only [hlen] using rr
  · simpa only [hlen, Nat.add_assoc] using rv
  · simpa only [hlen, Q, Data.comap_mem] using rm

end Cslib.Algorithms.WordRAM.ExactTriangle.BoxRecordWitness
