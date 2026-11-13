/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.RecordBoxProduct.Exec
public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.RecordProduct.Readback

/-!
# Box products from genuine native producer outputs

The complete descriptor, original zero/one matrix blocks, coordinate spans and
occurrence sparsity are derived from the actual `Instances.Output`. The selected
record invokes the new compiled box product and retains the producer catalogue.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.RecordBoxProduct

open Cslib.WordRAM Cslib.Algorithms.ExactTriangle Cslib.Matrix
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage
open RecordProduct

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
      y.regs Reg.result = x.regs 42 + QueriedProduct.outputBase (21 * m) m n qs.length ∧
      (∀ j : Fin qs.length,
        y.mem (x.regs 42 + (QueriedProduct.outputBase (21 * m) m n qs.length + j.val)) =
          Signed.encode ((leftMatrix m n g p values idx * rightMatrix m n g p values idx)
            (qs.get j).1 (qs.get j).2)) ∧
      (∀ a, a < x.regs 42 ∨ x.regs 42 + CallableProduct.windowSize n qs.length ≤ a →
        y.mem a = x.mem a) ∧
      (∀ j : Fin 320, j.val < 65 → y.regs j = x.regs j) ∧
      qs.length * 2 ^ m ≤ n ^ 2 := by
  obtain ⟨hDmem, hnmem, hrec, hdr, hs, ht, hq, hl, hr, hqs, hQ⟩ :=
    producer_readback values initial x h hD hg hp hN hheaderD hheaderN idx hidx
  obtain ⟨y, hy, yr, yv, yf, yg⟩ := exec (b := x.regs 42)
    (i := recordOrdinal n (D m) g p values idx) (out := x.regs 39)
    (rho := idx.residue.val) (piece := idx.piece)
    (leftMatrix m n g p values idx) (rightMatrix m n g p values idx) _ x
    hDmem hnmem hi rfl rfl hrec hdr hs ht hq hl hr hqs
    (matrices_zero_one m n g p values idx).1
    (matrices_zero_one m n g p values idx).2 hN
    (by simpa only [decodedQueries_length] using hfit)
  exact ⟨y, hy, yr, yv, yf, yg, hQ⟩

end Cslib.Algorithms.WordRAM.ExactTriangle.RecordBoxProduct
