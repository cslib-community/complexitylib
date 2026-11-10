/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.RecordWitness.AfterProduct
public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.RecordProduct.Producer

/-!
# The real product followed by candidate verification

The general caller selects any occupied record. The actual product is executed on its whole
renamed 320-register bank; the consumer then reads its real answers and protected query words.
The original signed arrays and caller catalogue remain untouched. The initialized entry derives
the numerical premises from original input, rather than supplying an intermediate run contract.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.RecordWitness

open Cslib.WordRAM Cslib.Matrix Cslib.Algorithms.ExactTriangle
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage

/-- Execute the actual product and verifier from one genuine producer output. No product
execution, accepted-pair list, witness or time certificate is a hypothesis. -/
theorem exec_of_output {w U m n g p : ℕ} (values : ℕ → ℤ)
    (AB BC AC : ℕ → ℕ → ℤ) (initial : Data 64) (x : Data 400)
    (h : Instances.Output n (D m) g p values initial
      ((x.comap productBank).comap RecordProduct.producerBank))
    (hD : 16 ≤ D m) (hg : 1 ≤ g) (hp : p ≠ 0) (hN : D m ^ 18 ≤ n)
    (hheaderD : initial.mem 1 = D m) (hheaderG : initial.mem 2 = g)
    (hheaderN : initial.mem 3 = n)
    (idx : InstanceIndex p)
    (hidx : idx ∈ instanceIndices (fun a b : Fin n => values (pairIndex (a, b))) (D m) g p)
    (hi : x.regs (productBank RecordProduct.Reg.ordinal) =
      RecordProduct.recordOrdinal n (D m) g p values idx)
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
        QueriedProduct.outputBase (19 * m) m n
          (RecordProduct.recordQueryCount n (D m) p values idx) +
        4 * RecordProduct.recordQueryCount n (D m) p values idx + 4 * D m +
        2 * (n * D m) + 9 * (n * n) + 4 * n + g + 4096)) :
    let hn : 0 < n := lt_of_lt_of_le (by omega : 0 < D m)
      ((Nat.le_self_pow (by decide : 18 ≠ 0) (D m)).trans hN)
    let q := RecordProduct.recordQueries n (D m) p idx
    let Q := RecordProduct.recordQueryCount n (D m) p values idx
    let qs := RecordProduct.decodedQueries hn x.mem q Q
    let first := idx.2.2 * pieceSize (D m) g
    let length := min (pieceSize (D m) g) (n - first)
    ∃ y S, ExecWithin (w + 2) program x y
        (RecordProduct.timeBound (m := m) qs + 5 * Nat.sqrt (D m) + 8 * Q +
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
  apply RecordWitness.exec_after_product values AB BC AC initial x h hD hg hp hN
    hheaderD hheaderG hheaderN idx hidx hi hmem hmag hU
    RecordProduct.program _ (QueriedProduct.outputBase (19 * m) m n
      (RecordProduct.recordQueryCount n (D m) p values idx)) ?_ hfit
  obtain ⟨r, hr, rr, rv, rm, rg, -⟩ := RecordProduct.exec_of_output values initial
    (x.comap productBank) h hD hg hp hN hheaderD hheaderN idx hidx hi
    (hfit.of_le (by
      change 2 * x.regs (productBank 42) +
        4 * CallableProduct.windowSize n
          (RecordProduct.recordQueryCount n (D m) p values idx) + 1024 ≤ _
      omega))
  refine ⟨r, hr, ?_, ?_, ?_, rg⟩
  · simpa only [RecordProduct.decodedQueries_length, Data.comap_regs] using rr
  · simpa only [RecordProduct.decodedQueries_length, Data.comap_regs, Data.comap_mem,
      Nat.add_assoc] using rv
  · simpa only [RecordProduct.decodedQueries_length, Data.comap_regs, Data.comap_mem] using rm

end Cslib.Algorithms.WordRAM.ExactTriangle.RecordWitness
