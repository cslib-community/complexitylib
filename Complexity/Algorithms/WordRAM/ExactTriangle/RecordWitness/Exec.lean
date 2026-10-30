/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.RecordWitness.Consume
public import Complexity.Algorithms.WordRAM.ExactTriangle.RecordWitness.Readback

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

private theorem productBank_injective : Function.Injective productBank := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 400 => k.val) h)

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
  let x' := x.comap productBank
  let produced := x'.comap RecordProduct.producerBank
  let heap := x.regs (productBank 42)
  let q := RecordProduct.recordQueries n (D m) p idx
  let Q := RecordProduct.recordQueryCount n (D m) p values idx
  let ord := RecordProduct.recordOrdinal n (D m) g p values idx
  let base := x.regs (productBank (RecordProduct.producerBank Instances.output)) +
    ord * (6 + 2 * (n * D m))
  let out := heap + QueriedProduct.outputBase (19 * m) m n Q
  change Fits (w + 2) (4 * heap + 4 * CallableProduct.windowSize n Q +
    QueriedProduct.outputBase (19 * m) m n Q + 4 * Q + 4 * D m +
    2 * (n * D m) + 9 * (n * n) + 4 * n + g + 4096) at hfit
  have hDn : D m ≤ n := (Nat.le_self_pow (by decide : 18 ≠ 0) (D m)).trans hN
  have hn : 0 < n := lt_of_lt_of_le (by omega) hDn
  let qs := RecordProduct.decodedQueries hn x.mem q Q
  have hlen : qs.length = Q := RecordProduct.decodedQueries_length hn x.mem q Q
  obtain ⟨hinputEnd, hrec, hq, hfirst, hv, hcoords, hprefix⟩ :=
    record_view values initial produced h hD hDn hg hp idx hidx
  change 5 + 3 * (n * n) ≤ heap at hinputEnd
  change base + 6 ≤ heap at hrec
  change q + 2 * Q ≤ heap at hq
  change ∀ j : Fin 6, x.mem (base + j.val) =
    ![idx.1.val, idx.2.2, q, Q, base + 6, base + 6 + n * D m] j at hv
  change ∀ j < Q, x.mem (q + 2 * j) < n ∧ x.mem (q + 2 * j + 1) < n at hcoords
  change ∀ j < 5 + 3 * (n * n), x.mem j = initial.mem j at hprefix
  obtain ⟨r, hr, rr, rvalues, rmem, rregs, -⟩ := RecordProduct.exec_of_output values
    initial x' h hD hg hp hN hheaderD hheaderN idx hidx hi (hfit.of_le (by
      change 2 * heap + 4 * CallableProduct.windowSize n Q + 1024 ≤ _
      omega))
  change r.regs RecordProduct.Reg.result =
    heap + QueriedProduct.outputBase (19 * m) m n qs.length at rr
  change ∀ j : Fin qs.length,
    r.mem (heap + (QueriedProduct.outputBase (19 * m) m n qs.length + j.val)) =
      Signed.encode ((RecordProduct.leftMatrix m n g p values idx *
        RecordProduct.rightMatrix m n g p values idx) (qs.get j).1 (qs.get j).2) at rvalues
  simp only [RecordProduct.decodedQueries_length] at rmem
  change ∀ u, u < heap ∨ heap + CallableProduct.windowSize n Q ≤ u →
    r.mem u = x.mem u at rmem
  let s := r.extend productBank x
  have hs : ExecWithin (w + 2) (RecordProduct.program.rename productBank) x s
      (RecordProduct.timeBound (m := m) qs) := hr.rename productBank_injective
  have sr (j : Fin 320) : s.regs (productBank j) = r.regs j :=
    productBank_injective.extend_apply _ _ j
  have sm (u : ℕ) (hu : u < heap) : s.mem u = x.mem u := rmem u (Or.inl hu)
  have snative (j : Fin 320) (hj : j.val < 65) :
      s.regs (productBank j) = x.regs (productBank j) := (sr j).trans (rregs j hj)
  have sout : s.regs (productBank RecordProduct.Reg.result) = out := by
    simpa only [out, hlen] using (sr RecordProduct.Reg.result).trans rr
  let v : Fin 6 → ℕ := ![idx.1.val, idx.2.2, q, Q, base + 6, base + 6 + n * D m]
  have hread (j : Fin 6) : s.mem (base + j.val) = v j :=
    (sm _ (by have := j.isLt; omega)).trans (hv j)
  have hquery : ∀ j < Q, s.mem (q + 2 * j) = x.mem (q + 2 * j) ∧
      s.mem (q + 2 * j + 1) = x.mem (q + 2 * j + 1) ∧
      x.mem (q + 2 * j) < n ∧ x.mem (q + 2 * j + 1) < n := by
    intro j hj
    exact ⟨sm _ (by omega), sm _ (by omega), hcoords j hj⟩
  have smem : ∀ a < n, ∀ b < n,
      s.mem (5 + (a * n + b)) = Signed.encode (AB a b) ∧
      s.mem (5 + n * n + (a * n + b)) = Signed.encode (BC a b) ∧
      s.mem (5 + n * n + n * n + (a * n + b)) = Signed.encode (AC a b) := by
    intro a ha b hb
    have hn := Nat.mul_le_mul_right n (Nat.succ_le_of_lt ha)
    rw [Nat.succ_mul] at hn
    simpa only [sm _ (by omega : 5 + (a * n + b) < heap),
      sm _ (by omega : 5 + n * n + (a * n + b) < heap),
      sm _ (by omega : 5 + n * n + n * n + (a * n + b) < heap)] using hmem a ha b hb
  obtain ⟨y, S, he, ym, ys, hS, yf, yiff, yw, frame⟩ := exec_consume AB BC AC
    (fun j => x.mem (q + 2 * j)) (fun j => x.mem (q + 2 * j + 1)) s v
    ((sm 1 (by omega)).trans ((hprefix 1 (by omega)).trans hheaderD))
    ((sm 2 (by omega)).trans ((hprefix 2 (by omega)).trans hheaderG))
    ((sm 3 (by omega)).trans ((hprefix 3 (by omega)).trans hheaderN))
    ((snative _ (by decide)).trans hi) (snative _ (by decide)) sout hrec hread hfirst
    hquery smem hmag hU (hfit.of_le (by
      change heap + out + q + 4 * Q + 4 * D m + 2 * (n * D m) +
        9 * (n * n) + 4 * n + g + 2048 ≤ _
      dsimp only [out]
      omega))
  change ExecWithin (w + 2) consume s y
    (5 * Nat.sqrt (D m) + 8 * Q +
      (42 * min (pieceSize (D m) g) (n - idx.2.2 * pieceSize (D m) g) + 28) * S + 52) at he
  change S ≤ Nat.count (fun j => s.mem (out + j) ≠ 0 ∧
    ∀ c : Fin (min (pieceSize (D m) g) (n - idx.2.2 * pieceSize (D m) g)),
      AB (x.mem (q + 2 * j)) (x.mem (q + 2 * j + 1)) +
        BC (x.mem (q + 2 * j + 1)) (idx.2.2 * pieceSize (D m) g + c.val) +
        AC (x.mem (q + 2 * j)) (idx.2.2 * pieceSize (D m) g + c.val) ≠ 0) Q + y.regs Reg.found at hS
  simp_rw [show v 1 = idx.2.2 from rfl, show v 3 = Q from rfl] at yiff
  have hexe : ExecWithin (w + 2) program x y
      (RecordProduct.timeBound (m := m) qs + 5 * Nat.sqrt (D m) + 8 * Q +
        (42 * min (pieceSize (D m) g) (n - idx.2.2 * pieceSize (D m) g) + 28) * S + 52) :=
    (hs.seq he).mono (by omega)
  refine ⟨y, S, hexe, ys, yf, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [ym, frame (productBank RecordProduct.Reg.result) (by decide), sout] using hS
  · simpa only [ym, frame (productBank RecordProduct.Reg.result) (by decide), sout] using yiff
  · intro j
    have hv := rvalues j
    rw [frame _ (by decide), sout, ym]
    change r.mem (out + j.val) = _
    simpa only [out, hlen, Nat.add_assoc] using hv
  · intro hy
    obtain ⟨j, hj, -, hwa, hwb, hlo, hhi, hz⟩ := yw hy
    obtain ⟨ha, hb⟩ := hcoords j hj
    exact ⟨by simpa only [hwa] using ha, by simpa only [hwb] using hb,
      hlo, hhi, by simpa only [hwa, hwb] using hz, j, hj, hwa, hwb⟩
  · intro u hu
    rw [ym]
    exact rmem u hu
  · intro j hj
    exact (frame _ (by change j.val < 320; omega)).trans (snative j hj)

end Cslib.Algorithms.WordRAM.ExactTriangle.RecordWitness
