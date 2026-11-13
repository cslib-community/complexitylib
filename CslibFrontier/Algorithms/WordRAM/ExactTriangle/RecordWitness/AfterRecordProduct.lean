/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.RecordWitness.Consume
public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.RecordProduct.RecordData

/-!
# Physical record composition with candidate verification

The physical ordinal is independent of the logical chunk/piece index. Only the selected
descriptor, original arrays and query span must survive the product; no all-record producer
output is required. This permits immediate consumption of a record in a reused slot.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.RecordWitness

open Cslib.WordRAM Cslib.Matrix Cslib.Algorithms.ExactTriangle
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage

private theorem productBank_injective : Function.Injective productBank := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 400 => k.val) h)

/-- Compose a proved product execution with the real consumer. The actual result offset,
exact signed answers, outside-window frame and producer registers are the only product
postconditions used. The selected physical descriptor need not retain any other record.
Concrete callers discharge the product premise with their actual programs. -/
theorem exec_after_record_product {w U m n g p i : ℕ} (values : ℕ → ℤ)
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
    (hmem : ∀ a < n, ∀ b < n,
      x.mem (5 + (a * n + b)) = Signed.encode (AB a b) ∧
      x.mem (5 + n * n + (a * n + b)) = Signed.encode (BC a b) ∧
      x.mem (5 + n * n + n * n + (a * n + b)) = Signed.encode (AC a b))
    (hmag : ∀ a < n, ∀ b < n,
      (AB a b).natAbs ≤ U ∧ (BC a b).natAbs ≤ U ∧ (AC a b).natAbs ≤ U)
    (hU : GenericRAM.Signed.Fits w (2 * U : ℕ))
    (product : Code .standard 320) (T offset : ℕ)
    (hproduct :
      let hn : 0 < n := lt_of_lt_of_le (by omega : 0 < D m)
        ((Nat.le_self_pow (by decide : 18 ≠ 0) (D m)).trans hN)
      let q := RecordProduct.recordQueries n (D m) p idx
      let Q := RecordProduct.recordQueryCount n (D m) p values idx
      let qs := RecordProduct.decodedQueries hn x.mem q Q
      ∃ r : Data 320,
        ExecWithin (w + 2) product (x.comap productBank) r T ∧
        r.regs RecordProduct.Reg.result = x.regs (productBank 42) + offset ∧
        (∀ j : Fin qs.length,
          r.mem (x.regs (productBank 42) + offset + j.val) = Signed.encode
            ((RecordProduct.leftMatrix m n g p values idx *
              RecordProduct.rightMatrix m n g p values idx) (qs.get j).1 (qs.get j).2)) ∧
        (∀ u, u < x.regs (productBank 42) ∨
          x.regs (productBank 42) + CallableProduct.windowSize n Q ≤ u →
          r.mem u = x.mem u) ∧
        (∀ j : Fin 320, j.val < 65 → r.regs j = x.regs (productBank j)))
    (hfit : Fits (w + 2)
      (4 * x.regs (productBank 42) +
        4 * CallableProduct.windowSize n (RecordProduct.recordQueryCount n (D m) p values idx) +
        offset +
        4 * RecordProduct.recordQueryCount n (D m) p values idx + 4 * D m +
        2 * (n * D m) + 9 * (n * n) + 4 * n + g + 4096)) :
    let hn : 0 < n := lt_of_lt_of_le (by omega : 0 < D m)
      ((Nat.le_self_pow (by decide : 18 ≠ 0) (D m)).trans hN)
    let q := RecordProduct.recordQueries n (D m) p idx
    let Q := RecordProduct.recordQueryCount n (D m) p values idx
    let qs := RecordProduct.decodedQueries hn x.mem q Q
    let first := idx.piece * pieceSize (D m) g
    let length := min (pieceSize (D m) g) (n - first)
    ∃ y S, ExecWithin (w + 2) (.seq (product.rename productBank) consume) x y
        (T + 5 * Nat.sqrt (D m) + 8 * Q +
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
  let heap := x.regs (productBank 42)
  let q := RecordProduct.recordQueries n (D m) p idx
  let Q := RecordProduct.recordQueryCount n (D m) p values idx
  let base := x.regs (productBank (RecordProduct.producerBank Instances.output)) +
    i * (6 + 2 * (n * D m))
  let out := heap + offset
  change Fits (w + 2) (4 * heap + 4 * CallableProduct.windowSize n Q +
    offset + 4 * Q + 4 * D m +
    2 * (n * D m) + 9 * (n * n) + 4 * n + g + 4096) at hfit
  have hDn : D m ≤ n := (Nat.le_self_pow (by decide : 18 ≠ 0) (D m)).trans hN
  have hn : 0 < n := lt_of_lt_of_le (by omega) hDn
  let qs := RecordProduct.decodedQueries hn x.mem q Q
  obtain ⟨hinputEnd, hrec, hq, hfirst, hv, hcoords⟩ := hview
  obtain ⟨r, hr, rr, rvalues, rmem, rregs⟩ := hproduct
  let s := r.extend productBank x
  have hs : ExecWithin (w + 2) (product.rename productBank) x s
      T := hr.rename productBank_injective
  have sr (j : Fin 320) : s.regs (productBank j) = r.regs j :=
    productBank_injective.extend_apply _ _ j
  have sm (u : ℕ) (hu : u < heap) : s.mem u = x.mem u := rmem u (Or.inl hu)
  have snative (j : Fin 320) (hj : j.val < 65) :
      s.regs (productBank j) = x.regs (productBank j) := (sr j).trans (rregs j hj)
  have sout : s.regs (productBank RecordProduct.Reg.result) = out := by
    exact (sr RecordProduct.Reg.result).trans rr
  let v : Fin 6 → ℕ := ![idx.residue.val, idx.piece, q, Q, base + 6, base + 6 + n * D m]
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
    ((sm 1 (by omega)).trans hheaderD)
    ((sm 2 (by omega)).trans hheaderG)
    ((sm 3 (by omega)).trans hheaderN)
    ((snative _ (by decide)).trans hi) (snative _ (by decide)) sout hrec hread hfirst
    hquery smem hmag hU (hfit.of_le (by
      change heap + out + q + 4 * Q + 4 * D m + 2 * (n * D m) +
        9 * (n * n) + 4 * n + g + 2048 ≤ _
      dsimp only [out]
      omega))
  change ExecWithin (w + 2) consume s y
    (5 * Nat.sqrt (D m) + 8 * Q +
      (42 * min (pieceSize (D m) g) (n - idx.piece * pieceSize (D m) g) + 28) * S + 52) at he
  change S ≤ Nat.count (fun j => s.mem (out + j) ≠ 0 ∧
    ∀ c : Fin (min (pieceSize (D m) g) (n - idx.piece * pieceSize (D m) g)),
      AB (x.mem (q + 2 * j)) (x.mem (q + 2 * j + 1)) +
        BC (x.mem (q + 2 * j + 1)) (idx.piece * pieceSize (D m) g + c.val) +
        AC (x.mem (q + 2 * j)) (idx.piece * pieceSize (D m) g + c.val) ≠ 0) Q + y.regs Reg.found
      at hS
  simp_rw [show v 1 = idx.piece from rfl, show v 3 = Q from rfl] at yiff
  have hexe : ExecWithin (w + 2) (.seq (product.rename productBank) consume) x y
      (T + 5 * Nat.sqrt (D m) + 8 * Q +
        (42 * min (pieceSize (D m) g) (n - idx.piece * pieceSize (D m) g) + 28) * S + 52) :=
    (hs.seq he).mono (by omega)
  refine ⟨y, S, hexe, ys, yf, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [ym, frame (productBank RecordProduct.Reg.result) (by decide), sout] using hS
  · simpa only [ym, frame (productBank RecordProduct.Reg.result) (by decide), sout] using yiff
  · intro j
    have hv := rvalues j
    rw [frame _ (by decide), sout, ym]
    change r.mem (out + j.val) = _
    exact hv
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
