/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.FixedPrime.Record

/-!
# Charged ordinal delivery, concrete call and native return

This internal step theorem composes the actual copy, unchanged full record computation and
native scan/flag/counter return. The selected finite index is proved from the runtime ordinal;
it is not an additional input field or a supplied algorithm.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.FixedPrime

open Cslib.WordRAM Cslib.Matrix Cslib.Algorithms.ExactTriangle
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage

/-- Execute one real occupied ordinal. The instruction bound includes every argument/return
instruction; its two outer-loop instructions appear in `recordBase`. -/
theorem exec_step {w m n g p A i : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hD : 16 ≤ D m)
    (hg : 1 ≤ g) (hp : p ∈ Nat.sqrtPrimeWindow (D m)) (hN : D m ^ 18 ≤ n)
    (hv : ∀ z ∈ values, z.natAbs ≤ A)
    (hW : admissionWidth n (D m) g p A ≤ w + 2)
    (a : Data 64) (x : Data 416)
    (hout : Instances.Output n (D m) g p (fun q => values.getD q 0)
      (.init (PreparationInput.input n (D m) g p values)) a)
    (hbank : ∀ j : Fin 64,
      x.regs (recordBank (RecordWitness.productBank (RecordProduct.producerBank j))) = a.regs j)
    (hmem : Set.EqOn x.mem a.mem (Set.Iio (a.regs Instances.heap)))
    (hheap : a.regs Instances.heap ≤ PreparationInput.wordBound n (D m) g p A)
    (hi : x.regs Reg.index = i) (hiM : i < a.regs Instances.produced)
    (hl : x.regs Reg.limit = a.regs Instances.produced) (h1 : x.regs Reg.one = 1)
    (hscans : x.regs Reg.scans ≤ i * (n * n + 1))
    (idx : InstanceIndex p)
    (hidx : idx ∈ instanceIndices
      (fun u v : Fin n => values.getD (pairIndex (u, v)) 0) (D m) g p)
    (hord : RecordProduct.recordOrdinal n (D m) g p (fun q => values.getD q 0) idx = i) :
    let V := fun q => values.getD q 0
    let hn : 0 < n := lt_of_lt_of_le (by omega : 0 < D m)
      ((Nat.le_self_pow (by decide : 18 ≠ 0) (D m)).trans hN)
    let Q := RecordProduct.recordQueryCount n (D m) p V idx
    ∃ y S T, ExecWithin (w + 2) step x y T ∧
      T + 2 ≤ recordBase (m := m) hn V a.mem idx +
        (42 * pieceSize (D m) g + 28) * S ∧
      y.regs Reg.index = i + 1 ∧
      y.regs Reg.limit = (if y.regs Reg.found = 1 then i + 1 else a.regs Instances.produced) ∧
      y.regs Reg.one = 1 ∧
      y.regs Reg.scans = x.regs Reg.scans + S ∧
      (y.regs Reg.found = 0 ∨ y.regs Reg.found = 1) ∧
      S ≤ recordFailures (m := m) (g := g) hn V a.mem idx + y.regs Reg.found ∧
      S ≤ n * n + 1 ∧
      (y.regs Reg.found = 1 ↔ recordHit (m := m) (n := n) (g := g) V idx) ∧
      (y.regs Reg.found = 1 →
        y.regs (recordBank RecordWitness.Reg.witnessA) < n ∧
        y.regs (recordBank RecordWitness.Reg.witnessB) < n ∧
        y.regs (recordBank RecordWitness.Reg.witnessC) < n ∧
        V (y.regs (recordBank RecordWitness.Reg.witnessA) * n +
            y.regs (recordBank RecordWitness.Reg.witnessB)) +
          V (n * n + (y.regs (recordBank RecordWitness.Reg.witnessB) * n +
            y.regs (recordBank RecordWitness.Reg.witnessC))) +
          V (2 * (n * n) + (y.regs (recordBank RecordWitness.Reg.witnessA) * n +
            y.regs (recordBank RecordWitness.Reg.witnessC))) = 0) ∧
      (∀ u, u < a.regs Instances.heap ∨
        a.regs Instances.heap + CallableProduct.windowSize n Q ≤ u → y.mem u = x.mem u) ∧
      ∀ j : Fin 64, y.regs
        (recordBank (RecordWitness.productBank (RecordProduct.producerBank j))) = a.regs j := by
  let V := fun q => values.getD q 0
  let hn : 0 < n := lt_of_lt_of_le (by omega : 0 < D m)
    ((Nat.le_self_pow (by decide : 18 ≠ 0) (D m)).trans hN)
  let dst := recordBank (RecordWitness.productBank RecordProduct.Reg.ordinal)
  let z := x.set dst i
  have hselect : ExecWithin (w + 2) select x z 1 := by
    simpa only [select, hi, dst, z] using
      (ExecWithin.copy (B := .standard) (w := w + 2) (x := x) (d := dst) (s := Reg.index))
  have zbank (j : Fin 64) :
      z.regs (recordBank (RecordWitness.productBank (RecordProduct.producerBank j))) =
        a.regs j := by
    change Function.update x.regs dst i
      (recordBank (RecordWitness.productBank (RecordProduct.producerBank j))) = a.regs j
    rw [Function.update_of_ne (by
      intro h
      have hv := congrArg (fun k : Fin 416 => k.val) h
      change j.val = 64 at hv
      omega)]
    exact hbank j
  have control (j : Fin 416) (hj : 400 ≤ j.val) : z.regs j = x.regs j := by
    change Function.update x.regs dst i j = x.regs j
    apply Function.update_of_ne
    intro h
    have hv := congrArg (fun k : Fin 416 => k.val) h
    change j.val = 64 at hv
    omega
  obtain ⟨r, S, hr, rs, rf, hS, hcoarse, hit, wit, frame, bank, ctrl⟩ :=
    exec_record values hlen hD hg hp hN hv hW a z hout zbank hmem hheap idx hidx (by
      change Function.update x.regs dst i dst = _
      simpa using hord.symm)
  have rc (j : Fin 416) (hj : 400 ≤ j.val) : r.regs j = x.regs j :=
    (ctrl j hj).trans (control j hj)
  have hfits := return_fits hW
    (produced_le V hout hD ((Nat.le_self_pow (by decide : 18 ≠ 0) (D m)).trans hN) hg)
    hiM hscans hcoarse
  obtain ⟨y, hy, ym, yi, yl, ys, yf, ypres⟩ := exec_receive r
    ((rc Reg.index (by decide)).trans hi) ((rc Reg.limit (by decide)).trans hl)
    (rc Reg.scans (by decide)) rs rfl ((rc Reg.one (by decide)).trans h1) hfits.1 hfits.2
  have yflag : y.regs Reg.found = r.regs (recordBank RecordWitness.Reg.found) := yf
  have ylow (j : Fin 400) : y.regs (recordBank j) = r.regs (recordBank j) :=
    ypres _ (Or.inl (by change j.val < 400; exact j.isLt))
  let T := RecordProduct.timeBound (m := m)
    (RecordProduct.decodedQueries hn a.mem (RecordProduct.recordQueries n (D m) p idx)
      (RecordProduct.recordQueryCount n (D m) p V idx)) +
    5 * Nat.sqrt (D m) + 8 * RecordProduct.recordQueryCount n (D m) p V idx +
      (42 * pieceSize (D m) g + 28) * S + 59
  have hex : ExecWithin (w + 2) step x y T := (hselect.seq (hr.seq hy)).mono (by
    dsimp only [T, V]
    omega)
  refine ⟨y, S, T, hex, ?_, yi, ?_, ?_, ys, ?_, ?_, hcoarse, ?_, ?_, ?_, ?_⟩
  · dsimp only [recordBase, T, V]
    omega
  · rw [yflag]
    exact yl
  · exact (ypres _ (Or.inr rfl)).trans ((rc Reg.one (by decide)).trans h1)
  · simpa only [yflag] using rf
  · simpa only [yflag] using hS
  · simpa only [yflag, recordHit, weightSum] using hit
  · intro hf
    simpa only [ylow] using wit (yflag ▸ hf)
  · intro u hu
    exact (congrFun ym u).trans (frame u hu)
  · intro j
    exact (ylow _).trans (bank j)

end Cslib.Algorithms.WordRAM.ExactTriangle.FixedPrime
