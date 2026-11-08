/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.StreamingFixedPrime.Record
public import Complexity.Algorithms.WordRAM.ExactTriangle.StreamingFixedPrime.Slot
public import Complexity.Algorithms.WordRAM.ExactTriangle.StreamingFixedPrime.Readback
public import Complexity.Algorithms.WordRAM.ExactTriangle.StreamingFixedPrime.Admission
import Complexity.Computability.WordRAM.RegisterFrame

/-!
# One-slot record construction, call, heap reset and return

`exec_step` composes one streaming loop body: constructing the next logical chunk/piece record in
the single physical slot (`construct`), selecting constant physical ordinal zero (`select`),
running the box-product and original-weight verifier (`FixedPrime.record`), resetting the heap
pointer to `Instances.output` (`reset`), and updating the scan counter, witness flag and early-stop
limit (`FixedPrime.receive`).
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.StreamingFixedPrime

open Cslib.WordRAM Cslib.Matrix Cslib.Algorithms.ExactTriangle
open FixedPrime
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage

/-- One actual construction, physical-slot call, reclamation and native return. The charge
includes every bridge instruction; the loop's two instructions appear on the left. -/
theorem exec_step {w m n g p A i : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hD : 16 ≤ D m)
    (hg : 1 ≤ g) (hp : p ∈ Nat.sqrtPrimeWindow (D m)) (hN : D m ^ 18 ≤ n)
    (hv : ∀ z ∈ values, z.natAbs ≤ A)
    (hW : FixedPrime.admissionWidth n (D m) g p A ≤ w + 2)
    (a : Data 64) (x : Data 416)
    (hout : Instances.Output n (D m) g p (fun q => values.getD q 0)
      (.init (PreparationInput.input n (D m) g p values)) a)
    (cursor : Cursor n (D m) g p (fun q => values.getD q 0) (x.comap producerBank))
    (hproduced : x.regs (producerBank Instances.produced) = i)
    (hslotHeap : x.regs (producerBank Instances.heap) = x.regs (producerBank Instances.output))
    (hmem : Set.EqOn x.mem a.mem (Set.Iio (a.regs Instances.output)))
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
      T + 2 ≤ FixedPrime.recordBase (m := m) hn V a.mem idx +
        (40 * (n * D m) + 67) +
        (42 * pieceSize (D m) g + 28) * S ∧
      y.regs Reg.index = i + 1 ∧
      y.regs Reg.limit = (if y.regs Reg.found = 1 then i + 1 else a.regs Instances.produced) ∧
      y.regs Reg.one = 1 ∧
      y.regs Reg.scans = x.regs Reg.scans + S ∧
      (y.regs Reg.found = 0 ∨ y.regs Reg.found = 1) ∧
      S ≤ FixedPrime.recordFailures (m := m) (g := g) hn V a.mem idx + y.regs Reg.found ∧
      S ≤ n * n + 1 ∧
      (y.regs Reg.found = 1 ↔ FixedPrime.recordHit (m := m) (n := n) (g := g) V idx) ∧
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
      (∀ u, u < a.regs Instances.output ∨
        a.regs Instances.output + (6 + 2 * (n * D m)) +
          CallableProduct.windowSize n Q ≤ u → y.mem u = x.mem u) ∧
      Cursor n (D m) g p V (y.comap producerBank) ∧
      y.regs (producerBank Instances.produced) = i + 1 ∧
      y.regs (producerBank Instances.heap) = y.regs (producerBank Instances.output) := by
  let V := fun q => values.getD q 0
  have hDn : D m ≤ n := (Nat.le_self_pow (by decide : 18 ≠ 0) (D m)).trans hN
  have hp0 := (Nat.mem_sqrtPrimeWindow_iff_sq.mp hp).1.ne_zero
  have hout' : x.regs (producerBank Instances.output) = a.regs Instances.output := by
    have hc := cursor.output
    rw [cursor.chunks] at hc
    exact hc.trans hout.2.2.2.1.symm
  have htotal : x.regs (producerBank Instances.total) = a.regs Instances.produced := by
    have hc := cursor.total
    rw [cursor.chunks, cursor.pieces] at hc
    exact hc.trans hout.2.2.2.2.1.symm
  have hprep : PreparationInput.width n (D m) g p A ≤ w + 2 := by
    have hr := FixedPrime.record_admitted hW
    unfold RecordWitness.admissionWidth RecordProduct.admissionWidth at hr
    omega
  have budget := (PreparationInput.fits_at_width n (D m) g p A).2.mono hprep
  have hf : Function.Injective producerBank := Fin.castLE_injective (by decide)
  obtain ⟨residues, descriptor⟩ := catalogue_readback V
    (.init (PreparationInput.input n (D m) g p values)) a (x.comap producerBank)
    hout hp0 cursor hmem idx hidx
  obtain ⟨c, hc, ccursor, ci, ch, cd, cL, cR, cm⟩ := exec_construct V
    (x.comap producerBank) hD hg hp0 cursor hslotHeap idx hidx
    (hproduced.trans hord.symm) residues descriptor
    (budget.of_le (cursor.visit_budget_le hD hDn hg hslotHeap (by
      change x.regs (producerBank Instances.produced) < x.regs (producerBank Instances.total)
      rw [hproduced, htotal]
      exact hiM)))
  simp only [Data.comap_regs, Data.comap_mem] at ci ch cd cL cR cm
  let s := c.extend producerBank x
  have hs : ExecWithin (w + 2) construct x s (40 * (n * D m) + 66) := hc.rename hf
  have sr (j : Fin 64) : s.regs (producerBank j) = c.regs j := hf.extend_apply _ _ j
  have scursor : Cursor n (D m) g p V (s.comap producerBank) := by
    simpa only [s, Data.comap_extend hf] using ccursor
  have scontrol (j : Fin 416) (hj : 400 ≤ j.val) : s.regs j = x.regs j :=
    hs.regs_eq (Instances.visit.preserves_rename_of_offset
      (offset := 0) producerBank (fun j => (Nat.zero_add j.val).symm) j
      (Or.inr (by omega)))
  have so : s.regs (producerBank Instances.output) = a.regs Instances.output := by
    have h := hc.regs_eq (Instances.visit_preserves Instances.output (by decide))
    exact (sr _).trans (h.trans hout')
  have sh : s.regs (producerBank Instances.heap) = a.regs Instances.output +
      (6 + 2 * (n * D m)) := by
    rw [sr]
    simpa only [hout'] using ch
  let dst := recordBank (RecordWitness.productBank RecordProduct.Reg.ordinal)
  let z := s.set dst 0
  have hz : ExecWithin (w + 2) select s z 1 := ExecWithin.const (fits_zero _)
  have zlow (j : Fin 64) : z.regs (producerBank j) = s.regs (producerBank j) := by
    change Function.update s.regs dst 0 (producerBank j) = _
    apply Function.update_of_ne
    intro h
    have hv := congrArg (fun k : Fin 416 => k.val) h
    change j.val = 64 at hv
    omega
  have zcontrol (j : Fin 416) (hj : 400 ≤ j.val) : z.regs j = x.regs j := by
    change Function.update s.regs dst 0 j = _
    rw [Function.update_of_ne (by
      intro h
      have hv := congrArg (fun k : Fin 416 => k.val) h
      change j.val = 64 at hv
      omega)]
    exact scontrol j hj
  have zm : z.mem = c.mem := rfl
  have zmem : Set.EqOn z.mem a.mem (Set.Iio (a.regs Instances.output)) := by
    intro u hu
    exact (cm u (Or.inl (by simpa only [hout', Set.mem_Iio] using hu))).trans (hmem hu)
  have zh : z.regs (producerBank Instances.heap) = a.regs Instances.output +
      (6 + 2 * (n * D m)) := (zlow _).trans sh
  have zo : z.regs (producerBank Instances.output) = a.regs Instances.output := (zlow _).trans so
  have slot_le : z.regs (producerBank Instances.heap) ≤ a.regs Instances.heap := by
    have hh := hout.2.2.2.2.2.1
    have ho := hout.2.2.2.1
    have hc := hout.2.2.2.2.1
    have hpositive : 1 ≤ a.regs Instances.produced := by omega
    have hs := Nat.mul_le_mul_right (6 + 2 * (n * D m)) hpositive
    rw [Nat.one_mul] at hs
    rw [zh, hh, ← ho, ← hc]
    omega
  obtain ⟨r, S, hr, rs, rf, hS, hcoarse, hit, wit, frame, bank, ctrl⟩ :=
    exec_record values hlen hD hg hp hN hv hW a z hout zmem hheap idx hidx
      (by change Function.update s.regs dst 0 dst = 0; simp)
      zo zh slot_le (by
        simpa only [Block.Realizes, Block.read, hout', Data.comap_mem, zm, V]
          using And.intro cd (And.intro cL cR))
  have rc (j : Fin 416) (hj : 400 ≤ j.val) : r.regs j = x.regs j :=
    (ctrl j hj).trans (zcontrol j hj)
  let t := r.set (producerBank Instances.heap) (r.regs (producerBank Instances.output))
  have ht : ExecWithin (w + 2) reset r t 1 := exec_reset r
  have tcontrol (j : Fin 416) (hj : 400 ≤ j.val) : t.regs j = x.regs j := by
    change Function.update r.regs (producerBank Instances.heap)
      (r.regs (producerBank Instances.output)) j = _
    rw [Function.update_of_ne (by
      intro h
      have hv := congrArg (fun k : Fin 416 => k.val) h
      change j.val = 42 at hv
      omega)]
    exact rc j hj
  have tflag : t.regs (recordBank RecordWitness.Reg.found) =
      r.regs (recordBank RecordWitness.Reg.found) := by
    change Function.update r.regs (producerBank Instances.heap)
      (r.regs (producerBank Instances.output)) (recordBank RecordWitness.Reg.found) = _
    apply Function.update_of_ne
    decide
  have tscans : t.regs (recordBank RecordWitness.Reg.scans) = S := by
    change Function.update r.regs (producerBank Instances.heap)
      (r.regs (producerBank Instances.output)) (recordBank RecordWitness.Reg.scans) = S
    rw [Function.update_of_ne (by decide)]
    exact rs
  have fits := FixedPrime.return_fits hW
    (FixedPrime.produced_le V hout hD hDn hg) hiM hscans hcoarse
  obtain ⟨y, hy, ym, yi, yl, ys, yf, ypres⟩ := FixedPrime.exec_receive t
    ((tcontrol _ (by decide)).trans hi) ((tcontrol _ (by decide)).trans hl)
    (tcontrol _ (by decide)) tscans tflag ((tcontrol _ (by decide)).trans h1) fits.1 fits.2
  have yflag : y.regs FixedPrime.Reg.found = r.regs (recordBank RecordWitness.Reg.found) := yf
  have ylow (j : Fin 400) : y.regs (recordBank j) = t.regs (recordBank j) :=
    ypres _ (Or.inl (by change j.val < 400; exact j.isLt))
  have tr (j : Fin 400) (hj : recordBank j ≠ producerBank Instances.heap) :
      t.regs (recordBank j) = r.regs (recordBank j) := Function.update_of_ne hj _ _
  have zcursor : Cursor n (D m) g p V (z.comap producerBank) :=
    scursor.transfer fun j _ _ _ _ => zlow j
  have rcursor : Cursor n (D m) g p V (r.comap producerBank) :=
    zcursor.transfer fun j _ _ _ _ => bank j
  have tcursor : Cursor n (D m) g p V (t.comap producerBank) := by
    apply rcursor.transfer
    intro j _ _ _ hj
    change Function.update r.regs (producerBank Instances.heap)
      (r.regs (producerBank Instances.output)) (producerBank j) = _
    exact Function.update_of_ne (fun he => hj (hf he)) _ _
  have ycursor : Cursor n (D m) g p V (y.comap producerBank) :=
    tcursor.transfer fun j _ _ _ _ => ypres _ (Or.inl (by change j.val < 400; omega))
  let Q := RecordProduct.recordQueryCount n (D m) p V idx
  let hn : 0 < n := lt_of_lt_of_le (by omega : 0 < D m) hDn
  let T := 40 * (n * D m) + 66 +
    (RecordBoxProduct.timeBound (m := m)
      (RecordProduct.decodedQueries hn a.mem (RecordProduct.recordQueries n (D m) p idx) Q) +
      5 * Nat.sqrt (D m) + 8 * Q + (42 * pieceSize (D m) g + 28) * S + 52) + 8
  have he : ExecWithin (w + 2) step x y T := by
    apply (hs.seq (hz.seq (hr.seq (ht.seq hy)))).mono
    dsimp only [T, Q, V]
    omega
  refine ⟨y, S, T, he, ?_, yi, ?_, ?_, ys, ?_, ?_, hcoarse, ?_, ?_, ?_,
    ycursor, ?_, ?_⟩
  · dsimp only [T, Q, FixedPrime.recordBase, V]
    omega
  · rw [yflag]
    exact yl
  · exact (ypres _ (Or.inr rfl)).trans ((tcontrol _ (by decide)).trans h1)
  · simpa only [yflag] using rf
  · simpa only [yflag] using hS
  · simpa only [yflag, FixedPrime.recordHit, weightSum] using hit
  · intro hh
    have hw := wit (yflag ▸ hh)
    simpa only [ylow, tr RecordWitness.Reg.witnessA (by decide),
      tr RecordWitness.Reg.witnessB (by decide), tr RecordWitness.Reg.witnessC (by decide)] using hw
  · intro u hu
    have slotframe : c.mem u = x.mem u := cm u (by
      rw [hout']
      omega)
    have recordframe : r.mem u = z.mem u := frame u (by rw [zh]; omega)
    exact (congrFun ym u).trans (recordframe.trans slotframe)
  · have yo : y.regs (producerBank Instances.produced) = r.regs (producerBank Instances.produced) :=
      (ypres _ (Or.inl (by decide))).trans (tr _ (by decide))
    rw [yo, bank, zlow, sr, ci, hproduced]
  · have yo : y.regs (producerBank Instances.output) = r.regs (producerBank Instances.output) :=
      (ypres _ (Or.inl (by decide))).trans (tr _ (by decide))
    rw [yo]
    exact (ypres _ (Or.inl (by decide))).trans (by simp [t])

end Cslib.Algorithms.WordRAM.ExactTriangle.StreamingFixedPrime
