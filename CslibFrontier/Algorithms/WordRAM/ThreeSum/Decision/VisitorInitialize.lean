/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ThreeSum.Decision.VisitorForestInvariant
public import CslibFrontier.Algorithms.WordRAM.ThreeSum.Decision.VisitorSetup
import all CslibFrontier.Algorithms.WordRAM.ThreeSum.ChanHe.PreprocessingSetup
import CslibFrontier.Algorithms.WordRAM.ThreeSum.Frontend.Frame
import CslibFrontier.Computability.WordRAM.Call
import CslibFrontier.Algorithms.WordRAM.ThreeSum.Decision.Registers

/-!
# Actual native initialization of the fused Chan–He forest

The existing snapshot, prime-table builder and layout programs prepare the same physical
regions as before. The caller then computes its value envelope before the first root.
Every stage executes actual native code and retains the computed frontend descriptors.
-/

public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.Decision.Visitor

open Cslib.WordRAM
open ChanHe.Traversal
open ChanHe.Preprocessing

private structure Prepared (κ n : ℕ) (rs : List (ℕ × ℕ)) (x : Data 128) : Prop where
  saved : Saved κ n x
  controls : (arena κ n x.mem).Controls x
  bitmap : (arena κ n x.mem).Bitmap x.mem
  heap : x.regs ChanHe.Traversal.heap = (arena κ n x.mem).floor
  frontend : Frontend.Output (Frontend.layout κ n) ((n + 2) ^ κ) rs x.mem

private theorem prepareTraversal_exec {κ n w : ℕ} (rs : List (ℕ × ℕ)) (x : Data 128)
    (hw : ChanHe.Preprocessing.width κ n ≤ w + 2)
    (hfront : Frontend.Output (Frontend.layout κ n) ((n + 2) ^ κ) rs x.mem)
    (hparams : ChanHe.Parameters.Output n ((n + 2) ^ κ) (x.comap Frontend.parameterRegisters))
    (hbase : x.regs Frontend.descriptorBase = (Frontend.layout κ n).descriptors)
    (hcount : x.regs Frontend.descriptorCount = (Frontend.layout κ n).count)
    (hend : x.regs Frontend.heapEnd = (Frontend.layout κ n).endpoint)
    (hcard : rs.length ≤ n) :
    let m := Cslib.Algorithms.ThreeSum.ChanHe.mPar n (2 * (n + 2) ^ κ)
    let F := Cslib.Algorithms.ThreeSum.ChanHe.fuel n
    ∃ y, ExecWithin (w + 2) prepareTraversal x y
        (13 + (2 + ((m + 1) * (7 * m + 15) + 8)) + 19 + (4 * (F + 1) + 5)) ∧
      Prepared κ n rs y := by
  have hfits := setup_fits hw x.mem
  obtain ⟨p, hp, ps, pm⟩ := snapshot_exec x hparams hbase hcount hend hfits.2.2.2
  obtain ⟨q, hq, qs, qm, qcount, qbitmap, qprefix⟩ := primes_exec p ps hfits.2.1
  obtain ⟨r, hr, rsaved, rcontrols, rcount, rpower, rremaining, rscalar, rm⟩ :=
    setupTraversal_exec q qs qcount (setup_fits hw q.mem).1
  obtain ⟨b, hb, bs, bcontrols, bcount, bheap, _, _, bm⟩ :=
    finish_exec r rsaved rcontrols rcount rpower rremaining rscalar
      (setup_fits hw r.mem).2.2.1 ((setup_fits hw r.mem).1.of_le (by omega))
  have bmem : b.mem = q.mem := bm.trans rm
  refine ⟨b, (hp.within.seq (hq.seq (hr.within.seq hb))).mono (by omega),
    bs, ?_, ?_, ?_, ?_⟩
  · simpa only [bmem, rm] using bcontrols
  · intro v hv
    change b.mem ((Frontend.layout κ n).endpoint + v) = _
    rw [bmem]
    exact qbitmap v hv
  · simpa only [bmem, rm] using bheap
  · rw [bmem]
    apply hfront.frame hcard
    intro v hv
    exact (qprefix v hv).trans (congrFun pm v)

/-- Execute every shared preparation instruction and the value-envelope loop before the forest.
Only actual frontend output and the uniform ordinary width are supplied. -/
theorem initialize_forest {r κ n w d : ℕ} (rs : List (ℕ × ℕ))
    (x : Data (registerCount r)) (hw : Decision.width κ d n ≤ w + 2)
    (hx : x.Bounded (w + 2))
    (hlen : x.regs (controllerRegisters r inputLength) = n)
    (hans : x.regs (controllerRegisters r answer) = 0)
    (hfront : Frontend.Output (Frontend.layout κ n) ((n + 2) ^ κ) rs x.mem)
    (hparams : ChanHe.Parameters.Output n ((n + 2) ^ κ)
      ((x.comap (preprocessingRegisters r)).comap Frontend.parameterRegisters))
    (hbase : x.regs (preprocessingRegisters r Frontend.descriptorBase) =
      (Frontend.layout κ n).descriptors)
    (hcount : x.regs (preprocessingRegisters r Frontend.descriptorCount) =
      (Frontend.layout κ n).count)
    (hend : x.regs (preprocessingRegisters r Frontend.heapEnd) =
      (Frontend.layout κ n).endpoint) (hcard : rs.length ≤ n) :
    let m := Cslib.Algorithms.ThreeSum.ChanHe.mPar n (2 * (n + 2) ^ κ)
    let F := Cslib.Algorithms.ThreeSum.ChanHe.fuel n
    ∃ y, ExecWithin (w + 2)
        (.seq (prepareTraversal.rename (preprocessingRegisters r))
          (.seq (prepareEnvelope κ) (Decision.power.rename (controllerRegisters r)))) x y
        (13 + (2 + ((m + 1) * (7 * m + 15) + 8)) + 19 + (4 * (F + 1) + 5) +
          (4 * envelopeExponent κ + 8)) ∧
      (ForestCursor.mk 0 []).Invariant (arena κ n y.mem) w κ n
        (Frontend.layout κ n) ((n + 2) ^ κ) rs y := by
  have hpre := (preprocessing_width_le κ d n).trans hw
  obtain ⟨b, hb, hprep, hframe⟩ := ExecWithin.rename_post (preprocessing_injective r)
    (prepareTraversal_exec rs (x.comap (preprocessingRegisters r)) hpre
      (by simpa only [Data.comap_mem] using hfront) hparams hbase hcount hend hcard)
  have hc (i : Fin 16) : b.regs (controllerRegisters r i) =
      x.regs (controllerRegisters r i) :=
    hframe _ (fun j => (controller_ne_preprocessing i j).symm)
  obtain ⟨y, hy, hyenv, hyone, hyans, hyp, hym⟩ :=
    exec_initializeEnvelope b hw ((hc _).trans hlen)
  have hys := hprep.saved.congr (y := y.comap (preprocessingRegisters r)) (by
    intro i _ _
    simpa only [Data.comap_regs] using hyp i)
  have hbc := hprep.controls
  have hbb := hprep.bitmap
  have hbh := hprep.heap
  have hbf := hprep.frontend
  simp only [Data.comap_mem, Data.comap_regs] at hbc hbb hbh hbf
  have yah : y.regs (preprocessingRegisters r ChanHe.Traversal.heap) = (arena κ n y.mem).floor := by
    rw [hyp, hbh, hym]
  have ya : y.regs (controllerRegisters r answer) = 0 := hyans.trans ((hc _).trans hans)
  refine ⟨y, hb.seq hy, ?_⟩
  refine {
    bounded := hy.bounded (hb.bounded hx)
    controls := ?_
    frontend := ?_
    descriptors := hys.base
    roots := hys.count
    current := hys.index
    levels := hys.fuel
    stride := hys.stride
    increment := hys.one
    index_le := Nat.zero_le _
    bitmap := ?_
    floor := yah.ge
    heapBudget := ?_
    packedLength := ?_
    envelopeValue := hyenv
    unit := hyone
    boolean := by omega
    verdict := ?_
    exactOutput := ?_
    protectedMemory := ?_ }
  · simpa only [hym] using hbc.congr (by
      intro i _
      simpa only [Data.comap_regs] using hyp i)
  · simpa only [hym] using hbf
  · simpa only [hym] using hbb
  · rw [yah]
    exact le_rfl
  · have hh : y.regs (preprocessingRegisters r packedLength) =
        8 * Cslib.Algorithms.ThreeSum.ChanHe.mPar n (2 * (n + 2) ^ κ) ^ 2 := hys.length
    change y.regs (preprocessingRegisters r packedLength) =
      4 * (2 * Cslib.Algorithms.ThreeSum.ChanHe.mPar n (2 * (n + 2) ^ κ) ^ 2)
    omega
  · simp only [ya, Nat.zero_ne_one, List.not_mem_nil, false_and, exists_false]
  · simp only [ForestCursor.remaining, List.drop_zero, List.nil_append]
  · intro p _
    rfl

end Cslib.Algorithms.WordRAM.ThreeSum.Decision.Visitor
