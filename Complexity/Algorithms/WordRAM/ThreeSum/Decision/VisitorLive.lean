/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.Decision.VisitorBounds
public import Complexity.Algorithms.WordRAM.ThreeSum.Decision.VisitorPop
import Complexity.Computability.WordRAM.Call
import Complexity.Algorithms.WordRAM.ThreeSum.Decision.Registers

/-!
# Actual live node consumption in the fused Chan–He visitor

The actual local node construction is followed by the certified Convolution call and all
three native child pushes. The callee may dirty arbitrary higher scratch; its live-prefix
frame preserves the newly constructed heavy arrays and every pending source.
-/

public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.Decision.Visitor

open Cslib.WordRAM
open Cslib.Algorithms.ThreeSum.ChanHe (Node)
open ChanHe.Traversal (Entry Arena)
open ChanHe.Traversal

/-- Construct the actual current node and consume it before modifying the pending worklist.
The construction witness stays at the pre-call state; the actual return frame retains live data. -/
theorem construct_consume {r κ n w : ℕ} {a : Arena} (c : Host.Callee r)
    (e : Entry) (x : Data (registerCount r))
    (hw : width κ c.widthCoefficient n ≤ w + 2)
    (ha : a.Separated)
    (hresources : a.ceiling ≤ (n + 2) ^ envelopeExponent κ ∧
      4 * a.N < (n + 2) ^ envelopeExponent κ ∧
      60 * a.U + 40 ≤ (n + 2) ^ envelopeExponent κ)
    (hready : a.Ready w)
    (hc : a.Controls
      (x.comap (preprocessingRegisters r)))
    (hl : e.Loaded (x.comap (preprocessingRegisters r)))
    (hv : e.Valid a.n
      a.U)
    (hs : e.Stored x.mem)
    (hbitmap : a.Bitmap x.mem)
    (hfloor : a.floor ≤
      x.regs (preprocessingRegisters r ChanHe.Traversal.heap))
    (hbudget : x.regs (preprocessingRegisters r ChanHe.Traversal.heap) +
      ChanHe.Traversal.allocationSize a.n
        a.m
        a.N ≤
      a.ceiling)
    (hsrc : ∀ j, e.source j + (e.data j).length ≤
      x.regs (preprocessingRegisters r ChanHe.Traversal.heap))
    (hlen : x.regs (preprocessingRegisters r ChanHe.Preprocessing.packedLength) =
      4 * a.N)
    (henv : x.regs (controllerRegisters r envelope) = (n + 2) ^ envelopeExponent κ)
    (hone : x.regs (controllerRegisters r one) = 1)
    (hb : x.regs (controllerRegisters r answer) ≤ 1) :
    ∃ q y, ExecWithin (w + 2)
        (ChanHe.Traversal.localVisit.rename (preprocessingRegisters r)) x q
        (ChanHe.Traversal.visitTime a.n a.m a.N) ∧
      ExecWithin (w + 2) (consume c.code) q y
        (Host.callerTime (4 * a.N)
          (c.time (Host.sideLength (4 * a.N)) (2 * (n + 2) ^ envelopeExponent κ + 1)) + 7) ∧
      Nonempty (ChanHe.Traversal.Emission (Nat.primesLE a.m) a.Λ e
        (x.comap (preprocessingRegisters r)) (q.comap (preprocessingRegisters r)) false) ∧
      y.regs (controllerRegisters r answer) ≤ 1 ∧
      (y.regs (controllerRegisters r answer) = 1 ↔
        x.regs (controllerRegisters r answer) = 1 ∨
          Cslib.Algorithms.ThreeSum.Convolution
            (4 * a.N)
            ((e.task.node (Nat.primesLE a.m)
              a.Λ).oneArray
                a.U)) ∧
      (∀ i, y.regs (preprocessingRegisters r i) = q.regs (preprocessingRegisters r i)) ∧
      (∀ i, i ≠ answer →
        y.regs (controllerRegisters r i) = x.regs (controllerRegisters r i)) ∧
      ∀ p < q.regs (preprocessingRegisters r ChanHe.Traversal.heap), y.mem p = q.mem p := by
  have hheap : x.regs (preprocessingRegisters r ChanHe.Traversal.heap) ≤
      a.ceiling := by
    omega
  have hlocal := ChanHe.Traversal.emit_admitted false (x.comap (preprocessingRegisters r)) e
    ha hready hc hl hv hs hbitmap
    hfloor hheap hsrc (by intro h; cases h)
  obtain ⟨v, he, ⟨em⟩, hf⟩ := ExecWithin.rename_post (preprocessing_injective r) hlocal
  have hframe (i : Fin 16) :
      v.regs (controllerRegisters r i) = x.regs (controllerRegisters r i) :=
    hf _ (fun j => (controller_ne_preprocessing i j).symm)
  have halloc : v.regs (preprocessingRegisters r ChanHe.Traversal.heap) ≤
      x.regs (preprocessingRegisters r ChanHe.Traversal.heap) +
        ChanHe.Traversal.allocationSize a.n a.m a.N := by
    have heh := em.heap_eq
    simp only [Data.comap_regs] at heh
    rw [heh]
    apply ChanHe.Traversal.allocation_le
    · intro j
      rw [hl.2.2]
      exact hv.length_le j
    · exact hc.2.2.2.1.le
    · simpa only [hc.1] using em.upper
  have hlenv : v.regs (preprocessingRegisters r ChanHe.Preprocessing.packedLength) = 4 * a.N :=
    (em.registers _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (Or.inr (by decide))).trans hlen
  obtain ⟨y, hy, hyb, hya, hyp, hym, hyf⟩ := exec_consume_emission c e
    (x.comap (preprocessingRegisters r)) v em hc hv hw hresources (by omega) hlenv
    ((hframe _).trans henv) ((hframe _).trans hone) (by rw [hframe]; exact hb)
  refine ⟨v, y, he, hy, ⟨em⟩, hyb, ?_, hyp, ?_, hyf⟩
  · rw [hya, hframe]
  · intro i hi
    exact (hym i hi).trans (hframe i)

end Cslib.Algorithms.WordRAM.ThreeSum.Decision.Visitor
