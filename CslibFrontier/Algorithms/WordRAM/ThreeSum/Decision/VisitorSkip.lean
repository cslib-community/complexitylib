/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ThreeSum.Decision.VisitorPop
public import CslibFrontier.Algorithms.WordRAM.ThreeSum.ChanHe.TraversalStackFrame

/-!
# Actual skipped transitions in the fused Chan–He visitor

Zero-fuel and empty-column entries execute the original seven pops and actual branch paths.
They perform no solver call, leave the consumed prefix unchanged and preserve every live
pending source, the bitmap and the original frontend prefix.

## Main results

* `skip_transition`: actual execution, complete cursor preservation and decreasing work.
-/

public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.Decision.Visitor

open Cslib.WordRAM
open Cslib.Algorithms.ThreeSum.ChanHe (Node)
open ChanHe.Traversal

/-- A skipped native descriptor leaves the Boolean fold unchanged and reduces traversal credit. -/
theorem skip_transition {r w κ n : ℕ} {a : Arena} {target : List Node}
    (solver : Code .standard (r + 7)) (e : Entry) (es : List Entry) (ns : List Node)
    (x : Data (registerCount r)) (ha : a.Separated) (h2 : Fits (w + 2) 2)
    (hcap : Fits (w + 2) (a.stack + a.capacity))
    (h : (Cursor.mk (e :: es) ns).Invariant a w κ n target x)
    (hskip : e.fuel = 0 ∨ (e.data 0).length = 0 ∨
      (e.data 1).length = 0 ∨ (e.data 2).length = 0) :
    ∃ y, ExecWithin (w + 2) (body solver) x y 107 ∧
      (Cursor.mk es ns).Invariant a w κ n target y ∧
      (Cursor.mk es ns).remaining a = (Cursor.mk (e :: es) ns).remaining a ∧
      (Cursor.mk es ns).work + 1 ≤ (Cursor.mk (e :: es) ns).work ∧
      (∀ T, 109 + (Cursor.mk es ns).credit a T ≤ (Cursor.mk (e :: es) ns).credit a T) ∧
      y.regs (preprocessingRegisters r heap) = x.regs (preprocessingRegisters r heap) := by
  obtain ⟨y, hy, hstack, hloaded, hframe, hp, hm⟩ := pop_entry x e es h2 hcap h.stack
  obtain ⟨(hheap : y.regs (preprocessingRegisters r ChanHe.Traversal.heap) =
      x.regs (preprocessingRegisters r ChanHe.Traversal.heap)), -, hcontrols, hmem, -, hstored,
      hends, hbitmap, hfloor⟩ :=
    Arena.preserved_of_stack_frame _ (y.comap (preprocessingRegisters r)) ha h.controls h.bitmap
      h.stored h.around h.ends h.floor hframe (fun i hi hi' => hp i (Or.inl hi') (Or.inr hi))
  have hbody := body_skip solver hy hloaded hcontrols.2.2.2.2.2.2.2.2.2.1 hskip
  have hstep := Entry.step_of_skip (Nat.primesLE a.m) a.Λ e es hskip
  have hdec := Math.potential_step (Nat.primesLE a.m) a.Λ e.task (es.map Entry.task)
  rw [hstep] at hdec
  change (Cursor.mk es ns).work + 1 ≤ (Cursor.mk (e :: es) ns).work at hdec
  have hremaining : (Cursor.mk es ns).remaining a =
      (Cursor.mk (e :: es) ns).remaining a := by
    have he := Math.output_step (Nat.primesLE a.m) a.Λ e.task (es.map Entry.task)
    rw [hstep] at he
    simp only [Option.toList_none, List.nil_append] at he
    exact he.symm
  have hcredit (T : ℕ) :
      109 + (Cursor.mk es ns).credit a T ≤ (Cursor.mk (e :: es) ns).credit a T := by
    simp only [Cursor.credit, hremaining]
    have hd := Nat.mul_le_mul_right (visitTime a.n a.m a.N + 316) hdec
    rw [Nat.add_mul, Nat.one_mul] at hd
    omega
  refine ⟨y, hbody, ?_, hremaining, hdec, hcredit, hheap⟩
  refine {
    bounded := hbody.bounded h.bounded
    controls := hcontrols
    bitmap := hbitmap
    stack := hstack
    depth := h.depth.2
    valid := fun d hd => h.valid d (List.mem_cons_of_mem e hd)
    stored := fun d hd => hstored d (List.mem_cons_of_mem e hd)
    around := fun d hd => h.around d (List.mem_cons_of_mem e hd)
    ends := fun d hd => hends d (List.mem_cons_of_mem e hd)
    floor := hfloor
    heapBudget := ?_
    packedLength := ?_
    envelopeValue := (hm _).trans h.envelopeValue
    unit := (hm _).trans h.unit
    boolean := (hm _).symm ▸ h.boolean
    verdict := ?_
    exactOutput := ?_
    protectedMemory := ?_ }
  · rw [hheap]
    have hb := h.heapBudget
    have hd := Nat.mul_le_mul_right (ChanHe.Traversal.allocationSize a.n a.m a.N)
      (show (Cursor.mk es ns).work ≤ (Cursor.mk (e :: es) ns).work by omega)
    omega
  · exact (hp _ (Or.inr (by decide)) (Or.inr (by decide))).trans h.packedLength
  · rw [hm]
    exact h.verdict
  · rw [hremaining]
    exact h.exactOutput
  · intro p hp
    exact (hmem p (Or.inl hp)).trans (h.protectedMemory p hp)

end Cslib.Algorithms.WordRAM.ThreeSum.Decision.Visitor
