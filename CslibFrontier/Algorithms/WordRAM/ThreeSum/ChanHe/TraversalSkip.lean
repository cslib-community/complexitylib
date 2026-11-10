/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ThreeSum.ChanHe.TraversalStackFrame
public import CslibFrontier.Algorithms.WordRAM.ThreeSum.ChanHe.TraversalStep

/-!
# Complete skipped transitions of the native worklist

Zero-fuel and empty entries still execute the seven native pops and their actual branch paths.
The remaining arrays, bitmap and previously emitted packed output retain exact readback.
Both space reservations improve because the transition measure decreases without allocation.

## Main results

* `skip_transition`: the actual native body preserves the full worklist invariant on every
  skipped entry and strictly decreases its remaining charged-transition measure.

These native composition and invariant proofs are original.
-/

public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Traversal

open Cslib.WordRAM
open Cslib.Algorithms.ThreeSum.ChanHe (Node)

/-- Popping a skipped entry executes the complete native body and preserves every part of the
worklist invariant, including exact output, all live memory and concrete space reservations. -/
theorem skip_transition {a : Arena} {w : ℕ} {target : List Node}
    (e : Entry) (es : List Entry) (ns : List (ℕ × Node)) (x : Data 128)
    (ha : a.Separated) (h2 : Fits (w + 2) 2)
    (hcap : Fits (w + 2) (a.stack + a.capacity))
    (h : (Cursor.mk (e :: es) ns).Invariant a w target x)
    (hskip : e.fuel = 0 ∨ (e.data 0).length = 0 ∨
      (e.data 1).length = 0 ∨ (e.data 2).length = 0) :
    ∃ y, ExecWithin (w + 2) body x y 107 ∧
      (Cursor.mk es ns).Invariant a w target y ∧
      (Cursor.mk es ns).work < (Cursor.mk (e :: es) ns).work := by
  obtain ⟨y, hy, hstack, hloaded, hframe, hp⟩ := pop_entry x e es h2 hcap h.stack
  obtain ⟨hheap, hcount, hcontrols, hmem, -, hstored, hends, hbitmap, hfloor⟩ :=
    Arena.preserved_of_stack_frame x y ha h.controls h.bitmap h.stored h.around h.ends h.floor
      hframe (fun i hi hi' => hp i (Or.inl hi') (Or.inr hi))
  have hbody := body_skip hy hloaded hcontrols.2.2.2.2.2.2.2.2.2.1 hskip
  have hstep := Entry.step_of_skip (Nat.primesLE a.m) a.Λ e es hskip
  have hdec := Math.potential_step (Nat.primesLE a.m) a.Λ e.task (es.map Entry.task)
  rw [hstep] at hdec
  change (Cursor.mk es ns).work + 1 ≤ (Cursor.mk (e :: es) ns).work at hdec
  refine ⟨y, hbody, ?_, by omega⟩
  refine ⟨hbody.bounded h.bounded, hcontrols, hbitmap, hstack, h.depth.2,
    fun d hd => h.valid d (List.mem_cons_of_mem e hd),
    fun d hd => hstored d (List.mem_cons_of_mem e hd),
    fun d hd => h.around d (List.mem_cons_of_mem e hd),
    fun d hd => hends d (List.mem_cons_of_mem e hd), hfloor, ?_, hcount.trans h.count, ?_, ?_,
    ?_, ?_, ?_⟩
  · rw [hheap]
    have hb := h.heapBudget
    have hd := Nat.mul_le_mul_right (allocationSize a.n a.m a.N) (Nat.le_of_lt
      (show (Cursor.mk es ns).work < (Cursor.mk (e :: es) ns).work by omega))
    omega
  · have hb := h.tableBudget
    change ns.length + (Cursor.mk (e :: es) ns).work ≤ a.outputCapacity at hb
    change ns.length + (Cursor.mk es ns).work ≤ a.outputCapacity
    omega
  · apply h.output.congr
    · intro p hp _
      exact hmem p (Or.inr (by have := ha.2.1; omega))
    · intro i u _
      exact hmem _ (Or.inr (by
        have hi := (h.outputBounds i).1
        have ht := ha.2.1
        have hf := ha.2.2.1
        omega))
  · intro i
    rw [hheap]
    exact h.outputBounds i
  · have he := Math.output_step (Nat.primesLE a.m) a.Λ e.task (es.map Entry.task)
    rw [hstep] at he
    simp only [Option.toList_none, List.nil_append] at he
    simpa only [Cursor.pending, Cursor.emitted, List.map_cons, he] using h.exactOutput
  · intro p hp
    exact (hmem p (Or.inl hp)).trans (h.protectedMemory p hp)

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Traversal
