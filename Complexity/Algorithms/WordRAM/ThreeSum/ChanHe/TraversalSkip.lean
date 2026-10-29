/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.TraversalInvariant
public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.TraversalStep

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

@[expose] public section

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
  have hreg (i : Fin 128) (hi : 71 ≤ i.val) (hi' : i.val < 96) :
      y.regs i = x.regs i := hp i (Or.inl hi') (Or.inr hi)
  have hheap : y.regs heap = x.regs heap := hreg _ (by decide) (by decide)
  have hcount : y.regs outputCount = x.regs outputCount := hreg _ (by decide) (by decide)
  have hcontrols : a.Controls y := h.controls.congr (by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    exact hreg i (by omega) (by omega))
  have hbody := body_skip hy hloaded hcontrols.2.2.2.2.2.2.2.2.2.1 hskip
  have hmem (p : ℕ) (hp : p < a.stack ∨ a.stack + a.capacity ≤ p) : y.mem p = x.mem p := by
    apply hframe
    simp only [Stack.footprint, Block.mem_footprint, Block.Owns]
    omega
  have hstep : Math.step (Nat.primesLE a.m) a.Λ e.task (es.map Entry.task) =
      (es.map Entry.task, none) := by
    by_cases hf : e.fuel = 0
    · simp only [Math.step, Entry.task, hf]
    · have hempty : e.task.empty := by
        simp only [Math.Task.empty, Entry.task, List.toFinset_eq_empty_iff]
        rcases hskip with hf' | h₀ | h₁ | h₂
        · exact (hf hf').elim
        · exact Or.inl (List.eq_nil_of_length_eq_zero h₀)
        · exact Or.inr (Or.inl (List.eq_nil_of_length_eq_zero h₁))
        · exact Or.inr (Or.inr (List.eq_nil_of_length_eq_zero h₂))
      cases he : e.fuel with
      | zero => exact (hf he).elim
      | succ f => simp only [Math.step, show e.task.fuel = f + 1 from he, hempty, ↓reduceIte]
  have hdec := Math.potential_step (Nat.primesLE a.m) a.Λ e.task (es.map Entry.task)
  rw [hstep] at hdec
  change (Cursor.mk es ns).work + 1 ≤ (Cursor.mk (e :: es) ns).work at hdec
  refine ⟨y, hbody, ?_, by omega⟩
  refine ⟨hbody.bounded h.bounded, hcontrols, ?_, hstack, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hcount.trans h.count, ?_, ?_, ?_, ?_, ?_⟩
  · intro q hq
    rw [hmem _ (Or.inl (by have := ha.1; omega))]
    exact h.bitmap q hq
  · exact h.depth.2
  · intro d hd
    exact h.valid d (List.mem_cons_of_mem e hd)
  · intro d hd
    exact (h.stored d (List.mem_cons_of_mem e hd)).of_stack_frame
      ((h.around d (List.mem_cons_of_mem e hd)).mono_capacity (by
        have ht := ha.2.1
        have hf := ha.2.2.1
        omega)) hframe
  · intro d hd
    exact h.around d (List.mem_cons_of_mem e hd)
  · intro d hd j
    rw [hheap]
    exact h.ends d (List.mem_cons_of_mem e hd) j
  · rw [hheap]
    exact h.floor
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
