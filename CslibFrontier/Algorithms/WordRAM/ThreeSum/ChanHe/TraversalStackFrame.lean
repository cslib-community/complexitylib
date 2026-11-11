/-
Copyright (c) 2026 Erik Demaine, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ThreeSum.ChanHe.TraversalInvariant

/-!
# Worklist facts that survive a stack-only native step

Popping a pending entry changes memory only inside the reserved native stack and keeps the
persistent caller registers `71`–`95`. The worklist facts shared by the catalogue and visitor
cursors therefore transfer to the popped state: the heap pointer and the floor below it, the
output-count register, the caller controls, memory outside the reserved interval, the prime
bitmap, and the readback and heap bounds of the pending entries. The lemma also records that the
reserved stack fits in the gap below the floor. Callers still derive the other invariant fields,
such as the output and its bounds, the heap budget and protected memory.

Both the native traversal and the fused decision visitor pop an entry before each transition,
so they share this argument.

## Main results

* `Arena.preserved_of_stack_frame`: the worklist facts preserved by a stack-only step.

These invariant proofs are original.
-/

public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Traversal

open Cslib.WordRAM

/-- A step that changes memory only inside the reserved native stack and keeps the persistent
caller registers `71`–`95` preserves the worklist facts shared by the catalogue and visitor
cursors. For the entries `es`, the conclusions are, in order:

* the heap pointer and output count are unchanged;
* the caller controls still hold;
* memory below the stack and above its reserved interval is unchanged;
* the reserved stack fits inside the gap below the heap floor;
* each entry keeps its exact readback;
* each entry still lies below the fresh heap;
* the prime bitmap is still represented;
* the heap pointer stays above the floor. -/
theorem Arena.preserved_of_stack_frame {a : Arena} {es : List Entry} (x y : Data 128)
    (ha : a.Separated) (hc : a.Controls x) (hb : a.Bitmap x.mem)
    (hs : ∀ d ∈ es, d.Stored x.mem) (har : ∀ d ∈ es, d.Around a.stack (a.floor - a.stack))
    (hen : ∀ d ∈ es, ∀ j, d.source j + (d.data j).length ≤ x.regs heap)
    (hfl : a.floor ≤ x.regs heap)
    (hframe : Modifies (WordStack.footprint a.stack a.capacity) x.mem y.mem)
    (hregs : ∀ i : Fin 128, 71 ≤ i.val → i.val < 96 → y.regs i = x.regs i) :
    y.regs heap = x.regs heap ∧ y.regs outputCount = x.regs outputCount ∧ a.Controls y ∧
      (∀ q, q < a.stack ∨ a.stack + a.capacity ≤ q → y.mem q = x.mem q) ∧
      a.capacity ≤ a.floor - a.stack ∧ (∀ d ∈ es, d.Stored y.mem) ∧
      (∀ d ∈ es, ∀ j, d.source j + (d.data j).length ≤ y.regs heap) ∧
      a.Bitmap y.mem ∧ a.floor ≤ y.regs heap := by
  have hheap : y.regs heap = x.regs heap := hregs _ (by decide) (by decide)
  have hmem (q : ℕ) (hq : q < a.stack ∨ a.stack + a.capacity ≤ q) : y.mem q = x.mem q := by
    apply hframe
    simp only [WordStack.footprint, Block.mem_footprint, Block.Owns]
    omega
  have gap : a.capacity ≤ a.floor - a.stack := by
    have ht := ha.2.1
    have hf := ha.2.2.1
    omega
  refine ⟨hheap, hregs _ (by decide) (by decide), hc.congr ?_, hmem, gap,
    fun d hd => (hs d hd).of_stack_frame ((har d hd).mono_capacity gap) hframe, ?_, ?_, ?_⟩
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    exact hregs i (by omega) (by omega)
  · intro d hd j
    rw [hheap]
    exact hen d hd j
  · intro q hq
    rw [hmem _ (Or.inl (by have := ha.1; omega))]
    exact hb q hq
  · rw [hheap]
    exact hfl

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Traversal
