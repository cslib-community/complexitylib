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

* `Arena.stack_frame`: memory outside `[a.stack, a.stack + a.capacity)` survives a stack-only step.
* `Entry.Stored.of_arena_frame`, `StoredNodes.of_arena_frame`: entry and emitted-node readbacks
  survive a stack-only step.
* `Arena.preserved_of_stack_frame`: the worklist facts preserved by a stack-only step.

These invariant proofs are original.
-/

public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Traversal

open Cslib.WordRAM
open Cslib.Algorithms.ThreeSum.ChanHe (Node)

/-- A step that modifies only the reserved native stack leaves memory outside
`[a.stack, a.stack + a.capacity)` unchanged. -/
theorem Arena.stack_frame (a : Arena) {mem₁ mem₂ : ℕ → ℕ}
    (hframe : Modifies (WordStack.footprint a.stack a.capacity) mem₁ mem₂) (q : ℕ)
    (hq : q < a.stack ∨ a.stack + a.capacity ≤ q) : mem₂ q = mem₁ q := by
  apply hframe
  simp only [WordStack.footprint, Block.mem_footprint, Block.Owns]
  omega

/-- An entry whose arrays avoid `[a.stack, a.floor)` retains its readback across a stack-only
memory modification. -/
theorem Entry.Stored.of_arena_frame {a : Arena} {e : Entry} {mem₁ mem₂ : ℕ → ℕ}
    (hs : e.Stored mem₁) (ha : a.Separated) (har : e.Around a.stack (a.floor - a.stack))
    (hframe : Modifies (WordStack.footprint a.stack a.capacity) mem₁ mem₂) :
    e.Stored mem₂ :=
  hs.of_stack_frame (har.mono_capacity ha.capacity_le_gap) hframe

/-- Emitted pointer-table entries and packed node arrays above `a.floor` retain their readback
across a stack-only memory modification. -/
theorem StoredNodes.of_arena_frame {a : Arena} {ns : List (ℕ × Node)} {mem₁ mem₂ : ℕ → ℕ}
    (ho : StoredNodes a.U a.N a.table ns mem₁) (ha : a.Separated)
    (hb : ∀ i : Fin ns.length, a.floor ≤ ns[i.val].1)
    (hframe : Modifies (WordStack.footprint a.stack a.capacity) mem₁ mem₂) :
    StoredNodes a.U a.N a.table ns mem₂ := by
  refine ho.congr (fun q _ _ => a.stack_frame hframe q (Or.inr (by have := ha.2.1; omega)))
    fun i _ _ => a.stack_frame hframe _ (Or.inr ?_)
  have hi := hb i
  have ht := ha.2.1
  have hf := ha.2.2.1
  omega

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
  have hmem := a.stack_frame hframe
  exact ⟨hheap, hregs _ (by decide) (by decide), hc.of_regs_71_96 hregs, hmem,
    ha.capacity_le_gap, fun d hd => (hs d hd).of_arena_frame ha (har d hd) hframe,
    fun d hd j => hheap ▸ hen d hd j,
    fun q hq => (hmem _ (Or.inl (by have := ha.1; omega))).trans (hb q hq), hheap ▸ hfl⟩

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Traversal
