/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.TraversalFrames

/-!
# Live arrays around the native traversal stack

The word stack occupies a reserved gap between the original arrays and the fresh heap.
Pending arrays lie entirely below the gap or start above it. Actual stack writes therefore
preserve their signed readback. Popping a serialized entry restores its seven registers and
retains every pending array.

## Main definitions

* `Entry.Around`: an array ends below the stack or starts above its reserved end.

## Main results

* `Entry.Stored.of_stack_frame`: stack writes preserve live arrays.
* `pop_entry`: the actual seven-pop program restores the semantic entry.

These memory-layout and composition proofs are original.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Traversal

open Cslib.WordRAM

/-- Every column lies entirely on one side of the reserved stack interval. -/
def Entry.Around (e : Entry) (base capacity : ℕ) : Prop :=
  ∀ j, e.source j + (e.data j).length ≤ base ∨ base + capacity ≤ e.source j

/-- Avoiding a larger reserved gap also avoids each smaller gap with the same base. -/
theorem Entry.Around.mono_capacity {e : Entry} {base small large : ℕ}
    (h : e.Around base large) (hle : small ≤ large) : e.Around base small := by
  intro j
  rcases h j with hj | hj
  · exact Or.inl hj
  · exact Or.inr (by omega)

/-- A concrete stack frame cannot alter any live column around its reserved interval. -/
theorem Entry.Stored.of_stack_frame {e : Entry} {before after : ℕ → ℕ}
    {base capacity : ℕ} (h : e.Stored before) (hg : e.Around base capacity)
    (hf : Modifies (Stack.footprint base capacity) before after) : e.Stored after := by
  apply h.congr
  intro j i hi
  apply hf
  simp only [Stack.footprint, Block.mem_footprint, Block.Owns]
  rcases hg j with hj | hj <;> omega

/-- A newly allocated heavy block remains above the stack; untouched columns retain their gap. -/
theorem Entry.Around.child {e : Entry} {base capacity p : ℕ} (h : e.Around base capacity)
    (j : Fin 3) (zs : List ℤ) (hp : base + capacity ≤ p) :
    (e.child j p zs).Around base capacity := by
  intro k
  by_cases he : k = j
  · subst k
    exact Or.inr (by simpa only [Entry.child, Function.update_self] using hp)
  · simpa only [Entry.child, Function.update_of_ne he] using h k

/-- Actual native popping restores the semantic entry, preserves the remaining stack and
changes memory only inside the reserved stack interval. -/
theorem pop_entry {w base capacity : ℕ} (x : Data 128) (e : Entry) (es : List Entry)
    (h2 : Fits w 2) (hcap : Fits w (base + capacity))
    (hr : Stack.Rep w base capacity ((e :: es).flatMap Entry.words) (x.comap registers)) :
    ∃ y, Exec w popFrame x y 99 ∧
      Stack.Rep w base capacity (es.flatMap Entry.words) (y.comap registers) ∧
      e.Loaded y ∧ Modifies (Stack.footprint base capacity) x.mem y.mem ∧
      ∀ j, Outside j → (j.val < 64 ∨ 71 ≤ j.val) → y.regs j = x.regs j := by
  let a : Fin 7 → ℕ := ![e.fuel, e.source 0, (e.data 0).length, e.source 1,
    (e.data 1).length, e.source 2, (e.data 2).length]
  have hrep : Stack.Rep w base capacity
      ([a 0, a 1, a 2, a 3, a 4, a 5, a 6] ++ es.flatMap Entry.words)
      (x.comap registers) := by
    simpa +decide [a, List.flatMap_cons, Entry.words] using hr
  obtain ⟨y, hy, hry, hslots, hframe, hp⟩ := popFrame_exec x _ a h2 hcap hrep
  refine ⟨y, hy, hry, ⟨hslots 0, ?_, ?_⟩, hframe, hp⟩
  · intro j
    fin_cases j
    · exact hslots 1
    · exact hslots 3
    · exact hslots 5
  · intro j
    fin_cases j
    · exact hslots 2
    · exact hslots 4
    · exact hslots 6

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Traversal
