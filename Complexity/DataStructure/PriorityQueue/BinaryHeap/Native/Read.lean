/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Realization.Absorb
public import Complexity.Computability.WordRAM.Realization.Reindex
public import Complexity.DataStructure.PriorityQueue.BinaryHeap.Native.Encoding
import Complexity.Tactic.Realize

/-!
# Native read-only memory-heap operations

The original `Memory.isEmpty` and `Memory.getKey` programs are realized over the shared runtime
layout and typed-handle encodings. Both emitters are selected before every layout, handle, word
width and memory. The bounded read and Boolean/optional-result glue are paid by a fixed factor.
No key is shifted to encode absence, so a maximum fitting key remains representable.

## Main results

* `realizes_isEmpty`: the original one-query emptiness test.
* `realizes_getKeyWord`, `realizes_getKey`: the same at-most-two-query lookup for a runtime
  handle word with a visible bound, or for the typed indexed-PQ client.

These certificates assume arguments installed in registers. They neither load an external heap
nor initialize its representation. The heap's existing source correctness remains separate.
-/

@[expose] public section

namespace Cslib.DataStructure.PriorityQueue.BinaryHeap.Native

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure

/-- The original emptiness test with constant native overhead and a runtime layout. -/
theorem realizes_isEmpty :
    Realizes .exact (fun d : HeapLayout => Memory.isEmpty d.2) layoutWords boolWords
      (fun _ d s => d.2.size.length = 1 ∧ d.2.size.Allocated s) (fun _ _ => 0) := by
  have h : Realizes .exact (fun d : HeapLayout => do
      let S ← d.2.size.get 0
      if S = 0 then pure true else pure false) layoutWords boolWords
      (fun _ d s => d.2.size.length = 1 ∧ d.2.size.Allocated s) (fun _ _ => 0) := by
    realize
    all_goals exact h.1 ▸ hwords 2
  exact h.congr fun d => by
    unfold Memory.isEmpty
    congr 1
    funext S
    by_cases hz : S = 0 <;> simp [hz]

/-- The original optional lookup on a runtime handle word. The bound is part of the explicit
entry domain; it is not an input-dependent choice of code or an extra native check. -/
theorem realizes_getKeyWord :
    Realizes .exact (fun d : HeapLayout × ℕ => Memory.getKey d.1.2 d.2) indexWords optionWords
      (fun _ d s => d.2 < d.1.1 ∧ d.1.2.arrays.Allocated s) (fun _ _ => 0) := by
  realize
  all_goals
    first
    | exact hmem.fits_of_lt_frontier (Memory.pos_lt h.2 h.1)
    | exact hmem.fits_of_lt_frontier (Memory.key_lt h.2 h.1)
    | apply hmem.fits_of_lt_frontier
      have hv := h.1
      have hA := h.2
      change d.1.2.base + (3 * d.1.1 + 1) ≤ s.frontier at hA
      omega

/-- The typed indexed-PQ client reuses the word-body certificate by static wiring. Its key is
returned unshifted, including the largest fitting word. -/
theorem realizes_getKey :
    Realizes .exact (fun d : HandleArgument => Memory.getKey d.2.1 d.2.2) handleWords optionWords
      (fun _ d s => d.2.1.arrays.Allocated s) (fun _ _ => 0) := by
  have h := realizes_getKeyWord.reindex
    (fun d : HandleArgument => ((⟨d.1, d.2.1⟩ : HeapLayout), d.2.2.val)) handleWords
    (fun i => i) (by intro d i; rfl)
  exact h.consequence (fun _ d _ _ _ h => ⟨d.2.2.isLt, h⟩) (fun _ _ => le_rfl)

end Cslib.DataStructure.PriorityQueue.BinaryHeap.Native
