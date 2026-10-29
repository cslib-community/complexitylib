/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.Frontend.Layout

/-!
# Preserving complete frontend output

Later native programs may allocate beyond the frontend's endpoint. Its exact descriptor and
payload interpretation survives a frame on the concrete allocated prefix.

## Main results

* `Output.frame`: preserve all descriptors and compact payloads below the frontend endpoint.

This memory-frame bridge is original and reuses the existing output and block predicates.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.Frontend

open Cslib.WordRAM

/-- A frame on the frontend allocation preserves every descriptor and actual payload word. -/
theorem Output.frame {l : Layout} {U : ℕ} {rs : List (ℕ × ℕ)} {before after : ℕ → ℕ}
    (h : Output l U rs before) (hcard : rs.length ≤ l.n)
    (hp : ∀ p < l.endpoint, after p = before p) : Output l U rs after := by
  intro j hj
  have hlen : (Math.array U l.digits rs j).length ≤ l.capacity :=
    (Math.length_array_le U l.digits rs j).trans (by dsimp only [Layout.capacity]; omega)
  have hend : l.pointer j + (Math.array U l.digits rs j).length ≤ l.endpoint := by
    calc l.pointer j + (Math.array U l.digits rs j).length
        ≤ l.pointer j + l.capacity := Nat.add_le_add_left hlen _
      _ = l.pointer (j + 1) := (l.pointer_succ j).symm
      _ ≤ l.pointer l.arrays := l.pointer_mono (by omega)
  have hdesc := l.descriptor_before hj j
  refine ⟨?_, ?_, (h j hj).2.2.frame ?_⟩
  · exact (hp _ (by omega)).trans (h j hj).1
  · exact (hp _ (by omega)).trans (h j hj).2.1
  · intro p _ hlt
    exact hp p (by omega)

end Cslib.Algorithms.WordRAM.ThreeSum.Frontend
