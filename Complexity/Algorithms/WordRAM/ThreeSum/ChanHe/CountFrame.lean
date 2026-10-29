/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.Count

/-!
# Collision-counting register and memory frames

Prime-search clients reuse the same fixed counting program on successive candidates.
Its input parameters and all memory below its scratch blocks are preserved.

## Main results

* `Count.memory_before`: cells below the two workspace blocks retain their contents.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Count

open Cslib.WordRAM

/-- Neither the residue array nor the histogram modifies an earlier memory cell. -/
theorem memory_before (mem : ℕ → ℕ) (values : ℕ → ℤ) (n M scratch dst a : ℕ)
    (hs : a < scratch) (hd : a < dst) : memory mem values n M scratch dst a = mem a := by
  simp [memory, Histogram.memory, Residues.memory, show ¬(dst ≤ a ∧ a < dst + M) by omega,
    show ¬(scratch ≤ a ∧ a < scratch + n) by omega]

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Count
