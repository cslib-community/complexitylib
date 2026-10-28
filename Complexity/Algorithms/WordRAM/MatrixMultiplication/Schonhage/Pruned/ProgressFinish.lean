/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Progress
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Finish

/-!
# Returning from a completed native internal node

## Main results

* `PrunedQuery.exec_progress_finish`: the native exhausted-term branch returns the existing
  pruned values and all frame, cursor and timestamp conclusions used by the parent.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- All ten stored partial sums give the existing `Pruned.result`. The native final dispatch
and pop change registers only, stopping at the root and resuming accumulation at a parent. -/
theorem exec_progress_finish {w L f a0 b0 n d p E : ℕ}
    (S : Finset (OutStr (n + 1))) (a b : Leaf (n + 1) → ℤ) (x y : Data registers)
    (hx : NodeReady L f a0 b0 (n + 1) d p E S x)
    (hy : NodeProgress L f a0 b0 n d p E S a b x 10 y)
    (hfit : Fits w (nodeBudget L f a0 b0 E (n + 1))) :
    ∃ z, ExecWithin w step y z 26 ∧ NodeResult L f a0 b0 (n + 1) d E S a b x z := by
  have hd : d ≤ L := by have := hx.depth_add; omega
  obtain ⟨z, hz, hregs, hmem, hlevel, hmode, hactive, hepoch⟩ :=
    exec_node_finish y hy.regs hy.level_eq hd hy.mode_eq (hy.frame 3)
      (hfit.of_le (by unfold nodeBudget; omega))
  refine ⟨z, hz, ⟨hregs, hlevel, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro hpos
    simpa only [ite_eq_right (by omega : d ≠ 0)] using hmode
  · simpa only [hy.active_eq] using hactive
  · rw [hepoch]
    exact hy.epoch_le
  · rw [hepoch]
    exact hy.epoch_upper.trans (Nat.add_le_add_left (epochAllowance_succ n) E)
  · intro q hq
    rw [hmem, hepoch]
    exact hy.timestamps q hq
  · intro q hq
    rw [hmem, hy.values q hq, partialValue_ten a b S q hq]
  · simpa only [hmem] using hy.footprint

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery
