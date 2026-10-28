/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Scan
public import Complexity.Computability.WordRAM.Heap

/-!
# Initialization of the actual root stack frame

## Main results

* `PrunedQuery.exec_rootFinish`: write the computed root count and enter its first phase.

The count comes from the preceding native deduplication. The frame words are ordinary stores,
not an externally supplied traversal certificate.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery

open Cslib.WordRAM

/-- Registers assigned after the actual root query list has been computed. -/
def RootFinishLocal (i : Fin registers) : Prop :=
  i = address ∨ i = level ∨ i = mode ∨ i = active

instance (i : Fin registers) : Decidable (RootFinishLocal i) :=
  inferInstanceAs (Decidable (i = address ∨ i = level ∨ i = mode ∨ i = active))

private theorem rootFinish_preserves (i : Fin registers) :
    ¬RootFinishLocal i → rootFinish.Preserves i := by decide +kernel +revert

/-- Eleven native instructions write the root's computed count, zero prefix, unit stride and
zero term, then set the controller to its entry phase. -/
theorem exec_rootFinish {w : ℕ} (x : Data registers) (h0 : x.regs nil = 0)
    (h1 : x.regs one = 1) (hw : Fits w (x.regs frames + 3)) :
    ∃ y, ExecWithin w rootFinish x y 11 ∧ y.regs level = 0 ∧ y.regs mode = 0 ∧
      y.regs active = 1 ∧
      y.mem = Function.update (Function.update (Function.update (Function.update x.mem
        (x.regs frames) (x.regs childCount)) (x.regs frames + 1) 0)
        (x.regs frames + 2) 1) (x.regs frames + 3) 0 ∧
      Modifies (Block.mk (x.regs frames) 4).footprint x.mem y.mem ∧
      (∀ i, ¬RootFinishLocal i → y.regs i = x.regs i) := by
  let f := x.regs frames
  let y := (((((((((((x.set address f).write f (x.regs childCount)).set address (f + 1)).write
    (f + 1) 0).set address (f + 2)).write (f + 2) 1).set address (f + 3)).write
    (f + 3) 0).set level 0).set mode 0).set active 1)
  have hconst : Fits w 1 := hw.of_le (by omega)
  have hf1 : Fits w (x.regs frames + 1) := hw.of_le (by omega)
  have hf2 : Fits w (x.regs frames + 2) := hw.of_le (by omega)
  have he : ExecWithin w rootFinish x y 11 := by
    ram_eval [rootFinish, y, f, h0, h1, hw, hconst, hf1, hf2, address, level, mode, active,
      one, nil, childCount, frames, Fin.mk.injEq]
  refine ⟨y, he, ?_, ?_, by simp [y], rfl, ?_,
    fun i hi => he.regs_eq (rootFinish_preserves i hi)⟩
  · simp +decide [y, active, mode, level]
  · simp +decide [y, active, mode]
  · intro a ha
    have hnot : ¬(f ≤ a ∧ a < f + 4) := by
      simpa only [Block.mem_footprint, Block.Owns, f, Block.base, Block.length] using ha
    have h0' : a ≠ f := by omega
    have h1' : a ≠ f + 1 := by omega
    have h2' : a ≠ f + 2 := by omega
    have h3' : a ≠ f + 3 := by omega
    simp only [y, Data.set_mem, Data.write_mem, Function.update_of_ne h3',
      Function.update_of_ne h2', Function.update_of_ne h1', Function.update_of_ne h0']

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery
