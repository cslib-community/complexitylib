/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Control
public import Complexity.Computability.WordRAM.Heap

/-!
# Computed child-frame writes

## Main results

* `PrunedQuery.exec_push`: compute the next stack address, prefix and stride, store all four
  child-frame words, and enter that frame in fifteen native instructions.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery

open Cslib.WordRAM

/-- Registers changed while constructing and entering one child frame. -/
def PushLocal (i : Fin registers) : Prop :=
  i = childFrame ∨ i = temporary₂ ∨ i = childPrefix ∨ i = childStride ∨ i = address ∨
    i = level ∨ i = mode

instance (i : Fin registers) : Decidable (PushLocal i) :=
  inferInstanceAs (Decidable
    (i = childFrame ∨ i = temporary₂ ∨ i = childPrefix ∨ i = childStride ∨ i = address ∨
      i = level ∨ i = mode))

private theorem push_preserves (i : Fin registers) : ¬PushLocal i → push.Preserves i := by
  decide +kernel +revert

/-- The child list's actual count is written to the computed frame, followed by the new leaf
prefix, stride and zero term counter. All scalar fit premises follow from the displayed budget. -/
theorem exec_push {w : ℕ} (x : Data registers) (h0 : x.regs nil = 0)
    (h1 : x.regs one = 1) (h4 : x.regs frameWidth = 4) (h10 : x.regs ten = 10)
    (hw : Fits w (x.regs frames + x.regs nextLevel * 4 + x.regs leafPrefix +
      x.regs term * x.regs stride + x.regs stride * 10 + 8)) :
    ∃ y, ExecWithin w push x y 15 ∧ y.regs level = x.regs nextLevel ∧ y.regs mode = 0 ∧
      y.regs childFrame = x.regs frames + x.regs nextLevel * 4 ∧
      y.regs childPrefix = x.regs leafPrefix + x.regs term * x.regs stride ∧
      y.regs childStride = x.regs stride * 10 ∧
      y.mem = Function.update (Function.update (Function.update (Function.update x.mem
        (x.regs frames + x.regs nextLevel * 4) (x.regs childCount))
        (x.regs frames + x.regs nextLevel * 4 + 1)
          (x.regs leafPrefix + x.regs term * x.regs stride))
        (x.regs frames + x.regs nextLevel * 4 + 2) (x.regs stride * 10))
        (x.regs frames + x.regs nextLevel * 4 + 3) 0 ∧
      Modifies (Block.mk (x.regs frames + x.regs nextLevel * 4) 4).footprint x.mem y.mem ∧
      (∀ i, ¬PushLocal i → y.regs i = x.regs i) := by
  let f := x.regs frames + x.regs nextLevel * 4
  let p := x.regs leafPrefix + x.regs term * x.regs stride
  let s := x.regs stride * 10
  let y := (((((((((((((((x.set childFrame (x.regs nextLevel * 4)).set childFrame f).set
    temporary₂ (x.regs term * x.regs stride)).set childPrefix p).set childStride s).set
    address f).write f (x.regs childCount)).set address (f + 1)).write (f + 1) p).set
    address (f + 2)).write (f + 2) s).set address (f + 3)).write (f + 3) 0).set
    level (x.regs nextLevel)).set mode 0)
  have hprod : Fits w (x.regs nextLevel * 4) := hw.of_le (by omega)
  have hf (k : ℕ) (hk : k ≤ 3) : Fits w (x.regs frames + x.regs nextLevel * 4 + k) :=
    hw.of_le (by omega)
  have hf0 : Fits w (x.regs frames + x.regs nextLevel * 4) := hw.of_le (by omega)
  have ht : Fits w (x.regs term * x.regs stride) := hw.of_le (by omega)
  have hp : Fits w (x.regs leafPrefix + x.regs term * x.regs stride) := hw.of_le (by omega)
  have hs : Fits w (x.regs stride * 10) := hw.of_le (by omega)
  have hexact : Exec w push x y 15 := by
    ram_eval [push, y, f, p, s, h0, h1, h4, h10, hprod, hf0,
      hf 1 (by decide), hf 2 (by decide), hf 3 (by decide), ht, hp, hs,
      childFrame, temporary₂, childPrefix, childStride, address, level, mode, frames,
      nextLevel, leafPrefix, term, stride, ten, one, frameWidth, childCount, nil,
      Fin.mk.injEq, Nat.add_zero]
  have he := hexact.within
  have hmod : Modifies (Block.mk f 4).footprint x.mem y.mem := by
    intro c hc
    have hnot : ¬(f ≤ c ∧ c < f + 4) := by
      simpa only [Block.mem_footprint, Block.Owns, Block.base, Block.length] using hc
    have h0' : c ≠ f := by omega
    have h1' : c ≠ f + 1 := by omega
    have h2' : c ≠ f + 2 := by omega
    have h3' : c ≠ f + 3 := by omega
    simp only [y, Data.set_mem, Data.write_mem, Function.update_of_ne h3',
      Function.update_of_ne h2', Function.update_of_ne h1', Function.update_of_ne h0']
  refine ⟨y, he, ?_, by simp [y], ?_, ?_, ?_, rfl, hmod,
    fun i hi => he.regs_eq (push_preserves i hi)⟩
  all_goals simp +decide [y, f, p, s, childFrame, temporary₂, childPrefix, childStride,
    address, level, mode]

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery
