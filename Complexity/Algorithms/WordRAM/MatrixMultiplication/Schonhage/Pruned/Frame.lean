/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Memory

/-!
# Native stack layout and frame loading

## Main results

* `PrunedQuery.exec_locate`: compute the actual stack/list/value/timestamp region addresses.
* `PrunedQuery.exec_loadFrame`: load all four stored frame words and compute row addresses.

Every index multiplication, pointer addition and load is an ordinary charged instruction.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery

open Cslib.WordRAM

/-- Exactly the registers used to locate the concrete workspace regions. -/
def LocateLocal (i : Fin registers) : Prop :=
  i = frames ∨ i = temporary ∨ i = temporary₂ ∨ i = lists ∨ i = values ∨ i = stamps

instance (i : Fin registers) : Decidable (LocateLocal i) :=
  inferInstanceAs (Decidable
    (i = frames ∨ i = temporary ∨ i = temporary₂ ∨ i = lists ∨ i = values ∨ i = stamps))

private theorem locate_preserves (i : Fin registers) :
    ¬LocateLocal i → locate.Preserves i := by decide +kernel +revert

/-- The seven actual instructions compute the workspace partition from depth and array size. -/
theorem exec_locate {w : ℕ} (x : Data registers) (h1 : x.regs one = 1)
    (h4 : x.regs frameWidth = 4)
    (hw : Fits w (x.regs scratch + 4 * (x.regs inputDepth + 1) +
      2 * (x.regs inputDepth + 1) * x.regs span + x.regs inputDepth + 8)) :
    ∃ y, ExecWithin w locate x y 7 ∧ y.mem = x.mem ∧
      y.regs frames = x.regs scratch ∧
      y.regs lists = x.regs scratch + 4 * (x.regs inputDepth + 1) ∧
      y.regs values = x.regs scratch + 4 * (x.regs inputDepth + 1) +
        (x.regs inputDepth + 1) * x.regs span ∧
      y.regs stamps = x.regs scratch + 4 * (x.regs inputDepth + 1) +
        2 * (x.regs inputDepth + 1) * x.regs span ∧
      (∀ i, ¬LocateLocal i → y.regs i = x.regs i) := by
  let d := x.regs inputDepth + 1
  let b := x.regs scratch + 4 * d
  let v := b + d * x.regs span
  let s := v + d * x.regs span
  let y := (((((((x.set frames (x.regs scratch)).set temporary d).set temporary₂ (4 * d)).set
    lists b).set temporary₂ (d * x.regs span)).set values v).set stamps s)
  have hd : Fits w d := hw.of_le (by dsimp [d]; omega)
  have harea : Fits w (4 * d) := hw.of_le (by dsimp [d]; omega)
  have hb : Fits w b := hw.of_le (by dsimp [b, d]; omega)
  have hds : Fits w (d * x.regs span) := hw.of_le (by dsimp [d]; nlinarith)
  have hv : Fits w v := hw.of_le (by dsimp [v, b, d]; nlinarith)
  have hs : Fits w s := hw.of_le (by dsimp [s, v, b, d]; nlinarith)
  have he : ExecWithin w locate x y 7 := by
    ram_eval [locate, y, d, b, v, s, h1, h4, hd, harea, hb, hds, hv, hs,
      frames, temporary, temporary₂, lists, values, stamps, scratch, inputDepth, frameWidth,
      span, one, Fin.mk.injEq, Nat.mul_comm]
  refine ⟨y, he, rfl, ?_, ?_, ?_, ?_, fun i hi => he.regs_eq (locate_preserves i hi)⟩
  all_goals simp +decide [y, b, d, v, s, frames, temporary, temporary₂, lists, values,
    stamps, two_mul, add_mul, Nat.add_assoc]

/-- Registers written while loading one stack frame and computing the two depth rows. -/
def LoadFrameLocal (i : Fin registers) : Prop :=
  i = frame ∨ i = address ∨ i = count ∨ i = leafPrefix ∨ i = stride ∨ i = term ∨
    i = temporary ∨ i = listBase ∨ i = valueBase ∨ i = nextLevel ∨ i = childList ∨
    i = childValues

instance (i : Fin registers) : Decidable (LoadFrameLocal i) :=
  inferInstanceAs (Decidable
    (i = frame ∨ i = address ∨ i = count ∨ i = leafPrefix ∨ i = stride ∨ i = term ∨
      i = temporary ∨ i = listBase ∨ i = valueBase ∨ i = nextLevel ∨ i = childList ∨
      i = childValues))

private theorem loadFrame_preserves (i : Fin registers) :
    ¬LoadFrameLocal i → loadFrame.Preserves i := by decide +kernel +revert

/-- Seventeen native instructions load the four words at the computed frame address and
locate the current and child rows. The memory words are read, not supplied as frame arguments. -/
theorem exec_loadFrame {w : ℕ} (x : Data registers) (h1 : x.regs one = 1)
    (h4 : x.regs frameWidth = 4)
    (hw : Fits w (x.regs frames + 4 * (x.regs level + 1) + x.regs lists +
      x.regs values + (x.regs level + 1) * x.regs span + x.regs level + 8)) :
    ∃ y, ExecWithin w loadFrame x y 17 ∧ y.mem = x.mem ∧
      y.regs frame = x.regs frames + 4 * x.regs level ∧
      y.regs count = x.mem (x.regs frames + 4 * x.regs level) ∧
      y.regs leafPrefix = x.mem (x.regs frames + 4 * x.regs level + 1) ∧
      y.regs stride = x.mem (x.regs frames + 4 * x.regs level + 2) ∧
      y.regs term = x.mem (x.regs frames + 4 * x.regs level + 3) ∧
      y.regs listBase = x.regs lists + x.regs level * x.regs span ∧
      y.regs valueBase = x.regs values + x.regs level * x.regs span ∧
      y.regs nextLevel = x.regs level + 1 ∧
      y.regs childList = x.regs lists + (x.regs level + 1) * x.regs span ∧
      y.regs childValues = x.regs values + (x.regs level + 1) * x.regs span ∧
      (∀ i, ¬LoadFrameLocal i → y.regs i = x.regs i) := by
  let f := x.regs frames + x.regs level * 4
  let j := x.regs level + 1
  let y := (((((((((((((((((x.set frame (x.regs level * 4)).set frame f).set address f).set
    count (x.mem f)).set address (f + 1)).set leafPrefix (x.mem (f + 1))).set
    address (f + 2)).set stride (x.mem (f + 2))).set address (f + 3)).set
    term (x.mem (f + 3))).set temporary (x.regs level * x.regs span)).set
    listBase (x.regs lists + x.regs level * x.regs span)).set
    valueBase (x.regs values + x.regs level * x.regs span)).set nextLevel j).set
    temporary (j * x.regs span)).set childList (x.regs lists + j * x.regs span)).set
    childValues (x.regs values + j * x.regs span))
  have hlev : Fits w (x.regs level * 4) := hw.of_le (by omega)
  have hf (k : ℕ) (hk : k ≤ 3) : Fits w (f + k) := hw.of_le (by dsimp [f]; omega)
  have hf0 : Fits w (x.regs frames + x.regs level * 4) := by
    simpa only [f, Nat.add_zero] using hf 0 (by decide)
  have hj : Fits w (x.regs level + 1) := hw.of_le (by omega)
  have hprod : Fits w (x.regs level * x.regs span) := hw.of_le (by nlinarith)
  have hnextprod : Fits w ((x.regs level + 1) * x.regs span) := hw.of_le (by nlinarith)
  have hl : Fits w (x.regs lists + x.regs level * x.regs span) := hw.of_le (by nlinarith)
  have hv : Fits w (x.regs values + x.regs level * x.regs span) := hw.of_le (by nlinarith)
  have hcl : Fits w (x.regs lists + (x.regs level + 1) * x.regs span) := hw.of_le (by nlinarith)
  have hcv : Fits w (x.regs values + (x.regs level + 1) * x.regs span) := hw.of_le (by nlinarith)
  have hexact : Exec w loadFrame x y 17 := by
    ram_eval [loadFrame, y, f, j, h1, h4, hlev, hf0, hf 1 (by decide),
      hf 2 (by decide), hf 3 (by decide), hj, hprod, hnextprod, hl, hv, hcl, hcv,
      frame, address, count, leafPrefix, stride, term, temporary, listBase, valueBase,
      nextLevel, childList, childValues, level, span, frames, lists, values, frameWidth, one,
      Fin.mk.injEq, Nat.add_zero]
  have he : ExecWithin w loadFrame x y 17 := ⟨17, le_rfl, hexact⟩
  refine ⟨y, he, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun i hi => he.regs_eq (loadFrame_preserves i hi)⟩
  all_goals simp +decide [y, f, j, frame, address, count, leafPrefix, stride, term, temporary,
    listBase, valueBase, nextLevel, childList, childValues, Nat.mul_comm]

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery
