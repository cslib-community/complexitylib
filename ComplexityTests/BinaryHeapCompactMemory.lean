/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.DataStructure.PriorityQueue.BinaryHeap.Memory
import Mathlib.Tactic.NormNum

/-! Compact heap storage retains the legacy footprint and local-zero admission edge cases.
These are source representation and real source-method tests, not a native initialization clock.
No global zero-above or arbitrary-dirty constant-time clearing is assumed. -/

namespace ComplexityTests.BinaryHeapCompactMemory

open Cslib.WordRAM Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.PriorityQueue Cslib.DataStructure.PriorityQueue.BinaryHeap.Memory
open Cslib.DataStructure.PriorityQueue.BinaryHeap (space)

private abbrev layout := compactLayout 1 3
private def mem (a : ℕ) : ℕ := if a = 0 ∨ a = 100 then 7 else 0
private def initial : Memory.State := ⟨mem, 7⟩

-- Size occupies the unused heap[0]; key[0], heap[1] and pos[0] remain distinct.
example : layout.size.base = 4 ∧ layout.key.base = 3 ∧
    layout.heap.base + 1 = 5 ∧ layout.pos.base = 6 := by decide +kernel

example : layout.footprint = (Block.mk 3 (space 1)).footprint := compactLayout_footprint 1 3

private theorem valid : layout.Valid 3 3 := valid_compactLayout (by decide) (by decide)

private theorem allocated : (Block.mk 3 (space 1)).Allocated initial := by
  change 3 + (3 * 1 + 1) ≤ 7
  decide

private theorem local_zero (a : ℕ) (ha : (Block.mk 3 (space 1)).Owns a) : mem a = 0 := by
  simp only [Block.Owns, space] at ha
  simp only [mem]
  split_ifs <;> omega

private theorem empty_inv : Inv layout initial ∧ abs layout initial = IndexedMinPQ.empty 1 :=
  inv_compactLayout allocated local_zero

example : ¬ZeroAbove initial := by
  intro hz
  have h := hz 100 (by decide)
  norm_num [initial, mem] at h

-- The original general source-correctness theorem now applies to the compact local instance.
example : Triple 3 initial (insert layout 0 3) (8 * Nat.log 2 1 + 9)
    (Post layout initial (.insert 0 3)) := by
  apply insert_triple valid empty_inv.1 (v := 0) (k := 3)
  rw [empty_inv.2]
  simp [IndexedMinPQ.valid, IndexedMinPQ.empty]

-- The actual source methods work with the size aliased to heap[0], without another cell.
private def roundTrip : Memory.Prog (Option (Fin 1 × ℕ)) := do
  insert layout 0 3
  extractMin layout

example : (Memory.spec 3).clientResult initial roundTrip = some (0, 3) := by decide +kernel
example : ((Memory.spec 3).clientState initial roundTrip).mem 0 = 7 ∧
    ((Memory.spec 3).clientState initial roundTrip).mem 100 = 7 ∧
    ((Memory.spec 3).clientState initial roundTrip).frontier = 7 := by decide +kernel

-- A stale position is not silently accepted as a freshly initialized empty heap.
example : ¬Inv layout ⟨Function.update mem 6 1, 7⟩ := by
  intro h
  have hp := h.heap.pos_le 0 (by decide)
  norm_num [layout, compactLayout, mem] at hp

-- These two widths admit the old exact footprint and reject the extra-cell layout.
example : Fits 3 (3 + space 1) ∧ ¬Fits 3 (3 + 1 + space 1) := by decide +kernel
example : Fits 1 (space 0) ∧ ¬Fits 1 (1 + space 0) := by decide +kernel
example : (compactLayout 0 0).Valid 1 0 := valid_compactLayout (by decide) (by decide)

private def zeroMem (a : ℕ) : ℕ := if a = 2 then 1 else 0
private def zeroState : Memory.State := ⟨zeroMem, 1⟩

example : Inv (compactLayout 0 0) zeroState ∧
    abs (compactLayout 0 0) zeroState = IndexedMinPQ.empty 0 := by
  apply inv_compactLayout
  · change 0 + (3 * 0 + 1) ≤ 1
    decide
  · intro a ha
    simp only [Block.Owns, space] at ha
    simp only [zeroState, zeroMem]
    split_ifs <;> omega

example : (Memory.spec 1).clientResult zeroState (isEmpty (compactLayout 0 0)) = true :=
  by decide +kernel

end ComplexityTests.BinaryHeapCompactMemory
