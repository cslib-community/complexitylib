/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

-- upstream: local-only (tests)

import CslibFrontier.Computability.WordRAM.MemoryView
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.ScanMemory

/-!
# Semantic views, dirty memory, overlap and exact frame boundaries

These examples use ordinary imports and actual stores. Two read-only lists overlap, but stores
at their common endpoint retain both. Writing an occupied cell corrupts its represented value.
A timestamped matrix-query list retains its membership interpretation through a frame chain;
its unoccupied list cells and old timestamps remain dirty.
-/

namespace ComplexityTests.WordRAMMemoryViews

open Cslib.WordRAM
open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery

private def dirty (a : ℕ) : ℕ := if a = 4 then 7 else if a = 5 then 8 else 913

private theorem words : Block.HoldsList 4 [7, 8] dirty := by
  intro i
  fin_cases i <;> rfl

-- An empty block owns no cells, including its own base address.
example : Block.HoldsList 4 [] (Function.update dirty 4 777) := by
  have h := Block.holdsList_nil 4 dirty
  ram_keep h

-- The aliased suffix is a second view of the same live cell, not a separation premise.
example : Block.HoldsList 4 [7, 8] (Function.update dirty 6 999) ∧
    Block.HoldsList 5 [8] (Function.update dirty 6 999) := by
  constructor
  · ram_keep words
  · have h : Block.HoldsList 5 [8] dirty := by intro i; fin_cases i; rfl
    ram_keep h

-- Different write regions compose; no value is prescribed for either dirty written cell.
example : Block.HoldsList 4 [7, 8]
    (Function.update (Function.update dirty 6 999) 9 777) := by
  have hm := (Modifies.update dirty 6 999).trans
    (Modifies.update (Function.update dirty 6 999) 9 777)
  have hf : Set.EqOn (Function.update (Function.update dirty 6 999) 9 777) dirty
      (Set.Iio 6) := hm.eqOn (by
    apply Set.disjoint_left.mpr
    intro a ha hw
    have hw' : a = 6 ∨ a = 9 := by simpa using hw
    change a < 6 at ha
    omega)
  ram_keep words using hf

-- The endpoint belongs to the dirty tail; its predecessor is still a required live cell.
example : ¬Block.HoldsList 4 [7, 8] (Function.update dirty 5 99) := by
  fail_if_success
    have bad : Block.HoldsList 4 [7, 8] (Function.update dirty 5 99) := by ram_keep words
  intro h
  have hv := h.get 1 (by decide)
  norm_num at hv

example : ¬Set.EqOn (Function.update dirty 5 99) dirty (Set.Iio 6) := by
  intro h
  have hv := h (show (5 : ℕ) ∈ Set.Iio 6 by decide)
  norm_num [dirty] at hv

private def oldStamps (_ : ℕ) : ℕ := 41

private theorem emptyScan : ScanMemory oldStamps 10 20 42 3 ∅ :=
  ScanMemory.empty (by intro q _; norm_num [oldStamps])

private def singletonScan : ℕ → ℕ :=
  Function.update (Function.update oldStamps 10 1) 21 42

private theorem singletonView : ScanMemory singletonScan 10 20 42 3 {1} := by
  simpa only [Finset.insert_empty, Finset.card_empty, Nat.add_zero, Nat.reduceAdd,
    singletonScan] using
    emptyScan.insert_new (q := 1) (by decide) (by simp) (Or.inl (by decide))

-- The list tail at 11 is outside the occupied view, while every directory cell is retained.
example : ScanMemory (Function.update (Function.update singletonScan 11 888) 23 999)
    10 20 42 3 {1} := by
  apply singletonView.keep (reads := Set.Ico 10 11 ∪ Set.Ico 20 23)
  · intro a ha
    rcases ha with ha | ha <;>
      rw [Function.update_of_ne (by rcases ha with ⟨hlo, hhi⟩; omega),
        Function.update_of_ne (by rcases ha with ⟨hlo, hhi⟩; omega)]
  · intro a ha
    left
    simpa using ha
  · exact Set.subset_union_right

-- The timestamp is semantically live even when the output list does not occupy its address.
example : ¬ScanMemory (Function.update singletonScan 21 41) 10 20 42 3 {1} := by
  intro h
  have hv := (h.marked 1 (by decide)).mpr (by simp)
  norm_num at hv

end ComplexityTests.WordRAMMemoryViews
