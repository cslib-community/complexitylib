/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.ScanMemory
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.ScanStep

/-!
# Query-set meaning of an actual native scan step

## Main results

* `PrunedQuery.exec_scanInsert`: the native filter and timestamp comparisons compute exactly
  a finite-set insertion, preserving the list/directory invariant and the outside memory frame.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery

open Cslib.WordRAM

/-- One charged native step computes its set insertion from the loaded source word and the
actual timestamp. `S` describes the current memory, rather than supplying a decision oracle. -/
theorem exec_scanInsert {w capacity : ℕ} (child : Bool) (x : Data registers) (S : Finset ℕ)
    (q : ℕ) (hq : x.mem (x.regs listBase + x.regs index) = q)
    (hcount : x.regs childCount = S.card)
    (htable : ScanMemory x.mem (x.regs childList) (x.regs stamps) (x.regs epoch) capacity S)
    (hcode : shortened child q < capacity)
    (hsep : x.regs childList + capacity ≤ x.regs stamps ∨
      x.regs stamps + capacity ≤ x.regs childList)
    (h1 : x.regs one = 1) (h10 : x.regs ten = 10) (h9 : x.regs nine = 9)
    (h10fit : Fits w 10) (hread : Fits w (x.regs listBase + x.regs index))
    (hs : Fits w (x.regs stamps + shortened child q))
    (hl : Fits w (x.regs childList + x.regs childCount))
    (hn : Fits w (x.regs childCount + 1)) (hi : Fits w (x.regs index + 1)) :
    ∃ y, ExecWithin w (scanStep child) x y 18 ∧ y.regs index = x.regs index + 1 ∧
      y.regs childCount = (if selected child (x.regs term) q then
        insert (shortened child q) S else S).card ∧
      ScanMemory y.mem (x.regs childList) (x.regs stamps) (x.regs epoch) capacity
        (if selected child (x.regs term) q then insert (shortened child q) S else S) ∧
      (∀ a, ¬(Block.mk (x.regs childList) capacity).Owns a →
        ¬(Block.mk (x.regs stamps) capacity).Owns a → y.mem a = x.mem a) ∧
      (∀ i, ¬ScanStepLocal i → y.regs i = x.regs i) := by
  obtain ⟨y, he, hindex, hc, hm, hf⟩ := exec_scanStep child x q hq h1 h10 h9
    h10fit hread hs hl hn hi
  have hseen := htable.marked (shortened child q) hcode
  refine ⟨y, he, hindex, ?_, ?_, ?_, hf⟩
  · by_cases hsel : selected child (x.regs term) q
    · by_cases hmem : shortened child q ∈ S
      · simpa [hsel, hmem, hseen.mpr hmem, hcount] using hc
      · have hmark : x.mem (x.regs stamps + shortened child q) ≠ x.regs epoch :=
          fun h => hmem (hseen.mp h)
        simpa [hsel, hmem, hmark, hcount] using hc
    · simpa [hsel, hcount] using hc
  · by_cases hsel : selected child (x.regs term) q
    · by_cases hmem : shortened child q ∈ S
      · simpa [hm, hsel, hmem, hseen.mpr hmem] using htable
      · have hmark : x.mem (x.regs stamps + shortened child q) ≠ x.regs epoch :=
          fun h => hmem (hseen.mp h)
        simpa [hm, hsel, hmark, hcount] using htable.insert_new hcode hmem hsep
    · simpa [hm, hsel] using htable
  · intro a hout hstamp
    rw [hm]
    split_ifs with hnew
    · have hmem : shortened child q ∉ S := fun h => hnew.2 (hseen.mpr h)
      have hcapa := htable.card_lt_of_notMem hcode hmem
      have hao : a ≠ x.regs childList + x.regs childCount := by
        intro ha
        apply hout
        rw [ha, hcount]
        change x.regs childList ≤ x.regs childList + S.card ∧
          x.regs childList + S.card < x.regs childList + capacity
        exact ⟨by omega, by omega⟩
      have has : a ≠ x.regs stamps + shortened child q := by
        intro ha
        apply hstamp
        rw [ha]
        change x.regs stamps ≤ x.regs stamps + shortened child q ∧
          x.regs stamps + shortened child q < x.regs stamps + capacity
        exact ⟨by omega, by omega⟩
      simp only [Function.update_of_ne has, Function.update_of_ne hao]
    · rfl

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery
