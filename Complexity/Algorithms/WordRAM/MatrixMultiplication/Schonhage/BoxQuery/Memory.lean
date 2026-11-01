/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery.Magnitude
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery.StackMemory
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery.Parameters

/-!
# Query readback from a real constructed table

The reusable query reads the original arrays and computed directory/value words.
These pure memory equalities are established by the actual constructor in the
initialized endpoint. Native stack stores lie above these protected ranges.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery

open Cslib.WordRAM Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Actual source-array and compact-table words consumed by the reusable native query. -/
structure Readback {L : ℕ} (m t D V AA BB : ℕ) (a b : Leaf L → ℤ) (μ : ℕ → ℕ) : Prop where
  /-- The original left encoding words. -/
  left : ∀ i : Fin (10 ^ L), μ (AA + i.val) = Signed.encode (a (BoxTable.leafAt i))
  /-- The original right encoding words. -/
  right : ∀ i : Fin (10 ^ L), μ (BB + i.val) = Signed.encode (b (BoxTable.leafAt i))
  /-- Every actually computed directory word, including zero invalid entries. -/
  directory : ∀ s < (m - t + 1) * 10 ^ L, μ (D + s) = BoxTable.directoryWord L (m - t) s
  /-- Every compact signed value written by the actual table routine. -/
  values : ∀ s < (m - t + 1) * 10 ^ L, BoxTable.Eligible L (m - t) s →
    μ (V + Nat.count (BoxTable.Eligible L (m - t)) s) = Signed.encode (BoxTable.slotValue a b s)

/-- Native scratch writes above the protected ranges preserve actual table/source readback. -/
theorem Readback.transport {L m t D V AA BB F : ℕ} {a b : Leaf L → ℤ}
    {μ ν : ℕ → ℕ} (h : Readback m t D V AA BB a b μ)
    (hA : AA + 10 ^ L ≤ F) (hB : BB + 10 ^ L ≤ F)
    (hD : D + (m - t + 1) * 10 ^ L ≤ F) (hV : V + (boxes L m t).card ≤ F)
    (hf : ∀ q < F, ν q = μ q) : Readback m t D V AA BB a b ν := by
  constructor
  · intro i
    rw [hf _ (by have := i.isLt; omega)]
    exact h.left i
  · intro i
    rw [hf _ (by have := i.isLt; omega)]
    exact h.right i
  · intro s hs
    rw [hf _ (by omega)]
    exact h.directory s hs
  · intro s hs hv
    have hr := Nat.count_strict_mono hv hs
    rw [BoxTable.count_eligible_eq_card_boxes] at hr
    rw [hf _ (by omega)]
    exact h.values s hs hv

/-- A valid canonical key has a positive actual directory rank and exact signed stored value. -/
theorem Readback.key {L m t D V AA BB : ℕ} {a b : Leaf L → ℤ} {μ : ℕ → ℕ}
    (h : Readback m t D V AA BB a b μ) (π : Cube L) (hπ : IsBox m t π) :
    let s := BoxTable.cubeSlot π
    let r := Nat.count (BoxTable.Eligible L (m - t)) s
    s < (m - t + 1) * 10 ^ L ∧ r < (boxes L m t).card ∧
      μ (D + s) = r + 1 ∧ μ (V + r) = Signed.encode
        (boxValue a b π.starLevels.card π) := by
  let s := BoxTable.cubeSlot π
  have hs : s < (m - t + 1) * 10 ^ L := BoxTable.cubeSlot_lt hπ
  have hv : BoxTable.Eligible L (m - t) s := BoxTable.eligible_cubeSlot hπ
  have hr := Nat.count_strict_mono hv hs
  rw [BoxTable.count_eligible_eq_card_boxes] at hr
  refine ⟨hs, hr, ?_, ?_⟩
  · rw [h.directory s hs, BoxTable.directoryWord, ite_eq_left hv]
  · rw [h.values s hs hv, BoxTable.slotValue, BoxTable.slotCube_cubeSlot hπ]
    change Signed.encode (boxValue a b (BoxTable.recordStars L (BoxTable.cubeSlot π)) π) = _
    rw [BoxTable.cubeSlot, BoxTable.recordStars_slot]

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery
