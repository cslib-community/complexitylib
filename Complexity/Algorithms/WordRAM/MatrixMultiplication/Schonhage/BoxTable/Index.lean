/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable.CatalogueState
import Complexity.Foundations.Data.Nat.RadixUpdate

/-!
# Exact canonical-box indexing of the native directory

Valid directory slots and the existing finite boxes are in bijection. The computed
compact count is therefore the actual box cardinality, not a supplied catalogue size.
The digit-update identity also gives the real child encoding-array index directly.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable

open Finset Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Completed leaf represented by a raw directory slot. -/
@[expose] def completionAt (L s : ℕ) : Leaf L :=
  leafAt ⟨recordCode L s, Nat.mod_lt _ (pow_pos (by decide) L)⟩

/-- Canonical cube represented by the slot's star count and completed leaf. -/
@[expose] def slotCube (L s : ℕ) : Cube L := starLowest (recordStars L s) (completionAt L s)

/-- Recover the unique raw directory slot of a canonical box. -/
@[expose] def cubeSlot {L : ℕ} (π : Cube L) : ℕ :=
  π.starLevels.card * 10 ^ L + (Encoding.leafIndex π.starsToP0).val

@[simp] theorem recordCode_slot {L : ℕ} (e : ℕ) (c : Fin (10 ^ L)) :
    recordCode L (e * 10 ^ L + c.val) = c.val := by
  simp [recordCode, Nat.add_mod, Nat.mod_eq_of_lt c.isLt]

@[simp] theorem recordStars_slot {L : ℕ} (e : ℕ) (c : Fin (10 ^ L)) :
    recordStars L (e * 10 ^ L + c.val) = e := by
  rw [recordStars, Nat.mul_comm e (10 ^ L), Nat.add_comm,
    Nat.add_mul_div_left _ _ (pow_pos (by decide) L),
    Nat.div_eq_of_lt c.isLt, Nat.zero_add]

@[simp] theorem completionAt_slot {L : ℕ} (e : ℕ) (c : Fin (10 ^ L)) :
    completionAt L (e * 10 ^ L + c.val) = leafAt c := by
  simp [completionAt]

private theorem completion_population (L s : ℕ) :
    (P0Levels (completionAt L s)).card = population (recordCode L s) L :=
  (population_eq_card_P0Levels ⟨recordCode L s, Nat.mod_lt _ (pow_pos (by decide) L)⟩).symm

/-- An eligible slot denotes a box with the original finite box predicate. -/
theorem slotCube_isBox {L m t s : ℕ} (h : Eligible L (m - t) s) :
    IsBox m t (slotCube L s) := by
  apply isBox_starLowest
  rw [completion_population]
  exact h.2

/-- Eligibility ensures that starring does not saturate before its supplied star count. -/
theorem slotCube_star_count {L H s : ℕ} (h : Eligible L H s) :
    (slotCube L s).starLevels.card = recordStars L s := by
  rw [slotCube, starLevels_starLowest, card_lowest, completion_population]
  exact min_eq_left h.1

/-- Completing a slot cube recovers its original completed leaf. -/
@[simp] theorem starsToP0_slotCube (L s : ℕ) :
    (slotCube L s).starsToP0 = completionAt L s := starsToP0_starLowest _ _

/-- Recovering an eligible slot's key returns that exact slot. -/
theorem cubeSlot_slotCube {L H s : ℕ} (h : Eligible L H s) :
    cubeSlot (slotCube L s) = s := by
  rw [cubeSlot, slotCube_star_count h, starsToP0_slotCube, completionAt, leafIndex_leafAt]
  simpa only [recordStars, recordCode, Nat.mul_comm] using Nat.div_add_mod s (10 ^ L)

/-- Every finite box has a raw slot in the allocated directory. -/
theorem cubeSlot_lt {L m t : ℕ} {π : Cube L} (hπ : IsBox m t π) :
    cubeSlot π < (m - t + 1) * 10 ^ L := by
  have he : π.starLevels.card ≤ m - t := (Nat.le_add_right _ _).trans hπ.1
  calc
    cubeSlot π < π.starLevels.card * 10 ^ L + 10 ^ L :=
      Nat.add_lt_add_left (Encoding.leafIndex π.starsToP0).isLt _
    _ = (π.starLevels.card + 1) * 10 ^ L := by rw [Nat.add_mul, Nat.one_mul]
    _ ≤ (m - t + 1) * 10 ^ L := Nat.mul_le_mul_right _ (Nat.succ_le_succ he)

/-- A box's recovered slot satisfies both actual digit-loop eligibility tests. -/
theorem eligible_cubeSlot {L m t : ℕ} {π : Cube L} (hπ : IsBox m t π) :
    Eligible L (m - t) (cubeSlot π) := by
  change recordStars L (cubeSlot π) ≤ population (recordCode L (cubeSlot π)) L ∧
    population (recordCode L (cubeSlot π)) L ≤ m - t
  rw [cubeSlot, recordStars_slot, recordCode_slot, population_eq_card_P0Levels,
    leafAt_leafIndex, card_P0Levels_starsToP0]
  exact ⟨Nat.le_add_right _ _, hπ.1⟩

/-- A recovered key denotes precisely the original box. -/
theorem slotCube_cubeSlot {L m t : ℕ} {π : Cube L} (hπ : IsBox m t π) :
    slotCube L (cubeSlot π) = π := by
  rw [slotCube, cubeSlot, recordStars_slot, completionAt_slot, leafAt_leafIndex]
  exact (eq_starLowest_starsToP0 π hπ.2).symm

/-- The computed compact count is exactly the existing finite box-set cardinality. -/
theorem count_eligible_eq_card_boxes (L m t : ℕ) :
    Nat.count (Eligible L (m - t)) ((m - t + 1) * 10 ^ L) = (boxes L m t).card := by
  rw [Nat.count_eq_card_filter_range]
  refine card_bij (fun s _ => slotCube L s) ?_ ?_ ?_
  · intro s hs
    exact mem_boxes.mpr (slotCube_isBox (mem_filter.mp hs).2)
  · intro s hs s' hs' heq
    have hkeys := congrArg cubeSlot heq
    simpa only [cubeSlot_slotCube (mem_filter.mp hs).2,
      cubeSlot_slotCube (mem_filter.mp hs').2] using hkeys
  · intro π hπ
    have hp := mem_boxes.mp hπ
    exact ⟨cubeSlot π, mem_filter.mpr ⟨mem_range.mpr (cubeSlot_lt hp),
      eligible_cubeSlot hp⟩, slotCube_cubeSlot hp⟩

/-- The native subtraction computes a replacement leaf's existing decimal index exactly. -/
theorem leafIndex_update_P0 {L : ℕ} (τ : Leaf L) (ℓ : Fin L) (d : Fin 10)
    (hτ : τ ℓ = .P0) :
    (Encoding.leafIndex (Function.update τ ℓ (Encoding.termDigits d))).val =
      (Encoding.leafIndex τ).val - (9 - d.val) * 10 ^ ℓ.val := by
  have hfun : (fun j => Encoding.termDigits.symm
      (Function.update τ ℓ (Encoding.termDigits d) j)) =
      Function.update (fun j => Encoding.termDigits.symm (τ j)) ℓ d := by
    funext j
    by_cases h : j = ℓ <;> simp [h]
  unfold Encoding.leafIndex
  rw [hfun]
  have hd : d.val ≤ (Encoding.termDigits.symm (τ ℓ)).val := by
    simpa [hτ, Encoding.termDigits] using (Nat.le_of_lt_succ d.isLt)
  simpa [hτ, Encoding.termDigits] using Nat.finFunctionFinEquiv_update_of_le
    (fun j => Encoding.termDigits.symm (τ j)) ℓ d hd

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable
