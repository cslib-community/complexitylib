/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable.Index
import Complexity.Foundations.Data.Finset.LowestMax

/-!
# Earlier native entries for a box's ten children

The computed e-th P0 stride selects the highest star of the existing canonical box.
The actual subtraction and directory-slot arithmetic therefore identify its ten
replacement boxes, all strictly earlier in the e-major catalogue. These finite facts
justify native memoization without supplying a geometry or lookup oracle.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable

open Finset Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- An eligible slot with a positive star count has a highest star. -/
theorem slotCube_stars_nonempty {L H s : ℕ} (hv : Eligible L H s)
    (he : 0 < recordStars L s) : (slotCube L s).starLevels.Nonempty := by
  apply card_pos.mp
  rw [slotCube_star_count hv]
  exact he

/-- The native child completion code obtained by replacing the selected P0 digit. -/
@[expose] def childCode (L s : ℕ) (d : Fin 10) : ℕ :=
  recordCode L s - (9 - d.val) * recordStride L s

/-- The actual child directory address before adding the directory base. -/
@[expose] def childSlot (L s : ℕ) (d : Fin 10) : ℕ :=
  (recordStars L s - 1) * 10 ^ L + childCode L s d

/-- The recorded place value is exactly that of the highest starred coordinate. -/
theorem recordStride_eq_pow_highest {L H s : ℕ} (hv : Eligible L H s)
    (he : 0 < recordStars L s) :
    recordStride L s = 10 ^ ((slotCube L s).starLevels.max'
      (slotCube_stars_nonempty hv he)).val := by
  let τ := completionAt L s
  let e := recordStars L s
  have hpop : e ≤ (P0Levels τ).card := by
    change recordStars L s ≤ (P0Levels (leafAt
      ⟨recordCode L s, Nat.mod_lt _ (pow_pos (by decide) L)⟩)).card
    rw [← population_eq_card_P0Levels]
    exact hv.1
  have hne : (lowest e (P0Levels τ)).Nonempty := by
    simpa only [slotCube, starLevels_starLowest] using slotCube_stars_nonempty hv he
  let q := (lowest e (P0Levels τ)).max' hne
  have hq : q ∈ P0Levels τ := lowest_subset _ _ (max'_mem _ hne)
  have hd : digitAt (recordCode L s) q.val = 9 :=
    (leafAt_eq_P0_iff _ q).mp (mem_P0Levels.mp hq)
  have hrank : population (recordCode L s) (q.val + 1) = e := by
    rw [population_succ, hd, ite_eq_left rfl]
    have hp := population_eq_card_P0Levels_filter
      (⟨recordCode L s, Nat.mod_lt _ (pow_pos (by decide) L)⟩ : Fin (10 ^ L))
      (Nat.le_of_lt q.isLt)
    have hc := card_filter_lt_max_lowest hpop hne
    have hf : ((P0Levels τ).filter fun ℓ => ℓ.val < q.val) =
        (P0Levels τ).filter fun ℓ => ℓ < q := by rfl
    rw [hp]
    change ((P0Levels τ).filter fun ℓ => ℓ.val < q.val).card + 1 = e
    rw [hf]
    exact hc
  have hs := starStride_of_rank q.isLt hd hrank
  change starStride (recordCode L s) (recordStars L s) L = _
  simpa only [slotCube, starLevels_starLowest] using hs

/-- Completion of a replacement changes exactly that completed-leaf coordinate. -/
theorem starsToP0_replace {L : ℕ} (π : Cube L) (q : Fin L)
    (lam : Term) : (π.replace q lam).starsToP0 = Function.update π.starsToP0 q lam := by
  funext ℓ
  by_cases h : ℓ = q
  · subst ℓ
    simp [Cube.replace, Cube.starsToP0]
  · simp [Cube.replace, Cube.starsToP0, Function.update_of_ne h]

/-- Native child arithmetic computes the exact canonical key of the replacement box. -/
theorem childSlot_eq_cubeSlot_replace {L H s : ℕ} (hv : Eligible L H s)
    (he : 0 < recordStars L s) (d : Fin 10) :
    childSlot L s d = cubeSlot ((slotCube L s).replace
      ((slotCube L s).starLevels.max' (slotCube_stars_nonempty hv he))
      (Encoding.termDigits d)) := by
  let π := slotCube L s
  let q := π.starLevels.max' (slotCube_stars_nonempty hv he)
  have hq : π q = .star := Cube.mem_starLevels.mp (max'_mem _ _)
  have hτ : π.starsToP0 q = .P0 := by simp [Cube.starsToP0, hq]
  have hc : π.starLevels.card = recordStars L s := slotCube_star_count hv
  have hpow : recordStride L s = 10 ^ q.val := recordStride_eq_pow_highest hv he
  have hchild : (π.replace q (Encoding.termDigits d)).starLevels.card =
      recordStars L s - 1 := by
    rw [Cube.starLevels_replace, card_erase_of_mem (max'_mem _ _), hc]
  change childSlot L s d = cubeSlot (π.replace q (Encoding.termDigits d))
  rw [cubeSlot, hchild, starsToP0_replace, leafIndex_update_P0 _ _ _ hτ,
    ← hpow]
  simp only [π, starsToP0_slotCube, completionAt, leafIndex_leafAt, childSlot, childCode]

/-- A child is a genuine finite box with exactly one fewer star. -/
theorem replace_mem_boxesWithStars {L H s : ℕ} (hv : Eligible L H s)
    (he : 0 < recordStars L s) (d : Fin 10) :
    (slotCube L s).replace ((slotCube L s).starLevels.max'
      (slotCube_stars_nonempty hv he)) (Encoding.termDigits d) ∈
      boxesWithStars L H 0 (recordStars L s - 1) := by
  apply replace_highest_mem_boxesWithStars
  refine mem_boxesWithStars.mpr ⟨?_, ?_⟩
  · exact slotCube_isBox (by simpa using hv)
  · rw [slotCube_star_count hv]
    omega

/-- Child directory lookups always address valid emitted entries. -/
theorem eligible_childSlot {L H s : ℕ} (hv : Eligible L H s)
    (he : 0 < recordStars L s) (d : Fin 10) : Eligible L H (childSlot L s d) := by
  rw [childSlot_eq_cubeSlot_replace hv he d]
  simpa using eligible_cubeSlot (mem_boxesWithStars.mp (replace_mem_boxesWithStars hv he d)).1

/-- The directory decoder returns the exact replacement cube required by the finite recurrence. -/
theorem slotCube_childSlot {L H s : ℕ} (hv : Eligible L H s)
    (he : 0 < recordStars L s) (d : Fin 10) :
    slotCube L (childSlot L s d) = (slotCube L s).replace
      ((slotCube L s).starLevels.max' (slotCube_stars_nonempty hv he))
      (Encoding.termDigits d) := by
  rw [childSlot_eq_cubeSlot_replace hv he d]
  exact slotCube_cubeSlot (mem_boxesWithStars.mp (replace_mem_boxesWithStars hv he d)).1

/-- The native replacement code remains an actual original encoding-array index. -/
theorem childCode_lt {L H s : ℕ} (hv : Eligible L H s)
    (he : 0 < recordStars L s) (d : Fin 10) : childCode L s d < 10 ^ L := by
  have hkey := childSlot_eq_cubeSlot_replace hv he d
  have hc := (mem_boxesWithStars.mp (replace_mem_boxesWithStars hv he d)).2
  rw [childSlot, cubeSlot, hc] at hkey
  have heq := Nat.add_left_cancel hkey
  exact heq ▸ (Encoding.leafIndex _).isLt

/-- Decreasing the exact star count puts every child before its parent in the raw catalogue. -/
theorem childSlot_lt {L H s : ℕ} (hv : Eligible L H s)
    (he : 0 < recordStars L s) (d : Fin 10) : childSlot L s d < s := by
  calc
    childSlot L s d < (recordStars L s - 1) * 10 ^ L + 10 ^ L :=
      Nat.add_lt_add_left (childCode_lt hv he d) _
    _ = recordStars L s * 10 ^ L := by
      rw [← Nat.add_one_mul, Nat.sub_add_cancel he]
    _ ≤ s := Nat.div_mul_le_self _ _

/-- Offset-one directory ranks point to values already written by the native e-major loop. -/
theorem child_rank_lt {L H s : ℕ} (hv : Eligible L H s)
    (he : 0 < recordStars L s) (d : Fin 10) :
    Nat.count (Eligible L H) (childSlot L s d) < Nat.count (Eligible L H) s :=
  Nat.count_strict_mono (eligible_childSlot hv he d) (childSlot_lt hv he d)

/-- The finite box-value recurrence reads precisely the ten earlier native child slots. -/
theorem boxValue_eq_sum_childSlots {L H s : ℕ} (hv : Eligible L H s)
    (he : 0 < recordStars L s) (encA encB : Leaf L → ℤ) :
    boxValue encA encB (recordStars L s) (slotCube L s) =
      ∑ d : Fin 10, boxValue encA encB (recordStars L s - 1)
        (slotCube L (childSlot L s d)) := by
  have heq : recordStars L s = (recordStars L s - 1) + 1 := by omega
  conv_lhs => rw [heq]
  rw [boxValue, dite_eq_left (slotCube_stars_nonempty hv he)]
  rw [← Encoding.termDigits.sum_comp]
  exact sum_congr rfl fun d _ => by rw [slotCube_childSlot hv he d]

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable
