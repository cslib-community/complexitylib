/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
-- upstream: candidate

import Complexity.Foundations.Probability.NormalizedAtomRows.RequestSharp

/-! A zero-start actual increment consumes the sharp no-overflow comparison at a positive
floor. This tests the weighted preloss/final-error conclusion with exact raw prefixes. -/

open Finset Cslib Matrix Cslib.RowCompression
open Matrix.FourthRootHierarchyParams.NormalizedRow
open scoped BigOperators

namespace NormalizedAtomSharpTests

private lemma singleton_rank (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (d : Unit → ℝ) : kthLargest HP.K univ d = 0 := by
  apply le_antisymm _ kthLargest_nonneg
  apply le_of_not_gt
  intro h
  have hh := (lt_kthLargest_iff (rank_pos HP) (le_refl (0 : ℝ))).mp h
  have hc := card_filter_le (s := (univ : Finset Unit)) (p := fun y => 0 < d y)
  have hk := rank_gt_one HP
  simp only [card_univ, Fintype.card_unit] at hc
  omega

/-- An exact first raw prefix gives zero root discrepancy after actual positive-floor
compression, starting from the zero state. The true first entry can be arbitrarily large. -/
theorem exact_increment (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (D : ℝ) (hD : 0 ≤ D) :
    let scale := HP.η / 2
    let ζ := scale / 4
    let w : Unit → Fin 2 → ℝ := fun _ ν => if ν = 0 then D else ζ * (3/4 : ℝ)
    let a := iterate univ (fun _ => HP.K) (fun _ => HP.K) (dyadicFloor scale 1)
      (fun _ => w) ⟨0, 0⟩ 1
    stateRootError (output HP ζ) univ HP.K a ⟨0, w⟩ () = 0 := by
  classical
  let scale := HP.η / 2
  let ζ := scale / 4
  let w : Unit → Fin 2 → ℝ := fun _ ν => if ν = 0 then D else ζ * (3/4 : ℝ)
  have hs : 0 < scale := half_pos HP.η_pos
  have hζ : 0 < ζ := div_pos hs (by norm_num)
  have hmargin : scale ≤ HP.η := by dsimp only [scale]; linarith [HP.η_pos]
  obtain ⟨Cf, _, hfinal⟩ := sharp_noOverflow HP ζ hζ hs hmargin
  obtain ⟨Cp, _, hbound⟩ := hfinal scale hs le_rfl
  have hno : ∀ i < 1, stepThreshold univ (fun _ => HP.K) (fun _ => HP.K)
      (dyadicFloor scale 1) (fun _ => w) (⟨0, 0⟩ : State Unit) i ≤ dyadicFloor scale 1 i := by
    intro i hi
    have hi0 : i = 0 := by omega
    subst i
    simp only [stepThreshold, inputRow, iterate_zero, zero_add, threshold, singleton_rank HP]
    rw [max_eq_left (dyadicFloor_nonneg hs.le 1 0),
      max_eq_right (dyadicFloor_nonneg hs.le 1 0)]
  have he (i : ℕ) (_hi : i < 1) (y : Unit) (_hy : y ∈ (univ : Finset Unit))
      (_hd : scale / 2 ≤ w y 0) :
      clippedError (w y 0) (w y 1) (uncompressedRow (fun _ => w) 0 (i+1) y) ≤ 0 := by
    have hi0 : i = 0 := by omega
    subst i
    have hw : uncompressedRow (fun _ => w) 0 1 y = w y := by
      funext ν
      simp only [uncompressedRow, sum_range_one, Pi.zero_apply, zero_add]
    rw [hw, clippedError_self (w y 0) (w y 1) (w y) rfl rfl]
  have hf : ∀ y ∈ (univ : Finset Unit),
      clippedError (w y 0) (w y 1) (uncompressedRow (fun _ => w) 0 1 y) ≤ 0 := by
    intro y hy
    have hw : uncompressedRow (fun _ => w) 0 1 y = w y := by
      funext ν
      simp only [uncompressedRow, sum_range_one, Pi.zero_apply, zero_add]
    rw [hw, clippedError_self (w y 0) (w y 1) (w y) rfl rfl]
  have hb := hbound univ (fun _ => HP.K) (fun _ => w) 0 w 1 hno
    (fun _ _ => hD) (fun _ => 0) (by intros; exact le_rfl) he 0 le_rfl hf () (mem_univ _)
  simp only [mul_zero, sum_const_zero, add_zero] at hb
  exact abs_nonpos_iff.mp hb

end NormalizedAtomSharpTests
