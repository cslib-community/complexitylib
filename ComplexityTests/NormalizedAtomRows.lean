/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
-- upstream: candidate

import Complexity.Computability.LogSpaceDerandomization.NormalizedAtomRows.BoundedLoss

/-! Behavioral regressions for actual uncentered normalization: full-rank off-usage
sensitivity and the obstruction to allowing arbitrary common first loss. -/

open Finset Cslib Matrix Cslib.RowCompression
open Matrix.FourthRootHierarchyParams.NormalizedRow
open scoped BigOperators
namespace NormalizedAtomRowsTests

variable (HP : FourthRootHierarchyParams 16 1 16 32 8)

private lemma unit_rank_zero (d : Unit → ℝ) : kthLargest HP.K univ d = 0 := by
  apply le_antisymm _ kthLargest_nonneg
  apply le_of_not_gt
  intro h
  have hh := (lt_kthLargest_iff (rank_pos HP) (le_refl (0:ℝ))).mp h
  have hc := card_filter_le (s := (univ : Finset Unit)) (p := fun y => 0 < d y)
  have hk := rank_gt_one HP
  simp only [card_univ, Fintype.card_unit] at hc
  omega



/-- Usage sees identical input coordinates, but perturbing the K full-rank coordinates
outside usage closes the actual normalized output gate. -/
theorem large_off_usage_rank_changes_output
    (HP : FourthRootHierarchyParams 16 1 16 32 8) {ζ : ℝ} (hζ : 0 < ζ) (D : ℝ) (hD : HP.η₂ ≤ D) :
    let V := Fin (HP.K+1)
    let usage : Finset V := {0}
    let w : V → Fin 2 → ℝ := fun y ν => if ν=0 then (if y=0 then 1 else 0) else (if y=0 then
      ζ*(3/4) else 0)
    let w' : V → Fin 2 → ℝ := fun y ν => if ν=0 then (if y=0 then 1 else D) else (if y=0 then
      ζ*(3/4) else 0)
    (∀ y ∈ usage, w y = w' y) ∧
    (∀ y ∈ usage, clippedError (w y 0) (w y 1) (w' y) = 0) ∧
    0 < output HP ζ (w 0 0) (w 0 1) (firstRank univ HP.K 0 w) ∧
    output HP ζ (w' 0 0) (w' 0 1) (firstRank univ HP.K 0 w') = 0 := by
  dsimp only
  let w : Fin (HP.K+1) → Fin 2 → ℝ := fun y ν => if ν=0 then (if y=0 then 1 else 0) else (if
    y=0 then ζ*(3/4) else 0)
  let w' : Fin (HP.K+1) → Fin 2 → ℝ := fun y ν => if ν=0 then (if y=0 then 1 else D) else (if
    y=0 then ζ*(3/4) else 0)
  have hr : kthLargest HP.K univ (fun y => w y 0) = 0 := by
    apply le_antisymm _ kthLargest_nonneg
    apply le_of_not_gt
    intro h
    have hc := (lt_kthLargest_iff (rank_pos HP) (le_refl (0:ℝ))).mp h
    have hf : ({y : Fin (HP.K+1) | 0 < w y 0} : Finset _) = {0} := by
      ext y
      simp only [w, Fin.isValue, ↓reduceIte, mem_filter, mem_univ, true_and, mem_singleton]
      split_ifs <;> norm_num <;> assumption
    rw [hf, card_singleton] at hc
    exact (not_le.mpr (rank_gt_one HP)) hc
  have hq : HP.η₂ ≤ kthLargest HP.K univ (fun y => w' y 0) := by
    apply (le_kthLargest_iff (rank_pos HP) (HP.η_pos.trans HP.η_lt_η₂)).mpr
    have hs : (univ.erase (0 : Fin (HP.K+1))) ⊆ ({y | HP.η₂ ≤ w' y 0} : Finset _) := by
      intro y hy
      have hy0 := (mem_erase.mp hy).1
      simp only [mem_filter, mem_univ, true_and, w', Fin.isValue, ↓reduceIte, hy0]
      linarith
    have hc := card_le_card hs
    simpa only [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin,
      Nat.add_sub_cancel] using hc
  refine ⟨?_,?_,?_,?_⟩
  · intro y hy
    have hy0 := mem_singleton.mp hy
    subst y
    rfl
  · intro y hy
    have hy0 := mem_singleton.mp hy
    subst y
    exact clippedError_self _ _ _ rfl rfl
  · change 0 < output HP ζ 1 (ζ*(3/4)) (firstRank univ HP.K 0 w)
    rw [firstRank, hr, max_self, output, HP.ρ_one _ HP.η_pos.le, mul_one]
    have hQ : 0 < HP.toHierarchyParams.atomCutoff 1 := by
      rw [HP.toHierarchyParams.atomCutoff_eq (by norm_num) (by
        have := Nat.cast_nonneg (α := ℝ) HP.k
        linarith)]
      have hh := HP.le_Q 1
      have ht := HP.θ₂_lt
      norm_num at ht
      linarith
    have hden : ζ*(3/4)/ζ = (3/4:ℝ) := mul_div_cancel_left₀ _ hζ.ne'
    rw [hden]
    exact div_pos hQ (by norm_num [clip])
  · exact gate_zero HP (hq.trans (kthLargest_le_firstRank))

/-- Unbounded common first loss invalidates a cap-free static theorem: the raw relative
error is 1/(1+D), while the post-loss output separation is the fixed positive value at 1. -/
theorem unbounded_loss_obstruction
    (HP : FourthRootHierarchyParams 16 1 16 32 8) {ζ : ℝ} (hζ : 0 < ζ)
    (D : ℝ) (hD : 0 ≤ D) :
    clippedError D (ζ*(3/4)) (fun ν : Fin 2 => if ν=0 then D+1 else ζ*(3/4)) = 1/(1+D) ∧
    output HP ζ (D+1-D) (ζ*(3/4)) 0 - output HP ζ (D-D) (ζ*(3/4)) 0 =
      output HP ζ 1 (ζ*(3/4)) 0 ∧ 0 < output HP ζ 1 (ζ*(3/4)) 0 := by
  have he : 0 ≤ 1/(1+D) := by positivity
  have he1 : 1/(1+D) ≤ 1 := (div_le_one (by linarith : 0 < 1+D)).mpr (by linarith)
  refine ⟨?_,?_,?_⟩
  · have hdiff : D+1-D=1 := by ring
    simp only [clippedError, Fin.isValue, one_ne_zero, ↓reduceIte, hdiff, abs_one, sub_self,
      abs_zero,
      min_eq_right zero_le_one, min_eq_right he1, max_eq_left he]
  · rw [show D+1-D=1 by ring, sub_self, entry_zero HP (x := 0) HP.θ_pos.le, sub_zero]
  · rw [output, HP.ρ_one _ HP.η_pos.le, mul_one]
    have hQ : 0 < HP.toHierarchyParams.atomCutoff 1 := by
      rw [HP.toHierarchyParams.atomCutoff_eq (by norm_num) (by
        have := Nat.cast_nonneg (α := ℝ) HP.k
        linarith)]
      have hh := HP.le_Q 1
      have ht := HP.θ₂_lt
      norm_num at ht
      linarith
    rw [mul_div_cancel_left₀ _ hζ.ne']
    exact div_pos hQ (by norm_num [clip])

/-- A zero initial state receives a nonzero raw increment and yields positive actual output.
The denominator signal is uncentered and positive; the rank is the actual padded rank. -/
theorem zero_start_nonzero_output : ∃ HP : FourthRootHierarchyParams 16 1 16 32 8,
    let w : Unit → Fin 2 → ℝ := fun _ ν => if ν = 0 then 1 else (3/4 : ℝ)
    let a := iterate univ (fun _ => HP.K) (fun _ => HP.K) (fun _ => 0)
      (fun _ => w) ⟨0, 0⟩ 1
    a.row () = w () ∧ 0 < output HP 1 (a.row () 0) (a.row () 1)
      (firstRank univ HP.K a.defaultValue a.row) := by
  classical
  obtain ⟨HP⟩ := FourthRootHierarchyParams.nonempty
    (by norm_num : (0 : ℝ) < 16) (by norm_num : (0 : ℝ) < 1)
  refine ⟨HP, ?_⟩
  let w : Unit → Fin 2 → ℝ := fun _ ν => if ν = 0 then 1 else (3/4 : ℝ)
  have ht : threshold univ HP.K 0 0 w = 0 := by
    simp only [threshold, unit_rank_zero HP, max_self]
  have hz : newDefault univ HP.K HP.K 0 0 w = 0 := by
    simp only [newDefault, ht, unit_rank_zero HP, max_self, mul_zero, min_self]
  have hw : update univ HP.K HP.K 0 0 w () = w () := by
    apply update_eq_self_of_three_mul_le
    rw [ht]
    simpa only [mul_zero] using entrySize_nonneg (w ())
  have ha : iterate univ (fun _ => HP.K) (fun _ => HP.K) (fun _ => 0)
      (fun _ => w) (⟨0, 0⟩ : State Unit) 1 = ⟨0, w⟩ := by
    simp only [iterate, advance, zero_add, hz]
    congr 1
    funext y
    cases y
    exact hw
  dsimp only
  change _ ∧ 0 < output HP 1 _ _ _
  rw [ha]
  refine ⟨rfl, ?_⟩
  rw [firstRank, unit_rank_zero HP, max_self, output, HP.ρ_one _ HP.η_pos.le, mul_one]
  have hQ : 0 < HP.toHierarchyParams.atomCutoff 1 := by
    rw [HP.toHierarchyParams.atomCutoff_eq (by norm_num)
      (by have := Nat.cast_nonneg (α := ℝ) HP.k; linarith)]
    have hh := HP.le_Q 1
    have ht := HP.θ₂_lt
    norm_num at ht
    linarith
  exact div_pos hQ (by norm_num [w, clip])

end NormalizedAtomRowsTests
