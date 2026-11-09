/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: local-only (tests of actual pilot local accuracy)
import Complexity.Computability.LogSpaceDerandomization.HierarchyPilotStability

/-! An actual raw rank change closes a nonzero score, detector and running maximum. -/
set_option linter.privateModule false
open Finset Cslib Matrix Matrix.HierarchyParams
open Matrix.HierarchyParams.PilotRowRecipe
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
namespace PilotStabilityRegression

private lemma spike_rank {n k : ℕ} (v : Fin n) (hk : 1 < k) (hkn : k ≤ n)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    kthLargest k univ (fun w => if w = v then b else a) = a := by
  apply le_antisymm
  · apply le_of_not_gt
    intro hlt
    have hc := (lt_kthLargest_iff (by omega : 0 < k) ha).mp hlt
    have hs : ({w : Fin n | a < if w = v then b else a} : Finset (Fin n)) ⊆ {v} := by
      intro w hw
      simp only [mem_filter, mem_univ, true_and] at hw
      simp only [mem_singleton]
      by_contra hne
      simp [hne] at hw
    have hcard := card_le_card hs
    simp only [card_singleton] at hcard
    omega
  · rcases eq_or_lt_of_le ha with h | h
    · rw [← h]
      exact kthLargest_nonneg
    · apply (le_kthLargest_iff (by omega : 0 < k) h).mpr
      have he : ({w : Fin n | a ≤ if w = v then b else a} : Finset (Fin n)) = univ := by
        ext w
        simp only [mem_filter, mem_univ, true_and, iff_true]
        split_ifs
        · exact hab
        · exact le_rfl
      simpa only [he, card_univ, Fintype.card_fin] using hkn

variable (HP : FourthRootHierarchyParams 16 1 16 32 8)
private abbrev Vert := Fin (HP.J + HP.K + 1)
private def target : Vert HP := ⟨0, by omega⟩
private def raw (a : ℝ) : Matrix (Vert HP) (Vert HP) ℝ :=
  fun _ y => if y = target HP then HP.δ₁ else a
private def mask (_ : Unit) (_ : Vert HP) : Prop := True
private def scores (a : ℝ) := score HP.toHierarchyParams (mask HP) 1 (raw HP a)
private def detected (a : ℝ) := detector HP.toHierarchyParams (mask HP) (mask HP) (scores HP a)

private lemma K_large : 1 < HP.K := by
  have hg := HP.gate
  have hn : 0 ≤ 32 * (HP.k : ℝ) / HP.η :=
    div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) HP.η_pos.le
  have hh : (1 : ℝ) < HP.K := by linarith
  exact_mod_cast hh

private lemma ladder : 0 < HP.η₂ ∧ HP.η₂ < HP.δ₁ := by
  have hη := HP.η_lt_η₂
  have hη₂ := HP.η₂_lt
  have hδ := HP.δ₀_lt_δ₁
  have h0 := HP.η_pos
  constructor <;> linarith

-- Raw ranks change, despite the scalar value at the inspected endpoint staying fixed.
private lemma ranks (x : Vert HP) :
    kthLargest HP.K univ (raw HP 0 x) = 0 ∧
      kthLargest HP.K univ (raw HP HP.η₂ x) = HP.η₂ := by
  exact ⟨spike_rank (target HP) (K_large HP) (by omega) le_rfl
    (by have := HP.δ₀_pos; have := HP.δ₀_lt_δ₁; linarith),
    spike_rank (target HP) (K_large HP) (by omega) (ladder HP).1.le (ladder HP).2.le⟩

private lemma score_change (x : Vert HP) :
    scores HP 0 () x (target HP) = 1 ∧ scores HP HP.η₂ () x (target HP) = 0 := by
  have hϕ : HP.ϕ HP.δ₁ = 1 := HP.ϕ_one _ le_rfl
  have hr := ranks HP x
  have hs : ({w | mask HP () w} : Finset (Vert HP)) = univ := filter_true _
  simp only [scores, score, atomPrep, rowGate, hs, div_one]
  change HP.ϕ HP.δ₁ * HP.ρ (kthLargest HP.K univ (raw HP 0 x)) = 1 ∧
    HP.ϕ HP.δ₁ * HP.ρ (kthLargest HP.K univ (raw HP HP.η₂ x)) = 0
  rw [hϕ, hr.1, hr.2, HP.ρ_one 0 HP.η_pos.le, HP.ρ_zero HP.η₂ le_rfl]
  norm_num

-- The selected score contract must pay the rank change: its inspected entry error is zero.
example : ∃ Lρ : ℝ, 0 ≤ Lρ ∧ 1 ≤ Lρ * HP.η₂ := by
  obtain ⟨Lϕ, Lρ, _hLϕ, hLρ, hϕ, hρ⟩ := HP.pilot_score_stability_constants
  refine ⟨Lρ, hLρ, ?_⟩
  have hd := score_stability HP.toHierarchyParams (mask HP) HP.ρ_nonneg hLρ hϕ hρ
    (by have := K_large HP; omega) (by norm_num : (0 : ℝ) < 1)
    (raw HP 0) (raw HP HP.η₂) () (target HP) (target HP)
  have hm : kthLargest 1 univ (fun w => |raw HP 0 (target HP) w -
      raw HP HP.η₂ (target HP) w|) ≤ HP.η₂ := by
    apply kthLargest_le (ladder HP).1.le
    intro w _
    by_cases hw : w = target HP
    · simpa only [raw, hw, ↓reduceIte, sub_self, abs_zero] using (ladder HP).1.le
    · simp only [raw, hw, ↓reduceIte, zero_sub, abs_neg, abs_of_pos (ladder HP).1]
      exact le_rfl
  change |scores HP 0 () (target HP) (target HP) -
    scores HP HP.η₂ () (target HP) (target HP)| ≤ _ at hd
  rw [(score_change HP (target HP)).1, (score_change HP (target HP)).2] at hd
  norm_num only [sub_zero, abs_one] at hd
  apply hd.trans
  have he : |raw HP 0 (target HP) (target HP) -
      raw HP HP.η₂ (target HP) (target HP)| = 0 := by simp [raw]
  rw [he, mul_zero, zero_add, div_one]
  apply mul_le_mul_of_nonneg_left _ hLρ
  have hs : ({w | mask HP () w} : Finset (Vert HP)) = univ := filter_true _
  rw [hs]
  exact hm

private lemma detector_change : detected HP 0 (target HP) = 1 ∧
    detected HP HP.η₂ (target HP) = 0 := by
  have h1 : kthLargest HP.J univ (fun _ : Vert HP => (1 : ℝ)) = 1 := by
    apply le_antisymm (kthLargest_le (by norm_num) (fun _ _ => le_rfl))
    apply (le_kthLargest_iff HP.J_pos (by norm_num : (0 : ℝ) < 1)).mpr
    simp only [le_refl, filter_true, card_univ, Fintype.card_fin]
    omega
  have h0 : kthLargest HP.J univ (fun _ : Vert HP => (0 : ℝ)) = 0 :=
    le_antisymm (kthLargest_le le_rfl (fun _ _ => le_rfl)) kthLargest_nonneg
  have hscore1 : (fun x => scores HP 0 () x (target HP)) = fun _ => 1 :=
    funext fun x => (score_change HP x).1
  have hscore0 : (fun x => scores HP HP.η₂ () x (target HP)) = fun _ => 0 :=
    funext fun x => (score_change HP x).2
  have hs : ({w | mask HP () w} : Finset (Vert HP)) = univ := filter_true _
  have ht : ({t | mask HP t (target HP)} : Finset Unit) = univ := filter_true _
  unfold detected detector
  rw [ht]
  simp only [Finset.univ_unique, expect_singleton, hs, hscore1, hscore0, h1, h0]
  norm_num

-- All three actual constructors respond to the same nonzero completed-raw perturbation.
example : detected HP 0 (target HP) - detected HP HP.η₂ (target HP) = 1 ∧
    maximum (fun _ => 1/4) (detected HP 0) (target HP) = 1 ∧
    maximum (fun _ => 1/4) (detected HP HP.η₂) (target HP) = 1/4 := by
  obtain ⟨h1, h0⟩ := detector_change HP
  norm_num [maximum, h1, h0]

-- A shared outer environment changes the actual children together; the maximum error
-- has fourth moment 81/512. No independent-seed or final-maximum hypothesis appears.
example : rowNormPow 4 1 1 (fun (_ : Bool) (_ : Unit) => True)
    (fun _ _ => True) (fun σ _ _ =>
      maximum (fun _ => 1/4) (detected HP (if σ then 0 else HP.η₂)) (target HP) -
        maximum (fun _ => 1/4) (detected HP HP.η₂) (target HP)) = 81/512 := by
  obtain ⟨h1, h0⟩ := detector_change HP
  norm_num [rowNormPow, expect_eq_sum_div_card, Fintype.sum_bool, maximum, h1, h0]

-- Negative unbounded score estimates are clipped only after actual source ranking/averaging.
example : detector HP.toHierarchyParams (mask HP) (mask HP)
    (fun _ _ _ => -1000) (target HP) = 0 := by
  have hr : kthLargest HP.J univ (fun _ : Vert HP => (-1000 : ℝ)) = 0 :=
    le_antisymm (kthLargest_le (by norm_num) (fun _ _ => by norm_num)) kthLargest_nonneg
  norm_num [detector, mask, Finset.univ_unique, hr]

-- Empty terminal slices and empty source seed types both average to zero.
example : detector HP.toHierarchyParams (mask HP) (fun (_ : Unit) (_ : Vert HP) => False)
    (scores HP 0) (target HP) = 0 := by simp [detector]
example : detector HP.toHierarchyParams (fun (_ : Fin 0) (_ : Vert HP) => True)
    (mask HP) (scores HP 0) (target HP) = 0 := by simp [detector]

example : detector HP.toHierarchyParams (fun (_ : Unit) (_ : Vert HP) => False)
    (mask HP) (scores HP 0) (target HP) = 0 := by simp [detector, kthLargest]

-- The maximum contract pays the actual changed detector on original source/terminal
-- pairs, even when the same outer bit controls every value in the table.
example : rowNormPow 4 1 1 (fun (_ : Bool) (_ : Unit) => True)
    (fun _ _ => True) (fun σ _ _ =>
      maximum (fun _ => 1/4) (fun _ : Unit =>
        detected HP (if σ then 0 else HP.η₂) (target HP)) () -
      maximum (fun _ => 1/4) (fun _ : Unit => detected HP HP.η₂ (target HP)) ()) ≤
    rowNormPow 4 1 1 (fun (_ : Bool) (_ : Unit) => True) (fun _ _ => True)
      (fun σ _ _ => detected HP (if σ then 0 else HP.η₂) (target HP) -
        detected HP HP.η₂ (target HP)) := by
  have h := maximum_row_moment (fun (_ : Bool) (_ : Unit) => True) (fun _ _ => True)
    (fun _ (_ : Unit) => (1/4 : ℝ))
    (fun σ (_ : Unit) => detected HP (if σ then 0 else HP.η₂) (target HP))
    (fun _ (_ : Unit) => (1/4 : ℝ))
    (fun _ (_ : Unit) => detected HP HP.η₂ (target HP)) (N := 1) (u := 1) (by norm_num)
  simpa [rowNormPow, maximum] using h

-- Empty vertex domains and zero normalization remain meaningful in the moment contract.
example : rowNormPow 4 1 1 (fun (_ : Unit) (_ : Fin 0) => True)
    (fun _ _ => True) (fun _σ _ y => maximum (fun _ => 0) (fun _ => 1) y -
      maximum (fun _ => 0) (fun _ => 0) y) = 0 := by simp [rowNormPow]
example : rowNormPow 4 0 1 (fun (_ : Unit) (_ : Unit) => True)
    (fun _ _ => True) (fun _ _ _ => (1 : ℝ)) = 0 := by simp [rowNormPow]
-- A source seed removes the entire ranked column half the time. The terminal hit
-- selects the score's nonzero branch, and the same outer bit controls every entry.
private def halfMask (s : Bool) (_ : Vert HP) : Prop := s = true
private def correlatedScores (σ t : Bool) : Matrix (Vert HP) (Vert HP) ℝ :=
  if σ && t then fun _ _ => 1 else fun _ _ => 0

private lemma halfMask_seeds (y : Vert HP) :
    ({t | halfMask HP t y} : Finset Bool) = {true} := by
  unfold halfMask
  ext t
  simp only [mem_filter, mem_univ, true_and, mem_singleton]

private lemma correlated_detector (σ : Bool) (y : Vert HP) :
    detector HP.toHierarchyParams (halfMask HP) (halfMask HP)
      (correlatedScores HP σ) y = if σ then 1/2 else 0 := by
  have h1 : kthLargest HP.J univ (fun _ : Vert HP => (1 : ℝ)) = 1 := by
    apply le_antisymm (kthLargest_le (by norm_num) (fun _ _ => le_rfl))
    apply (le_kthLargest_iff HP.J_pos (by norm_num : (0 : ℝ) < 1)).mpr
    simp only [le_refl, filter_true, card_univ, Fintype.card_fin]
    omega
  have h0 : kthLargest HP.J univ (fun _ : Vert HP => (0 : ℝ)) = 0 :=
    le_antisymm (kthLargest_le le_rfl (fun _ _ => le_rfl)) kthLargest_nonneg
  simp only [detector, halfMask_seeds, expect_singleton]
  have ht : ({x : Vert HP | halfMask HP true x} : Finset _) = univ := by
    simp only [halfMask, filter_true]
  have hf : ({x : Vert HP | halfMask HP false x} : Finset _) = ∅ := by
    simp only [halfMask, Bool.false_eq_true, filter_false]
  have he (f : Vert HP → ℝ) : kthLargest HP.J ∅ f = 0 := by simp [kthLargest]
  cases σ <;>
    norm_num [expect_eq_sum_div_card, Fintype.sum_bool, ht, hf, correlatedScores, h1, h0, he]

example : rowNormPow 4 1 1
    (fun (_ : Bool) (x : Vert HP) => x = target HP)
    (fun _ (y : Vert HP) => y = target HP)
    (fun σ _ y => detector HP.toHierarchyParams (halfMask HP) (halfMask HP)
      (correlatedScores HP σ) y -
      detector HP.toHierarchyParams (halfMask HP) (halfMask HP)
        (correlatedScores HP false) y) = 1/32 := by
  simp only [correlated_detector]
  have hs : ({x : Vert HP | x = target HP} : Finset _) = {target HP} := by
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
  norm_num [rowNormPow, hs, expect_eq_sum_div_card, Fintype.sum_bool]

-- The new transport consumes correlated scores and retains the source/terminal masks.
-- The child's normalization is 1/16, distinct from the parent's normalization 1.
example : rowNormPow 4 1 1
    (fun (_ : Bool) (x : Vert HP) => x = target HP)
    (fun _ (y : Vert HP) => y = target HP)
    (fun σ _ y => detector HP.toHierarchyParams (halfMask HP) (halfMask HP)
      (correlatedScores HP σ) y -
      detector HP.toHierarchyParams (halfMask HP) (halfMask HP)
        (correlatedScores HP false) y) ≤
    (Fintype.card (Vert HP) : ℝ) / 8 *
      rowNormPow 4 1 (1/16)
        (fun (p : Bool × (Bool × Bool)) x => halfMask HP p.2.1 x)
        (fun p y => halfMask HP p.2.2 y)
        (fun p x y => correlatedScores HP p.1 p.2.2 x y -
          correlatedScores HP false p.2.2 x y) := by
  have h := detector_row_moment_transport HP.toHierarchyParams (halfMask HP) (halfMask HP)
    (fun (_ : Bool) (x : Vert HP) => x = target HP)
    (fun _ (y : Vert HP) => y = target HP)
    (N := 1) (u := 1) (v := 1/16) (π := 1/2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by
      intro y
      norm_num only [dens_eq_card_div_card, halfMask_seeds, card_singleton,
        Fintype.card_bool, Nat.cast_ofNat, le_refl])
    (correlatedScores HP) (fun _ => correlatedScores HP false)
  norm_num only [one_mul, mul_one, div_div, one_div_div] at h
  convert h using 1; ring

-- No positive-density premise is needed when there are no terminal vertices.
example : (∑ y : Fin 0, |detector HP.toHierarchyParams
    (fun (_ : Bool) (_ : Fin 0) => True) (fun (_ : Bool) _ => False)
    (fun _ _ _ => 7) y| ^ 4) = 0 := by simp

-- Concrete frame channels distinguish inherited sampling from the detector rank reset.
-- Both source/terminal padding and a free third role survive the terminal split.
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
open Matrix.HierarchyParams.H4RankEnvironment
private def resetRequest : HierarchyTask.Request HP.k (Fin 3) (ZMod 5) :=
  ⟨.row 0 (.detector ⟨0, HP.k_pos⟩), gridChannel 0 2 [1],
    gridChannel 2 1 [2, 3], gridChannel 2 3 [2, 3]⟩
private lemma reset_admissible : Admissible (resetRequest HP) :=
  ⟨by change (0 : Fin 3) ≠ 2; decide, rfl, rfl⟩

example :
    (dens {σ : Environment 5 3 | (resetRequest HP).source.retains (channels 1) σ 0} : ℝ) =
      16/625 ∧
    (dens {s | stageSource 1 (fun _ : Unit => 0) (resetRequest HP)
      (reset_admissible HP) s ()} : ℝ) = 81/625 ∧
    (dens {t | splitTerminal 1 (fun _ : Unit => 0) (resetRequest HP) t ()} : ℝ) = 81/625 := by
  have hh := stage_channels 1 (fun _ : Unit => (0 : ZMod 5))
    (resetRequest HP) (reset_admissible HP) (by norm_num)
    (fun _ _ _ => Subsingleton.elim _ _)
    (⟨2, 4, by decide, by decide⟩ : Horizon 5) (k := 1) (by decide) rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [channel_density 1 (resetRequest HP).source 2 rfl]
    norm_num [side, Nat.ceilDiv_eq_add_pred_div]
  · convert hh.1.dens_X () using 1
    norm_num [side, Nat.ceilDiv_eq_add_pred_div]
  · convert hh.1.dens_Y () using 1
    norm_num [side, Nat.ceilDiv_eq_add_pred_div]

-- Source-aware children preserve empty/zero conventions and exactly specialize
-- the existing terminal-only algorithm when their source argument is ignored.
example (A : Unit → Matrix (Vert HP) (Vert HP) ℝ) :
    sourceDetector HP.toHierarchyParams (mask HP) (mask HP) (fun _ => A) =
      detector HP.toHierarchyParams (mask HP) (mask HP) A := rfl
example : sourceDetector HP.toHierarchyParams
    (fun (_ : Fin 0) (_ : Vert HP) => True) (mask HP)
    (fun _ _ _ _ => 7) (target HP) = 0 := by simp [sourceDetector]
example : sourceDetector HP.toHierarchyParams (mask HP)
    (fun (_ : Unit) (_ : Vert HP) => False)
    (fun _ _ _ _ => 7) (target HP) = 0 := by simp [sourceDetector]
example : sourceDetector HP.toHierarchyParams (mask HP) (mask HP)
    (fun _ _ _ _ => -1000) (target HP) = 0 := by
  have hr : kthLargest HP.J univ (fun _ : Vert HP => (-1000 : ℝ)) = 0 :=
    le_antisymm (kthLargest_le (by norm_num) (fun _ _ => by norm_num)) kthLargest_nonneg
  norm_num [sourceDetector, mask, hr]

end PilotStabilityRegression
