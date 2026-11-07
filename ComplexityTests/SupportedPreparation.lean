/-
Copyright (c) 2026 Samuel Schlesinger, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Christian Reitwiessner
-/

module
-- upstream: local-only (tests of supported relative preparation)

import Complexity.Foundations.Probability.NormalizedAtomRows.SupportedPreparation

/-! Nonzero, signed and saturated clients of the actual hierarchy preparation. The first
example constructs a hierarchy instance and consumes its supplied regularity constants. -/

open Finset Cslib Matrix
open Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
open Matrix.FourthRootHierarchyParams.NormalizedRow
set_option linter.privateModule false
noncomputable section

private lemma unit_rank_zero (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (d : Unit → ℝ) : kthLargest HP.K univ d = 0 := by
  apply kthLargest_eq_zero_of_card_lt
  simpa only [card_univ, Fintype.card_unit] using rank_gt_one HP

private lemma unit_preparation_one (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (v : ℝ) (hv : HP.θ ≤ v) :
    atomPrep (polynomialPrepCutoff4 HP.θ) HP.ρ HP.K 1
      (fun (_ _ : Unit) => v) univ () () = 1 := by
  simp only [atomPrep, rowGate, div_one, unit_rank_zero,
    HP.ρ_one _ HP.η_pos.le, mul_one]
  exact polynomialPrepCutoff4_eq_one HP.θ_pos (by linarith [HP.θ_pos])

/-- The inequality has a realized hierarchy and a genuinely nonzero preparation error.
The true row is zero, so the relative denominator is exactly the physical scale one. -/
example : ∃ HP : FourthRootHierarchyParams 16 1 16 32 8, ∃ Lh Lρ : ℝ,
    0 ≤ Lh ∧ 0 ≤ Lρ ∧
    atomPrep (polynomialPrepCutoff4 HP.θ) HP.ρ HP.K 1
      (fun (_ _ : Unit) => HP.θ) univ () () = 1 ∧
    atomPrep (polynomialPrepCutoff4 HP.θ) HP.ρ HP.K 1
      (fun (_ _ : Unit) => 0) univ () () = 0 ∧
    1 ≤ preparationRelativeConstant HP Lh Lρ * min 1 HP.θ := by
  classical
  obtain ⟨HP⟩ := FourthRootHierarchyParams.nonempty
    (by norm_num : (0 : ℝ) < 16) (by norm_num : (0 : ℝ) < 1)
  obtain ⟨Lh, Lρ, hLh, hLρ, hh, hρ⟩ := preparation_stability_constants HP
  have hzero : atomPrep (polynomialPrepCutoff4 HP.θ) HP.ρ HP.K 1
      (fun (_ _ : Unit) => 0) univ () () = 0 := by
    have hz := polynomialPrepCutoff4_eq_zero HP.θ_pos
      (show (0 : ℝ) ≤ HP.θ / 2 by linarith [HP.θ_pos])
    simp only [atomPrep, zero_div, hz, zero_mul]
  have hone := unit_preparation_one HP HP.θ le_rfl
  refine ⟨HP, Lh, Lρ, hLh, hLρ, hone, hzero, ?_⟩
  have hb := atomPrep_relative_le HP (rank_pos HP) hLh hLρ hh hρ
    (by norm_num : (0 : ℝ) < 1) (fun (_ _ : Unit) => HP.θ)
    (fun (_ _ : Unit) => 0) univ () (by intro y _; norm_num)
    (show 0 ≤ min 1 HP.θ by exact le_min zero_le_one HP.θ_pos.le)
    (by intro y _; simp only [sub_zero, add_zero, div_one, abs_of_pos HP.θ_pos, le_refl])
    () (mem_univ _)
  simpa only [hone, hzero, sub_zero, abs_one, preparationRelativeConstant] using hb

-- Signed approximate input remains legal and can erase a nonzero true preparation.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    atomPrep (polynomialPrepCutoff4 HP.θ) HP.ρ HP.K 1
      (fun (_ _ : Unit) => -HP.θ) univ () () = 0 ∧
    atomPrep (polynomialPrepCutoff4 HP.θ) HP.ρ HP.K 1
      (fun (_ _ : Unit) => HP.θ) univ () () = 1 := by
  constructor
  · have hz := polynomialPrepCutoff4_eq_zero HP.θ_pos
      (show -HP.θ ≤ HP.θ / 2 by linarith [HP.θ_pos])
    simp only [atomPrep, div_one, hz, zero_mul]
  · exact unit_preparation_one HP HP.θ le_rfl

-- An arbitrarily large true entry has the same preparation as the saturation scale.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (T : ℝ) (hT : HP.θ ≤ T) :
    atomPrep (polynomialPrepCutoff4 HP.θ) HP.ρ HP.K 1
      (fun (_ _ : Unit) => HP.θ) univ () () =
    atomPrep (polynomialPrepCutoff4 HP.θ) HP.ρ HP.K 1
      (fun (_ _ : Unit) => T) univ () () := by
  rw [unit_preparation_one HP HP.θ le_rfl, unit_preparation_one HP T hT]

-- With K large entries the actual full-rank gate closes, even though each entry
-- individually lies on the saturated preparation plateau.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (x y : Fin HP.K) :
    atomPrep (polynomialPrepCutoff4 HP.θ) HP.ρ HP.K 1
      (fun (_ _ : Fin HP.K) => HP.θ) univ x y = 0 := by
  classical
  have hq : HP.θ ≤ kthLargest HP.K univ (fun (_ : Fin HP.K) => HP.θ / 1) := by
    apply (le_kthLargest_iff (rank_pos HP) HP.θ_pos).mpr
    simp
  have ht : HP.η₂ ≤ HP.θ := by
    linarith [HP.η₂_lt, HP.δ₀_lt_δ₁, HP.δ₁_lt, HP.θ_pos]
  simp only [atomPrep, rowGate, HP.ρ_zero _ (ht.trans hq), mul_zero]
