/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
import Complexity.Foundations.Probability.CorrectionRowTasks
import Complexity.Foundations.Probability.FourthRootHierarchyParams
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

/-!
# Actual hierarchy correction/reward regression

A three-vertex forward path has a positive correction at `0 → 1`. The hierarchy pilot has
full-retention channels at stage zero. Its actual regular witness has detector rank greater
than three, so its detector is zero. The independent sampling model retains midpoints on one
of two Boolean seeds. This tests an actual correction and a nonconstant reward sample, with
the rank bound derived from the regular hierarchy parameters.
-/

namespace ComplexityTests.HierarchyTaskMeans

open Finset Matrix
open scoped BigOperators

private abbrev full {α : Type*} (_ : α) (_ : Fin 3) : Prop := True
private abbrev hit (t : Bool) (_ : Fin 3) : Prop := t = true

private noncomputable def C : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 1 / 2, 0; 0, 0, 1 / 2; 0, 0, 0]

private theorem C_nonneg (x y : Fin 3) : 0 ≤ C x y := by
  fin_cases x <;> fin_cases y <;> norm_num [C]

private theorem C_row : C *ᵥ 1 ≤ 1 := by
  intro x
  fin_cases x <;> norm_num [C, mulVec, dotProduct, Fin.sum_univ_three]

private theorem detector_rank (P : FourthRootHierarchyParams 2 1 1 1 0) : 3 < P.J := by
  have hk : (1 : ℝ) ≤ P.k := by exact_mod_cast P.k_pos
  have hm : (1 : ℝ) ≤ P.m := by
    have hmNat : 1 ≤ P.m := by
      by_contra hn
      have hm0 : P.m = 0 := by omega
      have h := P.copies_strict
      simp only [hm0, Nat.cast_zero, zero_add] at h
      linarith
    exact_mod_cast hmNat
  have hδ : P.δ₀ < 1 := by
    have h1 := P.δ₀_lt_δ₁
    have h2 := P.δ₁_lt
    have h3 := P.θ_lt_θ₂
    have h4 := P.θ₂_lt
    norm_num at h4
    linarith
  have hlower : (4 : ℝ) ≤ 2 * 1 * P.m * P.k * (P.k + 1) := by
    calc
      (4 : ℝ) = 2 * 1 * 1 * 1 * (1 + 1) := by norm_num
      _ ≤ _ := by gcongr
  have hrank := P.rank
  by_contra hn
  have hJ : (P.J : ℝ) ≤ 3 := by exact_mod_cast (le_of_not_gt hn)
  have hJ0 : (0 : ℝ) ≤ P.J := Nat.cast_nonneg _
  have hδJ : P.δ₀ * P.J ≤ 3 := (mul_le_mul_of_nonneg_right hδ.le hJ0).trans (by simpa using hJ)
  linarith

private theorem pilot_full (P : HierarchyParams 2 1 1 1 0) (hJ : 3 < P.J) :
    P.pilot (full (α := Unit)) (full (α := Unit)) 1 C = 0 := by
  rw [P.pilot_eq]
  have hU (G : Matrix (Fin 3) (Fin 3) ℝ) :
      columnDetector (full (α := Unit)) (full (α := Unit)) P.ϕ P.ρ P.J P.K 1 G = 0 := by
    ext y
    have hrank (S T : Finset (Fin 3)) : detectorTrial P.ϕ P.ρ P.J P.K 1 G S T y = 0 := by
      apply le_antisymm _ kthLargest_nonneg
      apply le_of_not_gt
      intro h
      have hc := (lt_kthLargest_iff P.J_pos (le_refl (0 : ℝ))).mp h
      have hb : #{x ∈ S | 0 < P.ϕ (G x y / 1) * rowGate P.ρ P.K 1 G T x} ≤ 3 :=
        card_le_univ _
      omega
    simp [columnDetector, hrank]
  have hmax (j : ℕ) : pilotMax (P.cutoff 1) P.γ
      (columnDetector (full (α := Unit)) (full (α := Unit)) P.ϕ P.ρ P.J P.K 1) C j = 0 := by
    induction j with
    | zero => exact pilotMax_zero
    | succ j ih => rw [pilotMax_succ, ih, hU, sup_idem]
  exact hmax P.k

private theorem input_zero (P : HierarchyParams 2 1 1 1 0) :
    P.correctionInput (full (α := Unit)) (full (α := Unit)) 1 C 0 = C := by
  simp [HierarchyParams.correctionInput, HierarchyParams.correctionIter, cutoffCorrectionIter]

private noncomputable def sampling (P : HierarchyParams 2 1 1 1 0) :
    P.CorrectionSampling (full (α := Unit)) (full (α := Unit)) (full (α := Unit))
      (full (α := Bool)) hit 1 C 0 where
  I := fun _ _ => 0
  τ := fun _ => 1
  h := fun _ => 1
  ρ := fun _ => 1
  K := 8
  Kc := 16
  η := 1
  τ₀ := 0
  e := 0
  c := 1
  p := 1
  R := 3
  π := 1 / 2
  π_pos := by norm_num
  density z := by norm_num [hit, filter_eq', dens_eq_card_div_card]
  Q_support _ _ := rfl
  ρ_nonneg _ := zero_le_one
  ρ_le_one _ := le_rfl
  η_pos := one_pos
  ρ_one _ _ := rfl
  τ_nonneg _ := zero_le_one
  τ_le_one _ := le_rfl
  τ₀_nonneg := le_rfl
  τ_one _ _ := rfl
  I_zero _ _ _ := rfl
  c_nonneg := zero_le_one
  row_rank := by norm_num
  terminal_pair _ _ _ := by simp [full, hit]
  p_nonneg := zero_le_one
  source_pair _ _ _ := by simp [full]
  incoming_count z _ := by
    simpa only [one_mul] using
      (show (#({w : Fin 3 | 0 <
          P.correctionInput (full (α := Unit)) (full (α := Unit)) 1 C 0 w z / 1} :
          Finset (Fin 3)) : ℝ)
        ≤ 3 by exact_mod_cast card_le_univ _)
  incoming_rank := by norm_num

private theorem atom_eq (P : HierarchyParams 2 1 1 1 0) (hJ : 3 < P.J)
    (σ : Unit × Bool) (x z : Fin 3) :
    (sampling P).atom σ x z = if σ.2 = true then P.Q (C x z) else 0 := by
  have hγ : ∀ z,
      P.γ (P.pilot (full (α := Unit)) (full (α := Unit)) 1 C z) = 1 := by
    intro z
    rw [pilot_full _ hJ]
    exact P.γ_one 0 (by norm_num)
  norm_num [HierarchyParams.CorrectionSampling.atom, sampling, correctionAtom,
    correctionNormalizer,
    correctionPrep, rowGate, incomingGate, full, hit, hγ, input_zero, filter_eq']

-- There is a genuine positive actual correction and the sampled reward is nonconstant.
private theorem nonconstant_reward : ∃ P : FourthRootHierarchyParams 2 1 1 1 0,
    0 < P.toHierarchyParams.correctionIter (full (α := Unit)) (full (α := Unit)) 1 C 1 0 1 ∧
    (sampling P.toHierarchyParams).rewardSample 1 (fun _ => 1) ((), false) 0 = 1 ∧
    1 < (sampling P.toHierarchyParams).rewardSample 1 (fun _ => 1) ((), true) 0 := by
  obtain ⟨P⟩ := FourthRootHierarchyParams.nonempty (q := 2) (cπ := 1) (Cπ := 1)
    (Cpair := 1) (Cvar := 0) (by norm_num) (by norm_num)
  have hJ := detector_rank P
  have hQ : 0 < P.Q (1 / 2) := by
    have h := P.le_Q (1 / 2)
    have hθ := P.θ₂_lt
    norm_num at hθ
    linarith
  have hγ : P.γ (P.toHierarchyParams.pilot (full (α := Unit)) (full (α := Unit)) 1 C 1) = 1 := by
    rw [pilot_full _ hJ]
    exact P.γ_one 0 (by norm_num)
  refine ⟨P, ?_, ?_, ?_⟩
  · rw [HierarchyParams.correctionIter_succ_apply, input_zero, hγ]
    simpa only [C, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, div_one,
      one_mul, mul_one] using hQ
  · simp [HierarchyParams.CorrectionSampling.rewardSample, atom_eq _ hJ]
  · have hQ0 : P.Q 0 = 0 := by
      apply le_antisymm _ (P.Q_nonneg 0)
      simpa only [max_eq_right (by linarith [P.θ_pos] : (0 : ℝ) - P.θ ≤ 0)] using P.Q_le 0
    simp only [HierarchyParams.CorrectionSampling.rewardSample, atom_eq _ hJ]
    norm_num [sampling, C, Fin.sum_univ_three, hQ0]
    linarith

-- The deterministic product used in the omission theorem is also nonzero.
example (P : FourthRootHierarchyParams 2 1 1 1 0) :
    0 < (P.toHierarchyParams.correctionIter (full (α := Unit)) (full (α := Unit)) 1 C 1 * C)
      0 2 := by
  have hγ : P.γ (P.toHierarchyParams.pilot (full (α := Unit)) (full (α := Unit)) 1 C 1) = 1 := by
    rw [pilot_full _ (detector_rank P)]
    exact P.γ_one 0 (by norm_num)
  have hQ : 0 < P.Q (1 / 2) := by
    have h := P.le_Q (1 / 2)
    have hθ := P.θ₂_lt
    norm_num at hθ
    linarith
  have he : P.toHierarchyParams.correctionIter (full (α := Unit)) (full (α := Unit)) 1 C 1
      0 1 = P.Q (1 / 2) := by
    rw [HierarchyParams.correctionIter_succ_apply, input_zero, hγ]
    norm_num [C]
  simp only [Matrix.mul_apply, Fin.sum_univ_three]
  rw [he]
  norm_num [C]
  exact hQ

-- Apply the gate-derived mean theorem on the nontrivial Boolean midpoint space.
example (P : HierarchyParams 2 1 1 1 0) :
    (𝔼 σ ∈ (univ : Finset Unit) ×ˢ (univ : Finset Bool),
      (sampling P).rewardSample 1 (fun _ => 1) σ 0) =
        1 + (P.correctionIter (full (α := Unit)) (full (α := Unit)) 1 C 1 *ᵥ (fun _ => 1)) 0 := by
  simpa only [full, filter_true, one_mul] using
    (sampling P).expect_rewardSample one_pos C_nonneg C_row
      (x := 0) (by simp [full]) 1 (fun _ => 1)

-- Actual correction–bin omission, with row/entry hypotheses derived inside the theorem.
example (P : HierarchyParams 2 1 1 1 0) :
    Cslib.rowNormPow 4 3 1 (fun (_ : Unit × Unit) (_ : Fin 3) => True)
      (fun _ _ => True)
      (fun _ x y =>
        (P.correctionIter (full (α := Unit)) (full (α := Unit)) 1 C 1 * C) x y) ≤ 1 := by
  have h := P.correctionIter_mul_bin_omission_le (X := full (α := Unit)) (Y := full (α := Unit))
    (full (α := Unit)) (full (α := Unit)) one_pos C_nonneg C_row 1 (N := 3) (u := 1) (a := 1)
    (b := 1) (Cu := 1) (Ca := 1) (Cb := 1) (by norm_num) one_pos one_pos zero_le_one
    zero_le_one zero_le_one zero_le_one (by norm_num) (fun _ => by simp [full])
    (fun _ => by simp [full]) C C_nonneg (fun _ _ => le_rfl)
    (fun x y => by fin_cases x <;> fin_cases y <;> norm_num [C])
  simpa only [full, div_one, Nat.cast_one, mul_one, one_pow, one_div] using h

-- The actual product family is summed at exact cutoff equality (M = c * (1 + |h|)).
example (P : HierarchyParams 2 1 1 1 0) :
    ∑ _h ∈ ({-1} : Finset ℤ),
      (Cslib.rowNormPow 4 3 1 (fun (_ : Unit × Unit) (_ : Fin 3) => True)
        (fun _ _ => True) (fun _ x y =>
          (P.correctionIter (full (α := Unit)) (full (α := Unit)) 1 C 1 * C) x y)) ^
            (4⁻¹ : ℝ) ≤
      (2 : ℝ) ^ (1 / 2 - (2 : ℝ) / (2 * 1)) *
        (2 / (1 - (2 : ℝ) ^ (-(1 : ℝ) / 8)) - 1) := by
  have ht := P.sum_correctionIter_mul_bin_omission_norm_le
    (X := full (α := Unit)) (Y := full (α := Unit))
    (full (α := Unit)) (full (α := Unit)) one_pos C_nonneg C_row 1
    (N := 3) (u := 1) (a := 1) (Cu := 1) (Ca := 1) (Cb := 1) (Ksum := 1)
    (by norm_num) one_pos one_pos zero_le_one zero_le_one zero_le_one zero_le_one
    (by norm_num) (by norm_num) (fun _ => by simp [full]) (fun _ => by simp [full])
    2 1 (by decide) {-1} (fun _ => 1 / 2) (fun _ => C)
    (fun _ _ => by norm_num) (fun h hh => by
      obtain rfl := mem_singleton.mp hh
      norm_num)
    (fun h hh => by
      obtain rfl := mem_singleton.mp hh
      norm_num [Cslib.LogSpaceEstimation.scaleCutoff])
    (fun h hh => by
      obtain rfl := mem_singleton.mp hh
      simp only [div_one]
      rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.logb_inv,
        Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
      norm_num)
    (fun _ _ => C_nonneg) (fun _ _ _ _ => le_rfl)
    (fun _ _ x y => by fin_cases x <;> fin_cases y <;> norm_num [C])
  simpa only [full, div_one, one_mul, Nat.cast_ofNat, Nat.cast_one] using ht

-- The unified constructor reads its earlier normalized task; the existing nonconstant
-- Boolean sample is preserved for both zero and positive midpoint outcomes.
private theorem projectedRecipe_primary
    (P : FourthRootHierarchyParams 2 1 1 1 0) (σ : Unit × Bool) (x : Fin 3) :
    (sampling P.toHierarchyParams).projectedRewardRecipe (fun _ => 1) σ (toLex (x, 0)) =
      (sampling P.toHierarchyParams).rewardSample 1 (fun _ => 1) σ x := by
  rw [(sampling P.toHierarchyParams).projectedRewardRecipe_eq_rewardSample
    one_pos C_nonneg C_row
    (fun x y => by fin_cases x <;> fin_cases y <;> norm_num [C]) (Nat.zero_le _)]
  have hweight : P.toHierarchyParams.weight (full (α := Unit)) (full (α := Unit)) 1 C
      (0 : Fin (P.m + 1)) x = 1 := by
    rw [HierarchyParams.weight_eq]
    simp [detectorWeight]
  simp only [ofLex_toLex, hweight]

-- The complete normalized-child recipe really varies with its sampled midpoint.
example : ∃ P : FourthRootHierarchyParams 2 1 1 1 0,
    (sampling P.toHierarchyParams).projectedRewardRecipe (fun _ => 1)
      ((), false) (toLex (0, 0)) = 1 ∧
    1 < (sampling P.toHierarchyParams).projectedRewardRecipe (fun _ => 1)
      ((), true) (toLex (0, 0)) := by
  obtain ⟨P, _, hfalse, htrue⟩ := nonconstant_reward
  exact ⟨P, (projectedRecipe_primary P ((), false) 0).trans hfalse,
    (projectedRecipe_primary P ((), true) 0).symm ▸ htrue⟩

-- Nonprimary copy multipliers read arbitrary completed pilot values through the shared
-- weight equation, rather than only appearing as a rank label.
example (P : HierarchyParams 2 1 1 1 0) (j : Fin (P.m + 1)) (hj : j ≠ 0) (x : Fin 3) :
    (sampling P).value (fun _ => 1) .weights j x =
      P.κ ((sampling P).value (fun _ => 1) (.pilot (.pilot (.maximum P.k))) x) := by
  rw [(sampling P).value_weights]
  simp only [detectorWeight, ite_eq_right hj]

-- The true copy/reward value is the existing weighted projection of the actual correction.
example (P : HierarchyParams 2 1 1 1 0) (W : Fin 3 → ℝ) :
    (sampling P).value W (.projectedReward P.k) =
      P.proj (full (α := Unit)) (full (α := Unit)) 1 C *ᵥ
        (W + P.correction (full (α := Unit)) (full (α := Unit)) 1 C *ᵥ W) := by
  rw [(sampling P).value_projectedReward]
  simp only [HierarchyParams.CorrectionSampling.value, P.correctionIter_last]

-- A nonconstant earlier reward is consumed as a whole vertex function, with no retained
-- source argument or right endpoint in the task label.
example (P : HierarchyParams 2 1 1 1 0) :
    (sampling P).value (fun x => if x = 0 then 1 else 0) (.projectedReward P.k)
      (toLex (0, 0)) = 1 ∧
    (sampling P).value (fun x => if x = 0 then 1 else 0) (.projectedReward P.k)
      (toLex (2, 0)) = 0 := by
  have hw (x : Fin 3) : P.weight (full (α := Unit)) (full (α := Unit)) 1 C
      (0 : Fin (P.m + 1)) x = 1 := by
    rw [P.weight_eq]
    simp [detectorWeight]
  have hC : C.IsStrictUpperTriangular := by
    intro x y h
    fin_cases x <;> fin_cases y <;> norm_num [C] at *
  have htri := (P.isCorrectionSeq_correctionIter (X := full (α := Unit))
    (Y := full (α := Unit)) one_pos C_nonneg).isStrictUpperTriangular hC P.k
  have he (x : Fin 3) : P.correctionIter (full (α := Unit)) (full (α := Unit)) 1 C
      P.k x 0 = 0 := htri (by omega)
  simp [HierarchyParams.CorrectionSampling.value, mulVec, dotProduct, he, hw]

end ComplexityTests.HierarchyTaskMeans
