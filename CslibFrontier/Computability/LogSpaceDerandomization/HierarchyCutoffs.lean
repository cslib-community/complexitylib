/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate
public import CslibFrontier.Computability.LogSpaceDerandomization.CorrectionRowTasks
public import CslibFrontier.Computability.LogSpaceDerandomization.PolynomialAtomCutoffs
public import CslibFrontier.Computability.LogSpaceDerandomization.PilotRowTasks

/-!
# Selected polynomial cutoffs for actual normalized correction and pilot tasks

These are original API bridges using the existing fourth-moment hierarchy construction
(by Samuel Schlesinger) and correction/pilot sampling constructors. No recursive noise or
native resource theorem is asserted. Incoming counts are derived by the existing detector.
-/
public section
open Finset Cslib
open scoped BigOperators
namespace Matrix.FourthRootHierarchyParams

variable (P : FourthRootHierarchyParams 16 1 16 32 8)

/-- The selected incoming gate uses the actual core copy thresholds. -/
@[expose] noncomputable def incomingCutoff (r : ℝ) : ℝ :=
  1 - polynomialSwitch4 P.τ₀ P.τ₁ r

theorem incomingCutoff_nonneg (r : ℝ) : 0 ≤ P.incomingCutoff r :=
  sub_nonneg.mpr (polynomialSwitch4_le_one _ _ _)

theorem incomingCutoff_le_one (r : ℝ) : P.incomingCutoff r ≤ 1 :=
  sub_le_self _ (polynomialSwitch4_nonneg _ _ _)

theorem incomingCutoff_one {r : ℝ} (hr : r ≤ P.τ₀) : P.incomingCutoff r = 1 := by
  rw [incomingCutoff, polynomialSwitch4_of_le (by rw [P.τ₀_eq, P.τ₁_eq]; norm_num) hr,
    sub_zero]

theorem incomingCutoff_zero {r : ℝ} (hr : P.τ₁ ≤ r) : P.incomingCutoff r = 0 := by
  rw [incomingCutoff, polynomialSwitch4_of_ge (by rw [P.τ₀_eq, P.τ₁_eq]; norm_num) hr,
    sub_self]

/-- Nonzero exact cutoff forces an entry strictly above the true threshold. -/
theorem theta_lt_of_Q_ne_zero {v : ℝ} (hv : P.Q v ≠ 0) : P.θ < v := by
  by_contra h
  have hb := P.Q_le v
  rw [max_eq_right (sub_nonpos.mpr (not_lt.mp h))] at hb
  exact hv (le_antisymm hb (P.Q_nonneg v))

/-- The actual row gate support lies strictly inside the auxiliary full-rank region. -/
theorem rank_lt_of_rho_ne_zero {r : ℝ} (hr : P.ρ r ≠ 0) : r < P.θ / 300 := by
  have h := lt_of_not_ge (fun h => hr (P.ρ_zero r h))
  linarith [P.η₂_lt, P.δ₀_lt_δ₁, P.δ₁_lt]

/-- Discharges the incoming support premise using the actual core row gate, not a surrogate. -/
theorem aux_full_on_Q_rho {v r : ℝ} (hv : P.Q v ≠ 0) (hr : P.ρ r ≠ 0) :
    polynomialAuxCutoff4 P.θ v r = 1 :=
  polynomialAuxCutoff4_eq_one P.θ_pos
    (by linarith [P.theta_lt_of_Q_ne_zero hv, P.θ_pos])
    (by linarith [P.rank_lt_of_rho_ne_zero hr, P.θ_pos])

theorem prep_full_on_Q {v : ℝ} (hv : P.Q v ≠ 0) :
    polynomialPrepCutoff4 P.θ v = 1 :=
  polynomialPrepCutoff4_eq_one P.θ_pos (by linarith [P.theta_lt_of_Q_ne_zero hv, P.θ_pos])

/-- Positive preparation and nonzero actual row gate also give full auxiliary score. -/
theorem aux_full_on_prep_rho {v r : ℝ}
    (hv : polynomialPrepCutoff4 P.θ v ≠ 0) (hr : P.ρ r ≠ 0) :
    polynomialAuxCutoff4 P.θ v r = 1 := by
  have hv' : P.θ / 2 < v :=
    lt_of_not_ge (fun h => hv (polynomialPrepCutoff4_eq_zero P.θ_pos h))
  exact polynomialAuxCutoff4_eq_one P.θ_pos (by linarith [P.θ_pos])
    (by linarith [P.rank_lt_of_rho_ne_zero hr, P.θ_pos])

/-- A genuine perturbation margin around the actual normalized Q/rho support.
Neither perturbed coordinate is assumed to remain in the original support. -/
theorem aux_full_near_Q_rho {v r v' r' : ℝ}
    (hv : P.Q v ≠ 0) (hr : P.ρ r ≠ 0)
    (hd : |v - v'| ≤ P.θ / 4) (hs : |r - r'| ≤ P.θ / 300) :
    polynomialAuxCutoff4 P.θ v' r' = 1 := by
  have hd' := (abs_sub_le_iff.mp hd).1
  have hs' := (abs_sub_le_iff.mp hs).2
  exact polynomialAuxCutoff4_eq_one P.θ_pos
    (by linarith [P.theta_lt_of_Q_ne_zero hv, P.θ_pos])
    (by linarith [P.rank_lt_of_rho_ne_zero hr, P.θ_pos])

/-- Preparation has its own explicit entry margin within the auxiliary full region. -/
theorem aux_full_near_prep_rho {v r v' r' : ℝ}
    (hv : polynomialPrepCutoff4 P.θ v ≠ 0) (hr : P.ρ r ≠ 0)
    (hd : |v - v'| ≤ P.θ / 8) (hs : |r - r'| ≤ P.θ / 300) :
    polynomialAuxCutoff4 P.θ v' r' = 1 := by
  have hv' : P.θ / 2 < v :=
    lt_of_not_ge (fun h => hv (polynomialPrepCutoff4_eq_zero P.θ_pos h))
  have hd' := (abs_sub_le_iff.mp hd).1
  have hs' := (abs_sub_le_iff.mp hs).2
  exact polynomialAuxCutoff4_eq_one P.θ_pos (by linarith [P.θ_pos])
    (by linarith [P.rank_lt_of_rho_ne_zero hr, P.θ_pos])

/-- The broader witness is full on positive auxiliary support. -/
theorem witness_full_on_aux {v r : ℝ} (h : polynomialAuxCutoff4 P.θ v r ≠ 0) :
    polynomialWitnessCutoff4 P.θ v r = 1 := by
  have hv : P.θ / 8 < v := lt_of_not_ge
    (fun hv => h (polynomialAuxCutoff4_eq_zero_of_entry_le P.θ_pos hv))
  have hr : r < P.θ / 50 := lt_of_not_ge
    (fun hr => h (polynomialAuxCutoff4_eq_zero_of_rank_ge P.θ_pos hr))
  exact polynomialWitnessCutoff4_eq_one P.θ_pos (by linarith [P.θ_pos])
    (by linarith [P.θ_pos])

theorem aux_zero_on_detector {v r : ℝ} (hv : v ≤ P.δ₁) :
    polynomialAuxCutoff4 P.θ v r = 0 :=
  polynomialAuxCutoff4_eq_zero_of_entry_le P.θ_pos (by linarith [P.δ₁_lt, P.θ_pos])

private theorem τ₁_le_one : P.τ₁ ≤ 1 := by
  rw [P.τ₁_eq]
  norm_num

/-- The incoming column cap `⌈4 (1 + 32 R)⌉₊` of the correction and pilot samplers is positive,
since `4 J ≤ R` (`R_rank`). -/
theorem incomingCap_pos : 0 < ⌈4 * (1 + 32 * P.R)⌉₊ := by
  have h := P.R_rank
  norm_num only [one_mul] at h
  exact Nat.ceil_pos.mpr (by linarith [(Nat.cast_nonneg P.J : (0 : ℝ) ≤ P.J)])

section Clients
universe u
variable {V ι κ : Type u} [Fintype V] [Fintype ι] [Fintype κ]
  (X : ι → V → Prop) (Y : κ → V → Prop)
  [∀ s v, Decidable (X s v)] [∀ t v, Decidable (Y t v)]
  {f π : ℝ} {C : Matrix V V ℝ} {i : ℕ}

/-- Actual pilot sampling data: the incoming count comes from the existing detector theorem. -/
noncomputable def pilotSampling
    (hXY : Probability.RetentionChannels X Y f π 1 16 32 8)
    (hYX : Probability.RetentionChannels Y X f π 1 16 32 8)
    (hf : 0 < f) (hπ : 0 < π) (hC : ∀ x y, 0 ≤ C x y)
    (hC1 : C *ᵥ 1 ≤ 1) (hi : i < P.k) :
    P.toHierarchyParams.PilotSampling X Y X Y Y f C i :=
  HierarchyParams.PilotSampling.ofChannels P X Y hXY hYX hf hπ (by norm_num)
    (by norm_num) hC hC1 hi (polynomialAuxCutoff4 P.θ) P.incomingCutoff
    (polynomialPrepCutoff4 P.θ) P.τ₀ (fun _ => P.prep_full_on_Q)
    P.incomingCutoff_nonneg P.incomingCutoff_le_one (by rw [P.τ₀_eq]; norm_num)
    (fun _ => P.incomingCutoff_one) (fun _ _ => P.aux_zero_on_detector)

/-- Actual correction sampling data with the final pilot multiplier and derived incoming count. -/
noncomputable def correctionSampling
    (hXY : Probability.RetentionChannels X Y f π 1 16 32 8)
    (hYX : Probability.RetentionChannels Y X f π 1 16 32 8)
    (hf : 0 < f) (hπ : 0 < π) (hC : ∀ x y, 0 ≤ C x y)
    (hC1 : C *ᵥ 1 ≤ 1) (hi : i < P.k) :
    P.toHierarchyParams.CorrectionSampling X Y X Y Y f C i :=
  HierarchyParams.CorrectionSampling.ofChannels P X Y hXY hYX hf hπ (by norm_num)
    (by norm_num) hC hC1 hi (polynomialAuxCutoff4 P.θ) P.incomingCutoff
    (polynomialPrepCutoff4 P.θ) P.τ₀ (fun _ => P.prep_full_on_Q)
    P.incomingCutoff_nonneg P.incomingCutoff_le_one (by rw [P.τ₀_eq]; norm_num)
    (fun _ => P.incomingCutoff_one) (fun _ _ => P.aux_zero_on_detector)

/-- Arbitrary raw/preparatory/vector children retain the actual normalized incoming cap.
The bounded atom cutoff is the hierarchy's actual Qat; ranks read the raw table. -/
theorem normalized_col_support (Yt : κ → V → Prop) [∀ t v, Decidable (Yt t v)]
    (K Kc : ℕ) (hKc : 0 < Kc) (f : ℝ)
    (input : Matrix V V ℝ) (prep : ι × κ → Matrix V V ℝ) (maximum : V → ℝ)
    (σ : ι × κ) (y : V) :
    #{x ∈ ({w | X σ.1 w} : Finset V) |
      CorrectionRowRecipe.normalized (polynomialAuxCutoff4 P.θ) P.incomingCutoff P.ρ
        P.toHierarchyParams.atomCutoff P.γ K Kc f X Y Yt input prep maximum σ x y ≠ 0} < Kc := by
  apply CorrectionRowRecipe.card_filter_normalized_col_ne_zero_lt
    (polynomialAuxCutoff4 P.θ) P.incomingCutoff P.ρ P.toHierarchyParams.atomCutoff
    P.γ K Kc f X Y Yt input prep maximum σ y hKc
  · intro v r hv hr
    exact P.aux_full_on_Q_rho (fun h => hv
      (P.toHierarchyParams.atomCutoff_eq_zero_of_Q_eq_zero h)) hr
  · exact P.τ₁_le_one
  · intro r hr
    exact P.incomingCutoff_zero hr

variable
    (hXY : Probability.RetentionChannels X Y f π 1 16 32 8)
    (hYX : Probability.RetentionChannels Y X f π 1 16 32 8)
    (hf : 0 < f) (hπ : 0 < π) (hC : ∀ x y, 0 ≤ C x y)
    (hC1 : C *ᵥ 1 ≤ 1) (hi : i < P.k)

/-- The selected sampler uses the supplied terminal density. -/
theorem selected_pi : (P.correctionSampling X Y hXY hYX hf hπ hC hC1 hi).π = π := by
  simp only [correctionSampling, HierarchyParams.CorrectionSampling.ofChannels_π]

/-- The selected sampler's incoming budget is based on the true stage source rate. -/
theorem selected_p : (P.correctionSampling X Y hXY hYX hf hπ hC hC1 hi).p = 32 * f := by
  simp only [correctionSampling, HierarchyParams.CorrectionSampling.ofChannels_p]

/-- The selected sampler retains the frame terminal pair constant. -/
theorem selected_c : (P.correctionSampling X Y hXY hYX hf hπ hC hC1 hi).c = 32 := by
  simp only [correctionSampling, HierarchyParams.CorrectionSampling.ofChannels_c]

/-- The selected sampler uses its prescribed I parameter. -/
theorem selected_I : (P.correctionSampling X Y hXY hYX hf hπ hC hC1 hi).I =
    polynomialAuxCutoff4 P.θ := by
  simp only [correctionSampling, HierarchyParams.CorrectionSampling.ofChannels_I]

/-- The selected sampler uses its prescribed τ parameter. -/
theorem selected_τ : (P.correctionSampling X Y hXY hYX hf hπ hC hC1 hi).τ =
    P.incomingCutoff := by
  simp only [correctionSampling, HierarchyParams.CorrectionSampling.ofChannels_τ]

/-- The selected sampler uses its prescribed h parameter. -/
theorem selected_h : (P.correctionSampling X Y hXY hYX hf hπ hC hC1 hi).h =
    polynomialPrepCutoff4 P.θ := by
  simp only [correctionSampling, HierarchyParams.CorrectionSampling.ofChannels_h]

/-- The selected sampler uses its prescribed ρ parameter. -/
theorem selected_ρ : (P.correctionSampling X Y hXY hYX hf hπ hC hC1 hi).ρ =
    P.ρ := by
  simp only [correctionSampling, HierarchyParams.CorrectionSampling.ofChannels_ρ]

/-- The selected sampler uses its prescribed K parameter. -/
theorem selected_K : (P.correctionSampling X Y hXY hYX hf hπ hC hC1 hi).K =
    P.K := by
  simp only [correctionSampling, HierarchyParams.CorrectionSampling.ofChannels_K]

/-- The selected sampler uses its prescribed Kc parameter. -/
theorem selected_Kc : (P.correctionSampling X Y hXY hYX hf hπ hC hC1 hi).Kc =
    ⌈4 * (1 + 32 * P.R)⌉₊ := by
  simp only [correctionSampling, HierarchyParams.CorrectionSampling.ofChannels_Kc]

/-- Preparation uses precisely the selected cutoffs and detector ranks. -/
theorem selected_preparation (input : Matrix V V ℝ) :
    (P.correctionSampling X Y hXY hYX hf hπ hC hC1 hi).preparationRecipe input =
      CorrectionRowRecipe.preparation (polynomialAuxCutoff4 P.θ) P.incomingCutoff
        (polynomialPrepCutoff4 P.θ) P.ρ P.K ⌈4 * (1 + 32 * P.R)⌉₊ f X Y input := by
  unfold HierarchyParams.CorrectionSampling.preparationRecipe
  simp only [correctionSampling, HierarchyParams.CorrectionSampling.ofChannels_I,
    HierarchyParams.CorrectionSampling.ofChannels_τ,
    HierarchyParams.CorrectionSampling.ofChannels_h,
    HierarchyParams.CorrectionSampling.ofChannels_ρ,
    HierarchyParams.CorrectionSampling.ofChannels_K,
    HierarchyParams.CorrectionSampling.ofChannels_Kc]

/-- Normalization uses precisely the selected cutoffs and actual bounded atom. -/
theorem selected_normalized (input : Matrix V V ℝ) (prep : ι × κ → Matrix V V ℝ)
    (maximum : V → ℝ) :
    (P.correctionSampling X Y hXY hYX hf hπ hC hC1 hi).normalizedRecipe input prep maximum =
      CorrectionRowRecipe.normalized (polynomialAuxCutoff4 P.θ) P.incomingCutoff P.ρ
        P.toHierarchyParams.atomCutoff P.γ P.K ⌈4 * (1 + 32 * P.R)⌉₊ f X Y Y
        input prep maximum := by
  unfold HierarchyParams.CorrectionSampling.normalizedRecipe
  simp only [correctionSampling, HierarchyParams.CorrectionSampling.ofChannels_I,
    HierarchyParams.CorrectionSampling.ofChannels_τ,
    HierarchyParams.CorrectionSampling.ofChannels_ρ,
    HierarchyParams.CorrectionSampling.ofChannels_K,
    HierarchyParams.CorrectionSampling.ofChannels_Kc]

/-- Preparation uses precisely the selected cutoffs and detector ranks. -/
theorem selectedPilot_preparation (input : Matrix V V ℝ) :
    (P.pilotSampling X Y hXY hYX hf hπ hC hC1 hi).preparationRecipe input =
      CorrectionRowRecipe.preparation (polynomialAuxCutoff4 P.θ) P.incomingCutoff
        (polynomialPrepCutoff4 P.θ) P.ρ P.K ⌈4 * (1 + 32 * P.R)⌉₊ f X Y input := by
  unfold HierarchyParams.PilotSampling.preparationRecipe
  simp only [pilotSampling, HierarchyParams.PilotSampling.ofChannels_I,
    HierarchyParams.PilotSampling.ofChannels_τ,
    HierarchyParams.PilotSampling.ofChannels_h,
    HierarchyParams.PilotSampling.ofChannels_ρ,
    HierarchyParams.PilotSampling.ofChannels_K,
    HierarchyParams.PilotSampling.ofChannels_Kc]

/-- Normalization uses precisely the selected cutoffs and actual bounded atom. -/
theorem selectedPilot_normalized (input : Matrix V V ℝ) (prep : ι × κ → Matrix V V ℝ)
    (maximum : V → ℝ) :
    (P.pilotSampling X Y hXY hYX hf hπ hC hC1 hi).normalizedRecipe input prep maximum =
      CorrectionRowRecipe.normalized (polynomialAuxCutoff4 P.θ) P.incomingCutoff P.ρ
        P.toHierarchyParams.atomCutoff P.γ P.K ⌈4 * (1 + 32 * P.R)⌉₊ f X Y Y
        input prep maximum := by
  unfold HierarchyParams.PilotSampling.normalizedRecipe
  simp only [pilotSampling, HierarchyParams.PilotSampling.ofChannels_I,
    HierarchyParams.PilotSampling.ofChannels_τ,
    HierarchyParams.PilotSampling.ofChannels_ρ,
    HierarchyParams.PilotSampling.ofChannels_K,
    HierarchyParams.PilotSampling.ofChannels_Kc]

/-- The correction client discharges incoming-cap hypotheses on arbitrary children. -/
theorem correction_col_support
    (input : Matrix V V ℝ) (prep : ι × κ → Matrix V V ℝ) (maximum : V → ℝ)
    (σ : ι × κ) (y : V) :
    let A := P.correctionSampling X Y hXY hYX hf hπ hC hC1 hi
    #{x ∈ ({w | X σ.1 w} : Finset V) |
      A.normalizedRecipe input prep maximum σ x y ≠ 0} < A.Kc := by
  dsimp only
  apply HierarchyParams.CorrectionSampling.card_filter_normalizedRecipe_col_ne_zero_lt
    _ input prep maximum σ y
  · simpa only [correctionSampling, HierarchyParams.CorrectionSampling.ofChannels_Kc] using
      P.incomingCap_pos
  · simp only [correctionSampling, HierarchyParams.CorrectionSampling.ofChannels_I,
      HierarchyParams.CorrectionSampling.ofChannels_ρ]
    exact fun _ _ hv hr => P.aux_full_on_Q_rho hv hr
  · exact P.τ₁_le_one
  · simp only [correctionSampling, HierarchyParams.CorrectionSampling.ofChannels_τ]
    exact fun _ hr => P.incomingCutoff_zero hr

/-- The same selected functions discharge the actual pilot recipe's column cap. -/
theorem pilot_col_support
    (input : Matrix V V ℝ) (prep : ι × κ → Matrix V V ℝ) (maximum : V → ℝ)
    (σ : ι × κ) (y : V) :
    let A := P.pilotSampling X Y hXY hYX hf hπ hC hC1 hi
    #{x ∈ ({w | X σ.1 w} : Finset V) |
      A.normalizedRecipe input prep maximum σ x y ≠ 0} < A.Kc := by
  dsimp only
  apply HierarchyParams.PilotSampling.card_filter_normalizedRecipe_col_ne_zero_lt
    _ input prep maximum σ y
  · simpa only [pilotSampling, HierarchyParams.PilotSampling.ofChannels_Kc] using
      P.incomingCap_pos
  · simp only [pilotSampling, HierarchyParams.PilotSampling.ofChannels_I,
      HierarchyParams.PilotSampling.ofChannels_ρ]
    exact fun _ _ hv hr => P.aux_full_on_Q_rho hv hr
  · exact P.τ₁_le_one
  · simp only [pilotSampling, HierarchyParams.PilotSampling.ofChannels_τ]
    exact fun _ hr => P.incomingCutoff_zero hr

/-- True normalized rows from the selected correction constructor have the genuine iterate mean. -/
theorem correction_mean (hCf : ∀ x y, C x y ≤ f)
    {x : V} (hx : ({s | X s x} : Finset ι).Nonempty) (y : V) :
    let A := P.correctionSampling X Y hXY hYX hf hπ hC hC1 hi
    (𝔼 σ ∈ ({s | X s x} : Finset ι) ×ˢ (univ : Finset κ),
      (f / A.π) * A.normalizedRecipe (P.toHierarchyParams.correctionInput X Y f C i)
        (A.preparationRecipe (P.toHierarchyParams.correctionInput X Y f C i))
        (HierarchyParams.PilotTask.value P.toHierarchyParams X Y f C (.maximum P.k)) σ x y) =
      P.toHierarchyParams.correctionIter X Y f C (i + 1) x y :=
  (P.correctionSampling X Y hXY hYX hf hπ hC hC1 hi).expect_normalizedRecipe
    hf hC hC1 hCf hi.le hx y
end Clients

/-- Regularity of the selected incoming gate reuses the existing complementary root theorem. -/
theorem incomingCutoff_root :
    ∃ K, LipschitzWith K fun r => P.incomingCutoff r ^ (4⁻¹ : ℝ) :=
  exists_lipschitzWith_one_sub_polynomialSwitch4_root P.τ₀ P.τ₁

theorem incomingCutoff_complement_root :
    ∃ K, LipschitzWith K fun r => (1 - P.incomingCutoff r) ^ (4⁻¹ : ℝ) := by
  simpa only [incomingCutoff, sub_sub_cancel] using
    exists_lipschitzWith_polynomialSwitch4_root P.τ₀ P.τ₁
end Matrix.FourthRootHierarchyParams
