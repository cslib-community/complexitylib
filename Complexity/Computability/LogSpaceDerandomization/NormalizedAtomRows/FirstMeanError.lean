/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate
public import Complexity.Computability.LogSpaceDerandomization.HierarchyEstimatedMean
public import Complexity.Computability.LogSpaceDerandomization.NormalizedAtomRows.MeanBias

/-!
# First deterministic mean error after the completed raw walk

Stationarity of the full-terminal raw walk and first-prefix telescoping preserve the
absolute input mean error, divided by `rate k + G x y`. This gives the first clipped
mean envelope without converting a clipped relative bound back to an absolute bound.
The target is explicitly nonnegative. Second-signal preparation still requires the
full-rank maximum in `preparationError`; no recursive relative budget is proved here.
The first-prefix pattern is adapted from Samuel Schlesinger's compression API.
-/
public section
noncomputable section
namespace Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
open Finset Cslib Cslib.Probability Cslib.RowCompression
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {P J : ℕ} [Fact P.Prime]

/-- Actual first discrepancy of a completed raw walk: stationarity removes the walk,
while rate normalization is retained exactly. Empty conditioning slices are allowed. -/
theorem actualClippedMean_first_eq {E : Type*} [Fintype E] [Nonempty E]
    (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (s t : Fin J) (Ls La Lt : ℕ) (D : ZMod P) (ss st : List (ZMod P))
    (graphs : ℕ → ∀ x y, RotationMap
      (RetainedPairSlice (retainedMask s Ls D ss) (retainedMask t La D st) x y) E)
    (times : ℕ → ZMod P → ZMod P → ℕ)
    (input : ℕ → Environment P J → ZMod P → ZMod P → ℝ)
    (k : ℕ) (ζ : ℝ) (G : Matrix (ZMod P) (ZMod P) ℝ)
    (second : Environment P J → ZMod P → ℕ → ZMod P → ℝ)
    (i : ℕ) (x y : ZMod P) :
    let F := fun j => conditionalWalk (retainedMask s Ls D ss) (retainedMask t La D st)
      (graphs j) (times j) (input j)
    actualClippedMean HP s t Ls La Lt D ss st k G ζ
      (firstSignalIncrement F k second) (fun _ _ _ _ => 0) 0 i x y =
      min 1 (|rowSliceMean (retainedMask s Ls D ss) (retainedMask t La D st)
        (input (i + 1)) x y - G x y| / (rate k + G x y)) := by
  dsimp only
  unfold actualClippedMean twoMaskMean
  simp only [Fin.isValue, ↓reduceIte, actualPrefix_firstSignalIncrement _ _ _ (fun _ _ _ _ => 0)
    (by intros; rfl)]
  unfold rowSliceMean
  rw [← expect_div]
  change min 1 (|rowSliceMean _ _ (conditionalWalk _ _ _ _ _) x y / rate k -
    G x y / rate k| / (1 + G x y / rate k)) = _
  rw [rowSliceMean_conditionalWalk, ← sub_div, abs_div, abs_of_pos (rate_pos k), div_div]
  congr 2
  field_simp [(rate_pos k).ne']

/-- A matrix-unit absolute input mean bound gives the genuine first clipped mean
bound after any completed raw walk. This direction needs no upper bound on G. -/
theorem actualClippedMean_first_le {E : Type*} [Fintype E] [Nonempty E]
    (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (s t : Fin J) (Ls La Lt : ℕ) (D : ZMod P) (ss st : List (ZMod P))
    (graphs : ℕ → ∀ x y, RotationMap
      (RetainedPairSlice (retainedMask s Ls D ss) (retainedMask t La D st) x y) E)
    (times : ℕ → ZMod P → ZMod P → ℕ)
    (input : ℕ → Environment P J → ZMod P → ZMod P → ℝ)
    (k : ℕ) (ζ : ℝ) (G : Matrix (ZMod P) (ZMod P) ℝ)
    (second : Environment P J → ZMod P → ℕ → ZMod P → ℝ)
    (i : ℕ) (x y : ZMod P) (hG : 0 ≤ G x y) {error : ℝ}
    (he : |rowSliceMean (retainedMask s Ls D ss) (retainedMask t La D st)
      (input (i + 1)) x y - G x y| ≤ error) :
    let F := fun j => conditionalWalk (retainedMask s Ls D ss) (retainedMask t La D st)
      (graphs j) (times j) (input j)
    actualClippedMean HP s t Ls La Lt D ss st k G ζ
      (firstSignalIncrement F k second) (fun _ _ _ _ => 0) 0 i x y ≤
      min 1 (error / (rate k + G x y)) := by
  dsimp only
  rw [actualClippedMean_first_eq]
  exact min_le_min_left _ (div_le_div_of_nonneg_right he (add_nonneg (rate_pos k).le hG))

set_option backward.isDefEq.respectTransparency false in
/-- First deterministic envelope of the actual finite estimated residual, after its
completed full-terminal raw walk. Structural requests stay fixed across walk precisions.
Preparation is applied later; no full-rank maximum has been replaced by a usage maximum. -/
theorem actualEstimatedResidual_first_mean_le
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (D : ZMod P)
    (hD : D ≠ 0) (H : Horizon P) (R : RoleProfile J)
    (l ks km kt n : ℕ) (ksH : ks ≤ H.maxExponent) (hms : km ≤ ks)
    (ss sm st : List (ZMod P)) (kb : ℕ → ℕ)
    (hbH : ∀ i ∈ range (n + 1), kb i ≤ H.maxExponent)
    (C : Matrix (ZMod P) (ZMod P) ℝ) (hC : ∀ x y, 0 ≤ C x y) (hC1 : C *ᵥ 1 ≤ 1)
    (hCf : ∀ x y, C x y ≤ rate km)
    (χ : ℝ → ℝ) (hχ : ∀ v, 1 ≤ v → χ v = 1)
    (h : ℕ → ℝ → ℝ) (ρ : ℝ → ℝ) (K : ℕ)
    (hkh : ∀ i ∈ range (n + 1), ∀ v,
      routedBinCutoff χ (fun i => rate (kb i)) i (fun _ => 1) v ≠ 0 → h i v = 1)
    (hρ0 : ∀ v, 0 ≤ ρ v) (hρ1 : ∀ v, ρ v ≤ 1) {η : ℝ}
    (hη : 0 < η) (hρη : ∀ v, v ≤ η → ρ v = 1)
    (hK : 2 * (1 + 32 / η) ≤ K)
    (hχmono : Monotone χ) (hχ0 : ∀ v, v ≤ 1 / 2 → χ v = 0)
    (hχrange : ∀ v, χ v ∈ Set.Icc 0 1)
    (hanti : Antitone (fun i => rate (kb i)))
    (hratio : ∀ i, rate (kb i) / rate (kb (i + 1)) ≤ 16)
    {cap : ℝ} (hcap : 0 ≤ cap) (hCcap : ∀ z w, C z w ≤ cap * rate (kb 0))
    (Kc : ℕ)
    (raw prep : ℕ → ℕ → HierarchyTask.Request HP.k (Fin J) (ZMod P) →
      Environment P J → Matrix (ZMod P) (ZMod P) ℝ)
    (maximum : ℕ → ℕ → HierarchyTask.Request HP.k (Fin J) (ZMod P) →
      Environment P J → ZMod P → ℝ)
    (x y : ZMod P) (hcover : ∀ z, C z y = 0 ∨ rate (kb n) ≤ C z y)
    (steps : ℕ → ℕ) (ζ : ℝ)
    (second : Environment P J → ZMod P → ℕ → ZMod P → ℝ) (j : ℕ) :
    let cutoff := fun i => routedBinCutoff χ (fun i => rate (kb i)) i (fun _ => 1)
    let bounded := fun i => boundedRoutedBinCutoff χ (fun i => rate (kb i)) cap i (fun _ => 1)
    let source := gridChannel R.source ks ss
    let mid := gridChannel R.midpoint km sm
    let terminal := gridChannel R.terminal kt st
    let estimated := fun precision i σ r => incomingChildren HP D id Kc (bounded i)
      (raw precision i) (prep precision i) (maximum precision i) r σ
    let canonical := fun i σ r => canonicalRequestChild HP D id C
      (cutoff i) (h i) ρ K r σ
    let channelsV := fun role b suffix σ v => channels D role b suffix σ (id v)
    let S := ({σ : Environment P J | source.retains (channels D) σ (id x) ∧
      terminal.retains (channels D) σ (id y)} : Finset _)
    let input := estimatedResidualInput HP D id R l ks km kt n ss sm st kb Kc bounded
      raw prep maximum
    let G := HP.toHierarchyParams.residual (canonicalChannel id (rate km))
      (canonicalChannel id (rate km)) (rate km) C
    let F := fun j => conditionalWalk (retainedMask R.source (side P ks) D ss)
      (retainedMask R.terminal (side P kt) D st)
      (graph R.source R.terminal R.source_terminal (side P ks) (side P kt)
        (side_le P ks) (side_le P kt) (fun x => CopyPadding.identifier D ss x)
        (fun y => CopyPadding.identifier D st y)) (fun _ _ => steps j) (input j)
    actualClippedMean HP R.source R.terminal (side P ks) (side P kt) (side P kt)
      D ss st kt G ζ (firstSignalIncrement F kt second) (fun _ _ _ _ => 0) 0 j x y ≤
      min 1 ((𝔼 σ ∈ S, ((∑ i ∈ range (n + 1), HierarchyTask.positiveChildError channelsV
      l i .residual source mid terminal (rate (kb i))
      (2 * HP.Q HP.toHierarchyParams.atomCap) (2 * max cap 16)
      (estimated (j + 1) i σ) (canonical i σ) x y) +
      HierarchyTask.negativeChildError channelsV l 0 .residual source mid terminal
        (rate (kb 0)) (estimated (j + 1) 0 σ) (canonical 0 σ) x y)) / (rate kt + G x y)) := by
  dsimp only
  apply actualClippedMean_first_le
  · exact HP.toHierarchyParams.residual_nonneg (rate_pos km) hC x y
  · have he := estimated_residual_bins_mean_error HP D id hD Function.injective_id
      H R l ks km kt n ksH hms ss sm st kb hbH C hC hC1 hCf χ hχ h ρ K hkh
      hρ0 hρ1 hη hρη hK hχmono hχ0 hχrange hanti hratio hcap hCcap Kc
      (raw (j + 1)) (prep (j + 1)) (maximum (j + 1)) x y hcover
    dsimp only at he
    simpa only [estimatedResidualInput, rowSliceMean, CorrectionRowTask.Channel.retains,
      channels, gridChannel,
      semanticSide_grid, retainedMask, id_eq] using he

end Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
