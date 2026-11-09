/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import CslibFrontier.Computability.LogSpaceDerandomization.NormalizedAtomRows.SecondSignal
public import CslibFrontier.Computability.LogSpaceDerandomization.DenseRowRecipes.Stability

/-!
# Actual preparation mean bias from absolute residual errors

The selected preparation uses a supplied completed raw child. The actual wiring client
uses the conditional-walk-smoothed incoming-normalized signed lower-child residual.
Its comparison target is `genuinePrep`, with the same full terminal rank slice on the same
full environment. Conditional averaging uses source × usage, preserving correlations and
inherited copy suffixes. Stationarity identifies the selected input mean of the ζ-scaled
second telescoping prefix. Mixing alone does not change this deterministic bias.

These original bounds require explicit absolute residual errors; they do not derive them
from recursive relative estimates, row mass or clipped relative errors. Numerical recursive
mean envelopes, reserve induction and native RL=L remain open. The telescoping proof pattern
is adapted from Samuel Schlesinger's compression API.
-/

public section
namespace Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
open Finset Cslib Cslib.Probability Cslib.RowCompression
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
variable {P J : ℕ} [Fact P.Prime]

/-- Actual cutoff regularity, retaining the hierarchy's own rho rather than replacing it
with a polynomial gate. The two constants multiply entry and rank errors separately. -/
theorem preparation_stability_constants (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ∃ Lh Lρ : ℝ, 0 ≤ Lh ∧ 0 ≤ Lρ ∧
      (∀ a b, |polynomialPrepCutoff4 HP.θ a - polynomialPrepCutoff4 HP.θ b| ≤ Lh * |a - b|) ∧
      (∀ a b, |HP.ρ a - HP.ρ b| ≤ Lρ * |a - b|) := by
  obtain ⟨Lh, hh⟩ := exists_lipschitzWith_polynomialSwitch4_root (HP.θ / 2) (3 * HP.θ / 4)
  obtain ⟨⟨Lρ, hρ⟩, _⟩ := HP.cutoff_roots HP.ρ (by simp)
  refine ⟨4 * Lh, 4 * Lρ, by positivity, by positivity, ?_, ?_⟩
  · exact abs_sub_le_four_mul_root_lipschitz
      (fun z => ⟨polynomialPrepCutoff4_nonneg _ _, polynomialPrepCutoff4_le_one _ _⟩) hh
  · exact abs_sub_le_four_mul_root_lipschitz (fun z => ⟨HP.ρ_nonneg z, HP.ρ_le_one z⟩) hρ

/-- Exact absolute residual-error envelope. The maximum is over the full terminal rank
slice, never the narrower usage slice. Signed entries and empty ranks are allowed. -/
@[expose] def preparationError (R : RoleProfile J) (D : ZMod P) (st : List (ZMod P))
    (k : ℕ) (Lh Lρ : ℝ) (A : Environment P J → Matrix (ZMod P) (ZMod P) ℝ)
    (G : Matrix (ZMod P) (ZMod P) ℝ) (σ : Environment P J) (x y : ZMod P) : ℝ :=
  (Lh * |A σ x y - G x y| + Lρ * kthLargest 1
    {w | retainedMask R.terminal (side P k) D st σ w} (fun w => |A σ x w - G x w|)) / rate k

/-- The completed raw-child error is exactly the absolute first-prefix error times its
rate. The maximum still ranges over the full terminal slice, including empty ranks.
This identity makes no inference from a clipped relative-error bound. -/
lemma preparationError_eq_firstPrefix
    (R : RoleProfile J) (D : ZMod P) (st : List (ZMod P)) (k : ℕ) (Lh Lρ : ℝ)
    (F : ℕ → Environment P J → ZMod P → ZMod P → ℝ)
    (second : Environment P J → ZMod P → ℕ → ZMod P → ℝ)
    (G : Matrix (ZMod P) (ZMod P) ℝ) (i : ℕ) (σ : Environment P J) (x y : ZMod P) :
    preparationError R D st k Lh Lρ (fun τ a b => F (i + 1) τ a b) G σ x y =
      (Lh * (rate k * |actualPrefix (firstSignalIncrement F k second)
        (fun _ _ _ _ => 0) i σ x y 0 - G x y / rate k|) +
      Lρ * kthLargest 1 {w | retainedMask R.terminal (side P k) D st σ w}
        (fun w => rate k * |actualPrefix (firstSignalIncrement F k second)
          (fun _ _ _ _ => 0) i σ x w 0 - G x w / rate k|)) / rate k := by
  simp only [preparationError, firstSignal_raw_error F k second G i]

/-- Explicit absolute entry/rank envelopes bound the actual preparation error. No bound
on the true row is required. The rank envelope is nonnegative also for an empty rank. -/
lemma preparationError_le (R : RoleProfile J) (D : ZMod P) (st : List (ZMod P)) (k : ℕ)
    {Lh Lρ : ℝ} (hLh : 0 ≤ Lh) (hLρ : 0 ≤ Lρ)
    (A : Environment P J → Matrix (ZMod P) (ZMod P) ℝ)
    (G : Matrix (ZMod P) (ZMod P) ℝ) (σ : Environment P J) (x y : ZMod P)
    {e m : ℝ} (hm : 0 ≤ m) (he : |A σ x y - G x y| ≤ e)
    (hrow : ∀ w, retainedMask R.terminal (side P k) D st σ w → |A σ x w - G x w| ≤ m) :
    preparationError R D st k Lh Lρ A G σ x y ≤ (Lh * e + Lρ * m) / rate k := by
  unfold preparationError
  apply div_le_div_of_nonneg_right _ (rate_pos k).le
  exact add_le_add (mul_le_mul_of_nonneg_left he hLh)
    (mul_le_mul_of_nonneg_left (kthLargest_le hm fun w hw => hrow w (mem_filter.mp hw).2) hLρ)

/-- Exact zero residual perturbation has zero error, including an empty full-rank slice. -/
@[simp] lemma preparationError_self (R : RoleProfile J) (D : ZMod P)
    (st : List (ZMod P)) (k : ℕ) (Lh Lρ : ℝ)
    (G : Matrix (ZMod P) (ZMod P) ℝ) (σ : Environment P J) (x y : ZMod P) :
    preparationError R D st k Lh Lρ (fun _ => G) G σ x y = 0 := by
  have hz (S : Finset (ZMod P)) : kthLargest 1 S (fun _ => (0 : ℝ)) = 0 :=
    le_antisymm (kthLargest_le le_rfl (fun _ _ => le_rfl)) kthLargest_nonneg
  simp only [preparationError, sub_self, abs_zero, mul_zero, hz, add_zero, zero_div]

/-- Pointwise genuine-target comparison for arbitrary signed full-environment residuals. -/
theorem preparation_sub_genuinePrep_le
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (hK : 0 < HP.K)
    (R : RoleProfile J) (D : ZMod P) (st : List (ZMod P)) (k : ℕ)
    {Lh Lρ : ℝ}
    (hh : ∀ a b, |polynomialPrepCutoff4 HP.θ a - polynomialPrepCutoff4 HP.θ b| ≤ Lh * |a - b|)
    (hρ : ∀ a b, |HP.ρ a - HP.ρ b| ≤ Lρ * |a - b|)
    (A : Environment P J → Matrix (ZMod P) (ZMod P) ℝ)
    (G : Matrix (ZMod P) (ZMod P) ℝ) (σ : Environment P J) (x y : ZMod P) :
    |DenseRowRecipe.preparation (polynomialPrepCutoff4 HP.θ) HP.ρ HP.K (rate k)
      (retainedMask R.terminal (side P k) D st) (A σ) σ x y -
      genuinePrep HP R.terminal D st k G σ x y| ≤ preparationError R D st k Lh Lρ A G σ x y := by
  have hLρ : 0 ≤ Lρ := (abs_nonneg _).trans (by simpa using hρ 1 0)
  simp only [genuinePrep, DenseRowRecipe.preparation, preparationError, retainedMask]
  have hb := DenseRowRecipe.atomPrep_stability
    (fun z => ⟨polynomialPrepCutoff4_nonneg _ _, polynomialPrepCutoff4_le_one _ _⟩)
    (fun z => ⟨HP.ρ_nonneg z, HP.ρ_le_one z⟩) hh hρ hLρ hK (rate_pos k) (A σ) G
      {w | frameRetains P 4 (side P k) (σ R.terminal) (CopyPadding.identifier D st w)} x y
  convert hb using 1 <;> congr 8

/-- Joint-slice integration against the actual genuine target. No source/usage
independence or desired preparation mean is assumed; empty slices contribute zero. -/
theorem preparation_mean_bias_le
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (hK : 0 < HP.K)
    (R : RoleProfile J) (D : ZMod P) (ss st : List (ZMod P)) (ks k kt : ℕ)
    {Lh Lρ : ℝ}
    (hh : ∀ a b, |polynomialPrepCutoff4 HP.θ a - polynomialPrepCutoff4 HP.θ b| ≤ Lh * |a - b|)
    (hρ : ∀ a b, |HP.ρ a - HP.ρ b| ≤ Lρ * |a - b|)
    (A : Environment P J → Matrix (ZMod P) (ZMod P) ℝ)
    (G : Matrix (ZMod P) (ZMod P) ℝ) (x y : ZMod P) :
    |rowSliceMean (retainedMask R.source (side P ks) D ss)
      (retainedMask R.terminal (side P kt) D st)
      (fun σ => DenseRowRecipe.preparation (polynomialPrepCutoff4 HP.θ) HP.ρ HP.K (rate k)
        (retainedMask R.terminal (side P k) D st) (A σ) σ) x y -
      genuineMean HP R.source R.terminal (side P ks) (side P kt)
        (CopyPadding.identifier D ss x) D st k G x y| ≤
    rowSliceMean (retainedMask R.source (side P ks) D ss)
      (retainedMask R.terminal (side P kt) D st) (preparationError R D st k Lh Lρ A G) x y := by
  let S : Finset (Environment P J) := {σ | retainedMask R.source (side P ks) D ss σ x ∧
    retainedMask R.terminal (side P kt) D st σ y}
  let T := fun σ => DenseRowRecipe.preparation (polynomialPrepCutoff4 HP.θ) HP.ρ HP.K (rate k)
    (retainedMask R.terminal (side P k) D st) (A σ) σ x y
  have hb := (abs_expect_le S (fun σ => T σ - genuinePrep HP R.terminal D st k G σ x y)).trans
    (expect_le_expect fun σ _ =>
      preparation_sub_genuinePrep_le HP hK R D st k hh hρ A G σ x y)
  simp only [expect_sub_distrib, S, T, genuineMean, rowSliceMean, retainedMask] at hb ⊢
  convert hb using 1
  congr 8

/-- Stationarity and telescoping isolate the actual second deterministic discrepancy.
The first coordinate and its raw full-rank target are retained unchanged. -/
lemma actualClippedMean_second_eq {E : Type*} [Fintype E] [Nonempty E]
    (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (s t : Fin J) (Ls La Lt : ℕ) (D : ZMod P) (ss st : List (ZMod P))
    (graphs : ℕ → ∀ x y, RotationMap
      (RetainedPairSlice (retainedMask s Ls D ss) (retainedMask t Lt D st) x y) E)
    (times : ℕ → ZMod P → ZMod P → ℕ)
    (input F : ℕ → Environment P J → ZMod P → ZMod P → ℝ)
    (k : ℕ) (ζ : ℝ) (G : Matrix (ZMod P) (ZMod P) ℝ) (i : ℕ) (x y : ZMod P) :
    let H := fun j => conditionalWalk (retainedMask s Ls D ss) (retainedMask t Lt D st)
      (graphs j) (times j) (input j)
    actualClippedMean HP s t Ls La Lt D ss st k G ζ
      (firstSignalIncrement F k (secondSignalIncrement H ζ)) (fun _ _ _ _ => 0) 1 i x y =
    min 1 (|ζ| * |rowSliceMean (retainedMask s Ls D ss) (retainedMask t Lt D st)
      (input (i + 1)) x y - genuineMean HP s t Ls Lt
        (CopyPadding.identifier D ss x) D st k G x y|) := by
  dsimp only
  unfold actualClippedMean twoMaskMean
  simp only [Fin.isValue, one_ne_zero, ↓reduceIte, actualPrefix_twoSignal_second]
  unfold rowSliceMean
  rw [← mul_expect]
  change min 1 |ζ * rowSliceMean _ _ (conditionalWalk _ _ _ _ _) x y - ζ * _| = _
  rw [rowSliceMean_conditionalWalk, ← mul_sub, abs_mul]
  rfl

/-- Completed raw-child errors pay the clipped second deterministic mean discrepancy.
All child requests and their correlations survive in A; the envelope is an average of
absolute residual errors, with the full-rank maximum and the rate divisor explicit. -/
theorem actualSelectedSecondSignal_mean_bias_le {E : Type*} [Fintype E] [Nonempty E]
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (hK : 0 < HP.K)
    (D : ZMod P) (R : RoleProfile J) (ks k kt : ℕ) (_husage : k ≤ kt)
    (ss st : List (ZMod P))
    (A : ℕ → Environment P J → Matrix (ZMod P) (ZMod P) ℝ)
    (graphs : ℕ → ∀ x y, RotationMap
      (RetainedPairSlice (retainedMask R.source (side P ks) D ss)
        (retainedMask R.terminal (side P kt) D st) x y) E)
    (times : ℕ → ZMod P → ZMod P → ℕ)
    (F : ℕ → Environment P J → ZMod P → ZMod P → ℝ)
    {Lh Lρ : ℝ} (_hLρ : 0 ≤ Lρ)
    (hh : ∀ a b, |polynomialPrepCutoff4 HP.θ a - polynomialPrepCutoff4 HP.θ b| ≤ Lh * |a - b|)
    (hρ : ∀ a b, |HP.ρ a - HP.ρ b| ≤ Lρ * |a - b|)
    (ζ : ℝ) (G : Matrix (ZMod P) (ZMod P) ℝ) (i : ℕ) (x y : ZMod P) :
    let T := fun j σ x y => selectedPreparation HP D R st k (A j) σ x y
    let H := fun j => conditionalWalk (retainedMask R.source (side P ks) D ss)
      (retainedMask R.terminal (side P kt) D st) (graphs j) (times j) (T j)
    actualClippedMean HP R.source R.terminal (side P ks) (side P k) (side P kt) D ss st k G ζ
      (firstSignalIncrement F k (secondSignalIncrement H ζ)) (fun _ _ _ _ => 0) 1 i x y ≤
      min 1 (|ζ| * rowSliceMean (retainedMask R.source (side P ks) D ss)
        (retainedMask R.terminal (side P kt) D st)
        (preparationError R D st k Lh Lρ (A (i + 1)) G) x y) := by
  dsimp only
  rw [actualClippedMean_second_eq]
  apply min_le_min_left
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg ζ)
  exact preparation_mean_bias_le HP hK R D ss st ks k kt hh hρ _ G x y

/-- Actual recursive preparation wiring: cutoff after the full-rank raw H4 child walk,
then the source × usage preparation walk. Request size q is fixed across precisions.
Bias is charged to that completed raw child
minus G, with full-rank maximum and inverse rate explicit in preparationError. -/
theorem actualCompletedSecondSignal_mean_bias_le {q : ℕ} {E : Type*} [Fintype E] [Nonempty E]
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (hK : 0 < HP.K)
    (D : ZMod P) (R : RoleProfile J) (ks k kt : ℕ) (_husage : k ≤ kt)
    (ss st : List (ZMod P))
    (l bin km kb : ℕ) (sm : List (ZMod P)) (Kc : ℕ) (binCutoff : ℝ → ℝ)
    (raw prep : ℕ → HierarchyTask.Request q (Fin J) (ZMod P) →
      Environment P J → Matrix (ZMod P) (ZMod P) ℝ)
    (maximum : ℕ → HierarchyTask.Request q (Fin J) (ZMod P) →
      Environment P J → ZMod P → ℝ)
    (rawSteps : ℕ → ℕ)
    (graphs : ℕ → ∀ x y, RotationMap
      (RetainedPairSlice (retainedMask R.source (side P ks) D ss)
        (retainedMask R.terminal (side P kt) D st) x y) E)
    (times : ℕ → ZMod P → ZMod P → ℕ)
    {Lh Lρ : ℝ} (_hLρ : 0 ≤ Lρ)
    (hh : ∀ a b, |polynomialPrepCutoff4 HP.θ a - polynomialPrepCutoff4 HP.θ b| ≤ Lh * |a - b|)
    (hρ : ∀ a b, |HP.ρ a - HP.ρ b| ≤ Lρ * |a - b|)
    (ζ : ℝ) (G : Matrix (ZMod P) (ZMod P) ℝ) (i : ℕ) (x y : ZMod P) :
    let A := fun j σ x y => completedRawChild HP D R l bin ks km k kb ss sm st Kc
      binCutoff (raw j) (prep j) (maximum j) (rawSteps j) σ x y
    let T := fun j σ x y => selectedPreparation HP D R st k (A j) σ x y
    let H := fun j => conditionalWalk (retainedMask R.source (side P ks) D ss)
      (retainedMask R.terminal (side P kt) D st) (graphs j) (times j) (T j)
    actualClippedMean HP R.source R.terminal (side P ks) (side P k) (side P kt) D ss st k G ζ
      (firstSignalIncrement A k (secondSignalIncrement H ζ)) (fun _ _ _ _ => 0) 1 i x y ≤
      min 1 (|ζ| * rowSliceMean (retainedMask R.source (side P ks) D ss)
        (retainedMask R.terminal (side P kt) D st)
        (preparationError R D st k Lh Lρ (A (i + 1)) G) x y) := by
  dsimp only
  exact actualSelectedSecondSignal_mean_bias_le HP hK D R ks k kt _husage ss st _
    graphs times _ _hLρ hh hρ ζ G i x y

end
end Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
