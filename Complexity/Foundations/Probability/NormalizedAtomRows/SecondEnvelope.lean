/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate
public import Complexity.Foundations.Probability.NormalizedAtomRows.FirstMeanError
public import Complexity.Foundations.Probability.NormalizedAtomRows.FirstPayment
public import Complexity.Foundations.Probability.RootMetric.AbsoluteError

/-!
# Second deterministic envelopes from actual raw child errors

`secondMeanEnvelope` is the clipped usage-conditional mean of actual `preparationError`.
Full-terminal rank stability and conditional Jensen pay its fourth row moment by
`P * (|ζ| * (Lh + Lρ) / rate k)^4` times the completed RAW absolute error moment.
The width is explicit and is not a dimension-free recursive estimate. No independence
between errors and retention or upper bound on the target is assumed.

The raw error splits at the actual full-rank conditional input mean. Centered noise is
paid in matrix units, never by silently substituting relative `actualNoiseEntry`.
Deterministic mean error can be paid by the actual finite estimated-child cost of #2424.
Cutoff is applied only after the completed raw walk. Structural requests remain fixed;
correction stage km and parent rank k retain their distinct meanings.

These are original finite quantitative bridges adapting Samuel Schlesinger's row and
compression APIs. Small numerical recursive errors/reserves, copy routing, full estimator,
workspace and native RL=L remain open.
-/
public section
noncomputable section
namespace Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
open Finset Cslib Cslib.Probability Cslib.RowCompression
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {P J : ℕ} [Fact P.Prime]

/-- The actual second envelope B1, with source × usage conditioning and full-rank errors. -/
@[expose] def secondMeanEnvelope (R : RoleProfile J) (D : ZMod P)
    (ss st : List (ZMod P)) (ks k ku : ℕ) (Lh Lρ ζ : ℝ)
    (A : Environment P J → Matrix (ZMod P) (ZMod P) ℝ)
    (G : Matrix (ZMod P) (ZMod P) ℝ) (x y : ZMod P) : ℝ :=
  min 1 (|ζ| * rowSliceMean (retainedMask R.source (side P ks) D ss)
    (retainedMask R.terminal (side P ku) D st) (preparationError R D st k Lh Lρ A G) x y)

/-- Zero raw error pays zero, including empty rank or conditioning slices. -/
@[simp] lemma secondMeanEnvelope_self (R : RoleProfile J) (D : ZMod P)
    (ss st : List (ZMod P)) (ks k ku : ℕ) (Lh Lρ ζ : ℝ)
    (G : Matrix (ZMod P) (ZMod P) ℝ) (x y : ZMod P) :
    secondMeanEnvelope R D ss st ks k ku Lh Lρ ζ (fun _ => G) G x y = 0 := by
  simp [secondMeanEnvelope, rowSliceMean]

/-- Usage inclusion lets entry stability share the FULL terminal maximum with rank stability. -/
theorem preparationError_le_fullRank (R : RoleProfile J) (D : ZMod P)
    (st : List (ZMod P)) (k ku : ℕ) (husage : k ≤ ku)
    {Lh Lρ : ℝ} (hLh : 0 ≤ Lh) (hLρ : 0 ≤ Lρ)
    (A : Environment P J → Matrix (ZMod P) (ZMod P) ℝ)
    (G : Matrix (ZMod P) (ZMod P) ℝ) (σ : Environment P J) (x y : ZMod P)
    (hy : retainedMask R.terminal (side P ku) D st σ y) :
    preparationError R D st k Lh Lρ A G σ x y ≤
      ((Lh + Lρ) / rate k) * kthLargest 1
        {w | retainedMask R.terminal (side P k) D st σ w} (fun w => |A σ x w - G x w|) := by
  have hside : side P ku ≤ side P k := by
    rw [side_eq_ceil, side_eq_ceil]
    exact Nat.ceil_mono (mul_le_mul_of_nonneg_left
      (inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) husage)) (by positivity))
  have hyr : retainedMask R.terminal (side P k) D st σ y :=
    mem_retentionBox.mpr (fun a => (mem_retentionBox.mp hy a).trans_le hside)
  have hm (w : ZMod P) (hw : retainedMask R.terminal (side P k) D st σ w) :=
    abs_le_kthLargest_one {w | retainedMask R.terminal (side P k) D st σ w}
      (fun w => A σ x w - G x w) w (mem_filter.mpr ⟨mem_univ _, hw⟩)
  exact (preparationError_le R D st k hLh hLρ A G σ x y kthLargest_nonneg
    (hm y hyr) hm).trans_eq (by ring)

/-- Conditional Jensen and max⁴ ≤ full-rank sum give the explicit width-P payment. -/
theorem secondMeanEnvelope_moment (R : RoleProfile J) (D : ZMod P)
    (ss st : List (ZMod P)) (ks k ku : ℕ) (husage : k ≤ ku)
    {Lh Lρ : ℝ} (hLh : 0 ≤ Lh) (hLρ : 0 ≤ Lρ) (ζ : ℝ)
    (A : Environment P J → Matrix (ZMod P) (ZMod P) ℝ)
    (G : Matrix (ZMod P) (ZMod P) ℝ) {N u : ℝ} (hNu : 0 ≤ N * u) :
    rowNormPow 4 N u (retainedMask R.source (side P ks) D ss)
      (retainedMask R.terminal (side P ku) D st)
      (fun _ => secondMeanEnvelope R D ss st ks k ku Lh Lρ ζ A G) ≤
      P * (|ζ| * (Lh + Lρ) / rate k) ^ 4 *
        rowNormPow 4 N u (retainedMask R.source (side P ks) D ss)
          (retainedMask R.terminal (side P k) D st) (fun σ x y => A σ x y - G x y) := by
  have hb := rowNormPow_clipped_conditional_le_fullRank
    (X := retainedMask R.source (side P ks) D ss)
    (U := retainedMask R.terminal (side P ku) D st)
    (Y := retainedMask R.terminal (side P k) D st) hNu
    (fun σ x y => A σ x y - G x y) (preparationError R D st k Lh Lρ A G)
    (ζ := ζ) (div_nonneg (add_nonneg hLh hLρ) (rate_pos k).le)
    (fun σ x y => by
      unfold preparationError
      exact div_nonneg
        (add_nonneg (mul_nonneg hLh (abs_nonneg _)) (mul_nonneg hLρ kthLargest_nonneg))
        (rate_pos k).le)
    (fun σ x y _ hy => preparationError_le_fullRank R D st k ku husage hLh hLρ A G σ x y hy)
  unfold secondMeanEnvelope
  simpa only [ZMod.card, mul_div_assoc] using hb

/-- A centered RAW fourth moment and an ABSOLUTE deterministic mean-error moment pay B1.
Both hypotheses concern the actual raw child, never the desired final envelope. -/
theorem secondMeanEnvelope_moment_le (R : RoleProfile J) (D : ZMod P)
    (ss st : List (ZMod P)) (ks k ku : ℕ) (husage : k ≤ ku)
    {Lh Lρ : ℝ} (hLh : 0 ≤ Lh) (hLρ : 0 ≤ Lρ) (ζ : ℝ)
    (A : Environment P J → Matrix (ZMod P) (ZMod P) ℝ)
    (μ G : Matrix (ZMod P) (ZMod P) ℝ) {N u noise meanError : ℝ} (hNu : 0 ≤ N * u)
    (hnoise : rowNormPow 4 N u (retainedMask R.source (side P ks) D ss)
      (retainedMask R.terminal (side P k) D st) (fun σ x y => A σ x y - μ x y) ≤ noise)
    (hmean : rowNormPow 4 N u (retainedMask R.source (side P ks) D ss)
      (retainedMask R.terminal (side P k) D st) (fun _ x y => μ x y - G x y) ≤ meanError) :
    rowNormPow 4 N u (retainedMask R.source (side P ks) D ss)
      (retainedMask R.terminal (side P ku) D st)
      (fun _ => secondMeanEnvelope R D ss st ks k ku Lh Lρ ζ A G) ≤
      P * (|ζ| * (Lh + Lρ) / rate k) ^ 4 * (8 * (noise + meanError)) := by
  exact (secondMeanEnvelope_moment R D ss st ks k ku husage hLh hLρ ζ A G hNu).trans
    (mul_le_mul_of_nonneg_left ((rowNormPow_sub_le_centered hNu A μ G).trans
      (mul_le_mul_of_nonneg_left (add_le_add hnoise hmean) (by norm_num))) (by positivity))

/-- Actual full-rank H4 raw walking pays centered noise in matrix units and actual absolute
input mean error pays the deterministic part. No relative/clipped bound is inverted. -/
theorem secondMeanEnvelope_walk_moment (R : RoleProfile J) (D : ZMod P)
    (ss st : List (ZMod P)) (ks k ku steps : ℕ) (husage : k ≤ ku)
    {Lh Lρ : ℝ} (hLh : 0 ≤ Lh) (hLρ : 0 ≤ Lρ) (ζ : ℝ)
    (input : Environment P J → Matrix (ZMod P) (ZMod P) ℝ)
    (G : Matrix (ZMod P) (ZMod P) ℝ) (error : ZMod P → ZMod P → ℝ)
    (he : ∀ x y, |rowSliceMean (retainedMask R.source (side P ks) D ss)
      (retainedMask R.terminal (side P k) D st) input x y - G x y| ≤ error x y)
    {N u : ℝ} (hNu : 0 ≤ N * u) :
    let A := conditionalWalk (retainedMask R.source (side P ks) D ss)
      (retainedMask R.terminal (side P k) D st)
      (graph R.source R.terminal R.source_terminal (side P ks) (side P k)
        (side_le P ks) (side_le P k) (fun x => CopyPadding.identifier D ss x)
        (fun y => CopyPadding.identifier D st y)) (fun _ _ => steps) input
    rowNormPow 4 N u (retainedMask R.source (side P ks) D ss)
      (retainedMask R.terminal (side P ku) D st)
      (fun _ => secondMeanEnvelope R D ss st ks k ku Lh Lρ ζ A G) ≤
      P * (|ζ| * (Lh + Lρ) / rate k) ^ 4 * (8 *
        (32 * (1 - 1 / (155648 * (J + 1) * (4 : ℝ) ^ 4)) ^ (2 * steps) *
          rowNormPow 4 N u (retainedMask R.source (side P ks) D ss)
            (retainedMask R.terminal (side P k) D st) input +
        rowNormPow 4 N u (retainedMask R.source (side P ks) D ss)
          (retainedMask R.terminal (side P k) D st) (fun _ => error))) := by
  dsimp only
  apply secondMeanEnvelope_moment_le R D ss st ks k ku husage hLh hLρ ζ _
    (rowSliceMean (retainedMask R.source (side P ks) D ss)
      (retainedMask R.terminal (side P k) D st) input) G hNu
  · exact noise R.source R.terminal R.source_terminal (side P ks) (side P k)
      (side_le P ks) (side_le P k) (fun x => CopyPadding.identifier D ss x)
      (fun y => CopyPadding.identifier D st y) hNu steps input
  · apply (rowNormPow_le_mul hNu (c := 1) ?_).trans_eq (one_mul _)
    intro σ x y _ _
    rw [one_mul, abs_of_nonneg ((abs_nonneg _).trans (he x y))]
    exact pow_le_pow_left₀ (abs_nonneg _) (he x y) 4

/-- The actual clipped second discrepancy is bounded by the constructed B1. -/
theorem actualSelectedSecondSignal_mean_le_envelope {E : Type*} [Fintype E] [Nonempty E]
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (hK : 0 < HP.K)
    (D : ZMod P) (R : RoleProfile J) (ks k kt : ℕ) (_husage : k ≤ kt)
    (ss st : List (ZMod P))
    (A : ℕ → Environment P J → Matrix (ZMod P) (ZMod P) ℝ)
    (graphs : ℕ → ∀ x y, RotationMap
      (RetainedPairSlice (retainedMask R.source (side P ks) D ss)
        (retainedMask R.terminal (side P kt) D st) x y) E)
    (times : ℕ → ZMod P → ZMod P → ℕ)
    (F : ℕ → Environment P J → ZMod P → ZMod P → ℝ)
    {Lh Lρ : ℝ} (hLρ : 0 ≤ Lρ)
    (hh : ∀ a b, |polynomialPrepCutoff4 HP.θ a - polynomialPrepCutoff4 HP.θ b| ≤ Lh * |a - b|)
    (hρ : ∀ a b, |HP.ρ a - HP.ρ b| ≤ Lρ * |a - b|)
    (ζ : ℝ) (G : Matrix (ZMod P) (ZMod P) ℝ) (i : ℕ) (x y : ZMod P) :
    let T := fun j σ x y => selectedPreparation HP D R st k (A j) σ x y
    let H := fun j => conditionalWalk (retainedMask R.source (side P ks) D ss)
      (retainedMask R.terminal (side P kt) D st) (graphs j) (times j) (T j)
    actualClippedMean HP R.source R.terminal (side P ks) (side P k) (side P kt) D ss st k G ζ
      (firstSignalIncrement F k (secondSignalIncrement H ζ)) (fun _ _ _ _ => 0) 1 i x y ≤
      secondMeanEnvelope R D ss st ks k kt Lh Lρ ζ (A (i + 1)) G x y := by
  exact actualSelectedSecondSignal_mean_bias_le HP hK D R ks k kt _husage ss st A graphs
    times F hLρ hh hρ ζ G i x y

set_option backward.isDefEq.respectTransparency false in
/-- Actual finite child-error costs pay the second deterministic envelope after the RAW
walk. Positive-bin costs sum and the special negative cost is charged once. The canonical
residual is built at km; normalization and full rank stay at kt. No desired B is assumed. -/
theorem actualEstimatedResidual_second_envelope_moment
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
    (hcover : ∀ z y, C z y = 0 ∨ rate (kb n) ≤ C z y)
    (steps : ℕ → ℕ) (ku : ℕ) (husage : kt ≤ ku)
    {Lh Lρ : ℝ} (hLh : 0 ≤ Lh) (hLρ : 0 ≤ Lρ) (ζ : ℝ) (j : ℕ) :
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
    let input := estimatedResidualInput HP D id R l ks km kt n ss sm st kb Kc bounded
      raw prep maximum
    let G := HP.toHierarchyParams.residual (canonicalChannel id (rate km))
      (canonicalChannel id (rate km)) (rate km) C
    let F := fun j => conditionalWalk (retainedMask R.source (side P ks) D ss)
      (retainedMask R.terminal (side P kt) D st)
      (graph R.source R.terminal R.source_terminal (side P ks) (side P kt)
        (side_le P ks) (side_le P kt) (fun x => CopyPadding.identifier D ss x)
        (fun y => CopyPadding.identifier D st y)) (fun _ _ => steps j) (input j)
    let cost := fun x y => HierarchyTask.conditionalChildCost channelsV (range (n + 1)) l
      source mid terminal (fun i => rate (kb i))
      (2 * HP.Q HP.toHierarchyParams.atomCap) (2 * max cap 16)
      (estimated (j + 1)) canonical x y
    rowNormPow 4 P (rate ks) (retainedMask R.source (side P ks) D ss)
      (retainedMask R.terminal (side P ku) D st)
      (fun _ => secondMeanEnvelope R D ss st ks kt ku Lh Lρ ζ (F (j + 1)) G) ≤
      P * (|ζ| * (Lh + Lρ) / rate kt) ^ 4 * (8 *
        (32 * (1 - 1 / (155648 * (J + 1) * (4 : ℝ) ^ 4)) ^ (2 * steps (j + 1)) *
          (16 * P * (estimatedResidualBound HP P km kt n kb (estimatedBinCap cap)) ^ 4) +
          rowNormPow 4 P (rate ks) (retainedMask R.source (side P ks) D ss)
            (retainedMask R.terminal (side P kt) D st) (fun _ => cost))) := by
  have hHPK : 0 < HP.K := by
    have hg := HP.gate
    have hn : 0 ≤ 32 * (HP.k : ℝ) / HP.η :=
      div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) HP.η_pos.le
    have hk : (0 : ℝ) < HP.K := by linarith
    exact_mod_cast hk
  extract_lets cutoff bounded source mid terminal estimated canonical channelsV input G F cost
  refine le_trans (secondMeanEnvelope_walk_moment R D ss st ks kt ku (steps (j + 1))
    husage hLh hLρ ζ (input (j + 1)) G cost ?_ (mul_nonneg (Nat.cast_nonneg P) (rate_pos ks).le)) ?_
  · intro x y
    have he := estimated_residual_bins_mean_error HP D id hD Function.injective_id
      H R l ks km kt n ksH hms ss sm st kb hbH C hC hC1 hCf χ hχ h ρ K hkh
      hρ0 hρ1 hη hρη hK hχmono hχ0 hχrange hanti hratio hcap hCcap Kc
      (raw (j + 1)) (prep (j + 1)) (maximum (j + 1)) x y (fun z => hcover z y)
    dsimp only at he
    convert he using 1 <;>
      simp only [input, G, cost, HierarchyTask.conditionalChildCost, channelsV, estimated,
        canonical, cutoff, bounded, source, mid,
        terminal, estimatedResidualInput, rowSliceMean, CorrectionRowTask.Channel.retains,
        channels, gridChannel, semanticSide_grid, retainedMask, id_eq]
    congr!
  · have hp := estimatedResidualInput_moment_le HP hHPK D R H l ks km kt n ksH
      ss sm st kb Kc
      (fun i => boundedRoutedBinCutoff χ (fun i => rate (kb i)) cap i (fun _ => 1))
      (estimatedBinCap cap) (fun i => by unfold estimatedBinCap; split_ifs <;> positivity)
      (boundedRoutedBinCutoff_grid_range χ kb hcap hχmono hχ0 hχ hχrange hanti hratio)
      raw prep maximum (j + 1)
    gcongr
    rw [pow_mul]
    positivity

/-- Actual range-based FirstPayment pays the centered RAW child in matrix units. Combined
with an absolute input mean-error bound this yields B1; no relative noise is substituted. -/
theorem actualCompletedRaw_absolute_moment_le_payment {q : ℕ}
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (hK : 0 < HP.K)
    (D : ZMod P) (R : RoleProfile J) (H : Horizon P)
    (l bin ks km k kb : ℕ)
    (hks : ks ≤ H.maxExponent) (hkm : km ≤ H.maxExponent)
    (ss sm st : List (ZMod P)) (Kc : ℕ) (hKc : 0 < Kc) (binCutoff : ℝ → ℝ)
    {CB : ℝ} (hCB : 0 ≤ CB) (hbin : ∀ d, binCutoff d ∈ Set.Icc 0 CB)
    (raw prep : HierarchyTask.Request (q + 1) (Fin J) (ZMod P) →
      Environment P J → Matrix (ZMod P) (ZMod P) ℝ)
    (maximum : HierarchyTask.Request (q + 1) (Fin J) (ZMod P) →
      Environment P J → ZMod P → ℝ)
    (steps : ℕ)
    (G : Matrix (ZMod P) (ZMod P) ℝ) (error : ZMod P → ZMod P → ℝ)
    (he : ∀ x y, |rowSliceMean (retainedMask R.source (side P ks) D ss)
      (retainedMask R.terminal (side P k) D st)
      (rawIncomingNormalized HP D id R l bin ks km k kb ss sm st
        (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff Kc binCutoff raw prep maximum)
        x y - G x y| ≤ error x y) :
    let A := completedRawChild HP D R l bin ks km k kb ss sm st Kc binCutoff
      raw prep maximum steps
    rowNormPow 4 P (rate ks) (retainedMask R.source (side P ks) D ss)
      (retainedMask R.terminal (side P k) D st) (fun σ x y => A σ x y - G x y) ≤
      8 *
        (32 * (1 - 1 / (155648 * (J + 1) * (4 : ℝ) ^ 4)) ^ (2 * steps) *
          firstSignalPayment HP P Kc ks km k kb CB +
          rowNormPow 4 P (rate ks) (retainedMask R.source (side P ks) D ss)
            (retainedMask R.terminal (side P k) D st) (fun _ => error)) := by
  dsimp only
  have hP : (0 : ℝ) < P := by exact_mod_cast (Fact.out : P.Prime).pos
  have hNu := (mul_pos hP (rate_pos ks)).le
  apply (rowNormPow_sub_le_centered hNu _
    (rowSliceMean (retainedMask R.source (side P ks) D ss)
      (retainedMask R.terminal (side P k) D st)
      (rawIncomingNormalized HP D id R l bin ks km k kb ss sm st
        (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff Kc binCutoff raw prep maximum)) G).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 8)
  apply add_le_add
  · have hn := rawIncomingNormalized_noise_le_lower HP hK D (id : ZMod P → ZMod P) R
      l bin ks km k kb ss sm st Kc hKc binCutoff raw prep maximum hP (rate_pos ks) steps
    have hp := incomingMomentBudget_le_payment HP D R H l bin ks km k kb hks hkm
      ss sm st Kc binCutoff hCB hbin raw prep maximum
    exact hn.trans (mul_le_mul_of_nonneg_left hp (by rw [pow_mul]; positivity))
  · apply (rowNormPow_le_mul hNu (c := 1) ?_).trans_eq (one_mul _)
    intro σ x y _ _
    rw [one_mul, abs_of_nonneg ((abs_nonneg _).trans (he x y))]
    exact pow_le_pow_left₀ (abs_nonneg _) (he x y) 4


/-- The raw absolute payment yields the actual second deterministic envelope. -/
theorem actualCompletedSecondSignal_envelope_payment {q : ℕ}
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (hK : 0 < HP.K)
    (D : ZMod P) (R : RoleProfile J) (H : Horizon P)
    (l bin ks km k kb ku : ℕ) (husage : k ≤ ku)
    (hks : ks ≤ H.maxExponent) (hkm : km ≤ H.maxExponent)
    (ss sm st : List (ZMod P)) (Kc : ℕ) (hKc : 0 < Kc) (binCutoff : ℝ → ℝ)
    {CB : ℝ} (hCB : 0 ≤ CB) (hbin : ∀ d, binCutoff d ∈ Set.Icc 0 CB)
    (raw prep : HierarchyTask.Request (q + 1) (Fin J) (ZMod P) →
      Environment P J → Matrix (ZMod P) (ZMod P) ℝ)
    (maximum : HierarchyTask.Request (q + 1) (Fin J) (ZMod P) →
      Environment P J → ZMod P → ℝ)
    (steps : ℕ) {Lh Lρ : ℝ} (hLh : 0 ≤ Lh) (hLρ : 0 ≤ Lρ) (ζ : ℝ)
    (G : Matrix (ZMod P) (ZMod P) ℝ) (error : ZMod P → ZMod P → ℝ)
    (he : ∀ x y, |rowSliceMean (retainedMask R.source (side P ks) D ss)
      (retainedMask R.terminal (side P k) D st)
      (rawIncomingNormalized HP D id R l bin ks km k kb ss sm st
        (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff Kc binCutoff raw prep maximum)
        x y - G x y| ≤ error x y) :
    let A := completedRawChild HP D R l bin ks km k kb ss sm st Kc binCutoff
      raw prep maximum steps
    rowNormPow 4 P (rate ks) (retainedMask R.source (side P ks) D ss)
      (retainedMask R.terminal (side P ku) D st)
      (fun _ => secondMeanEnvelope R D ss st ks k ku Lh Lρ ζ A G) ≤
      P * (|ζ| * (Lh + Lρ) / rate k) ^ 4 * (8 *
        (32 * (1 - 1 / (155648 * (J + 1) * (4 : ℝ) ^ 4)) ^ (2 * steps) *
          firstSignalPayment HP P Kc ks km k kb CB +
          rowNormPow 4 P (rate ks) (retainedMask R.source (side P ks) D ss)
            (retainedMask R.terminal (side P k) D st) (fun _ => error))) := by
  dsimp only
  exact (secondMeanEnvelope_moment R D ss st ks k ku husage hLh hLρ ζ _ G
    (mul_nonneg (Nat.cast_nonneg P) (rate_pos ks).le)).trans
    (mul_le_mul_of_nonneg_left
      (actualCompletedRaw_absolute_moment_le_payment HP hK D R H l bin ks km k kb
        hks hkm ss sm st Kc hKc binCutoff hCB hbin raw prep maximum steps G error he)
      (by positivity))

/-- Completed-child wiring satisfies the actual B1 deterministic envelope. -/
theorem actualCompletedSecondSignal_mean_le_envelope {q : ℕ} {E : Type*} [Fintype E] [Nonempty E]
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
    {Lh Lρ : ℝ} (hLρ : 0 ≤ Lρ)
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
      secondMeanEnvelope R D ss st ks k kt Lh Lρ ζ (A (i + 1)) G x y := by
  exact actualCompletedSecondSignal_mean_bias_le HP hK D R ks k kt _husage ss st
    l bin km kb sm Kc binCutoff raw prep maximum rawSteps graphs times hLρ hh hρ ζ G i x y

end Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
