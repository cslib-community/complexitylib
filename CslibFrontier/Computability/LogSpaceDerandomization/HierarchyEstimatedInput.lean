/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate
public import CslibFrontier.Computability.LogSpaceDerandomization.HierarchyChildError
public import CslibFrontier.Computability.LogSpaceDerandomization.GridRowMoment
public import CslibFrontier.Foundations.Probability.SpectralPayment

/-!
# Actual finite estimated residual input

The input sums real positive bins and subtracts one negative correction. Structural
requests remain at HP.k; precision indexes only the earlier estimates. Bounds use the
actual selected correction support, dense cutoff ranges, and rounded frame marginals.
No independence or final input-moment premise is assumed. This original finite payment
does not establish recursive reserves or copy routing. Range arguments adapt Samuel
Schlesinger’s normalized-row APIs.
-/
public section
noncomputable section
open Finset Cslib Cslib.Probability
open scoped BigOperators
namespace Matrix.HierarchyParams.H4RankEnvironment
attribute [local instance] Classical.propDecidable
variable {P J : ℕ} [Fact P.Prime]
/-- Arbitrary bin cutoffs need an explicit bound. The clipped denominator doubles it. -/
theorem normalizedRequest_mem_Icc {q : ℕ}
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (D : ZMod P)
    (r : HierarchyTask.Request q (Fin J) (ZMod P)) (binCutoff : ℝ → ℝ)
    {CB : ℝ} (hCB : 0 ≤ CB) (hbin : ∀ d, binCutoff d ∈ Set.Icc 0 CB)
    (raw prep : Environment P J → Matrix (ZMod P) (ZMod P) ℝ)
    (σ : Environment P J) (x y : ZMod P) :
    normalizedRequest D id r binCutoff HP.ρ HP.K raw prep σ x y ∈ Set.Icc 0 (2 * CB) := by
  unfold normalizedRequest
  split_ifs
  · exact DenseRowRecipe.normalized_mem_Icc _ _ _ _ _ _ _ hCB hbin
      (fun d => ⟨HP.ρ_nonneg d, HP.ρ_le_one d⟩) _ _ _ _ _
  · exact ⟨le_rfl, by positivity⟩


/-- Top-bin cap and fine-bin adjacent ratio are kept separate in the finite scale sum. -/
@[expose] def estimatedBinCap (cap : ℝ) (i : ℕ) : ℝ := if i = 0 then cap else 16

/-- Actual bounded routed cutoffs satisfy the top cap or the adjacent-16 cap, independently
of the sizes of arbitrary earlier estimates. -/
theorem boundedRoutedBinCutoff_grid_range
    (χ : ℝ → ℝ) (kb : ℕ → ℕ) {cap : ℝ} (hcap : 0 ≤ cap)
    (hχ : Monotone χ) (hχ0 : ∀ v, v ≤ 1 / 2 → χ v = 0)
    (hχ1 : ∀ v, 1 ≤ v → χ v = 1) (hχrange : ∀ v, χ v ∈ Set.Icc 0 1)
    (hanti : Antitone (fun i => rate (kb i)))
    (hratio : ∀ i, rate (kb i) / rate (kb (i + 1)) ≤ 16) (i : ℕ) (d : ℝ) :
    boundedRoutedBinCutoff χ (fun i => rate (kb i)) cap i (fun _ => 1) d ∈
      Set.Icc 0 (estimatedBinCap cap i) := by
  cases i with
  | zero =>
    let v := min cap (max 0 d)
    have hv : 0 ≤ v := le_min hcap (le_max_left _ _)
    have hvc : v ≤ cap := min_le_left _ _
    have hc := hχrange v
    have he : boundedRoutedBinCutoff χ (fun i => rate (kb i)) cap 0 (fun _ => 1) d =
        v * χ v := by
      simp only [boundedRoutedBinCutoff, routedBinCutoff, Cslib.binWeight,
        ↓reduceIte, mul_one, mul_div_cancel_left₀ _ (rate_pos (kb 0)).ne']
      rfl
    rw [he]
    exact ⟨mul_nonneg hv hc.1, (mul_le_of_le_one_right hv hc.2).trans hvc⟩
  | succ i =>
    have hb := boundedRoutedBinCutoff_mem_Icc (cap := 0) (B := 16)
      (by norm_num) (by norm_num) (by norm_num) hχ hχ0 hχ1 hχrange
      (fun j => rate_pos (kb j)) hanti hratio
      (fun _ => 1) (fun _ => ⟨zero_le_one, le_rfl⟩) (i + 1) d
    simpa only [estimatedBinCap, boundedRoutedBinCutoff, Nat.succ_ne_zero,
      ↓reduceIte] using hb

/-- Actual once-negative finite residual, with independent statistical precision. -/
@[expose] def estimatedResidualInput
    {V : Type} [Fintype V]
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (D : ZMod P) (ident : V → ZMod P)
    (R : RoleProfile J)
    (l ks km kt n : ℕ) (ss sm st : List (ZMod P)) (kb : ℕ → ℕ)
    (Kc : ℕ) (cutoff : ℕ → ℝ → ℝ)
    (raw prep : ℕ → ℕ → HierarchyTask.Request HP.k (Fin J) (ZMod P) →
      Environment P J → Matrix V V ℝ)
    (maximum : ℕ → ℕ → HierarchyTask.Request HP.k (Fin J) (ZMod P) →
      Environment P J → V → ℝ)
    (precision : ℕ) (σ : Environment P J) (x y : V) : ℝ :=
  (∑ i ∈ range (n + 1), HierarchyTask.rawPositiveSample
    (fun role b suffix σ v => channels D role b suffix σ (ident v))
    l i .residual (gridChannel R.source ks ss) (gridChannel R.midpoint km sm)
    (gridChannel R.terminal kt st) (rate (kb i))
    (fun r => incomingChildren HP D ident Kc (cutoff i)
      (raw precision i) (prep precision i) (maximum precision i) r σ) x y) -
  HierarchyTask.rawNegativeSample
    (fun role b suffix σ v => channels D role b suffix σ (ident v)) l 0 .residual
    (gridChannel R.source ks ss) (gridChannel R.midpoint km sm)
    (gridChannel R.terminal kt st) (rate (kb 0))
    (fun r => incomingChildren HP D ident Kc (cutoff 0)
      (raw precision 0) (prep precision 0) (maximum precision 0) r σ) x y

/-- Finite scale sum with literal importance ratios and midpoint density. The product
uses row support K rather than ambient width P. -/
@[expose] def estimatedResidualBound
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (P km kt n : ℕ)
    (kb : ℕ → ℕ) (CB : ℕ → ℝ) : ℝ :=
  let CA := 2 * HP.Q HP.toHierarchyParams.atomCap
  (∑ i ∈ range (n + 1), rate (kb i) *
    (gridMass P kt / gridMass P (max kt (kb i))) * (2 * CB i) *
    (1 + HP.K * CA * rate km / gridMass P km)) +
    rate km * (gridMass P kt / gridMass P (max kt km)) * CA

/-- Actual positive-bin range. The left support is at most K and vanishes off
its midpoint usage channel, so the product pays K, not P. -/
theorem estimatedPositiveSample_abs_le
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (hK : 0 < HP.K)
    (D : ZMod P) (R : RoleProfile J) (l bin ks km kt kb : ℕ)
    (ss sm st : List (ZMod P)) (Kc : ℕ) (cutoff : ℝ → ℝ)
    {CB : ℝ} (hCB : 0 ≤ CB) (hcut : ∀ v, cutoff v ∈ Set.Icc 0 CB)
    (raw prep : HierarchyTask.Request HP.k (Fin J) (ZMod P) →
      Environment P J → Matrix (ZMod P) (ZMod P) ℝ)
    (maximum : HierarchyTask.Request HP.k (Fin J) (ZMod P) →
      Environment P J → ZMod P → ℝ)
    (σ : Environment P J) (x y : ZMod P) :
    |HierarchyTask.rawPositiveSample (channels D) l bin .residual
      (gridChannel R.source ks ss) (gridChannel R.midpoint km sm)
      (gridChannel R.terminal kt st) (rate kb)
      (fun r => incomingChildren HP D id Kc cutoff raw prep maximum r σ) x y| ≤
    rate kb * (gridMass P kt / gridMass P (max kt kb)) * (2 * CB) *
      (1 + HP.K * (2 * HP.Q HP.toHierarchyParams.atomCap) * rate km / gridMass P km) := by
  let source := gridChannel R.source ks ss
  let mid := gridChannel R.midpoint km sm
  let terminal := gridChannel R.terminal kt st
  let req := HierarchyTask.rawRequests (k := HP.k) l bin .residual source mid terminal (rate kb)
  let child := incomingChildren HP D id Kc cutoff raw prep maximum
  let CA := 2 * HP.Q HP.toHierarchyParams.atomCap
  have hCA : 0 ≤ CA := mul_nonneg (by norm_num) (HP.Q_nonneg _)
  have hleft : ∀ a b, child req.left σ a b = correctionRequest D id req.left
      (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ HP.toHierarchyParams.atomCutoff
      HP.γ HP.K Kc (raw req.left) (prep req.left) (maximum req.left) σ a b := by
    intro a b
    simp only [child, incomingChildren, req, HierarchyTask.rawRequests,
      HierarchyTask.correctionAtomTask_last HP.k_pos]
  have hl (z : ZMod P) : |child req.left σ x z| ≤ CA := by
    rw [hleft]
    have hb := selectedRequest_mem_Icc HP D id req.left Kc (raw req.left) (prep req.left)
      (maximum req.left) σ x z
    exact (abs_of_nonneg hb.1).trans_le hb.2
  have hr (z : ZMod P) : |child req.right σ z y| ≤ 2 * CB := by
    have hb := normalizedRequest_mem_Icc HP D req.right cutoff hCB hcut
      (raw req.right) (prep req.right) σ z y
    exact (abs_of_nonneg hb.1).trans_le hb.2
  have hd : |child req.direct σ x y| ≤ 2 * CB := by
    have hb := normalizedRequest_mem_Icc HP D req.direct cutoff hCB hcut
      (raw req.direct) (prep req.direct) σ x y
    exact (abs_of_nonneg hb.1).trans_le hb.2
  let T : Finset (ZMod P) := {z ∈ {z | mid.retains (channels D) σ z} |
    child req.left σ x z ≠ 0}
  have hT : T.card ≤ HP.K := by
    simp only [T, hleft]
    exact selectedRequest_row_support HP hK D id req.left Kc _ _ _ σ x
  have hz (z : ZMod P) (hz : z ∉ T) : child req.left σ x z = 0 := by
    by_cases hm : mid.retains (channels D) σ z
    · by_contra hn
      exact hz (mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, hm⟩, hn⟩)
    · rw [hleft]
      exact correctionRequest_eq_zero_of_not_usage D id req.left _ _ _ _ _ _ _ _ _ _
        σ x z hm
  have hp : |∑ z, child req.left σ x z * child req.right σ z y| ≤ HP.K * CA * (2 * CB) := by
    have heq : (∑ z, child req.left σ x z * child req.right σ z y) =
        ∑ z ∈ T, child req.left σ x z * child req.right σ z y := by
      symm
      apply sum_subset (subset_univ T)
      intro z _ hz'
      rw [hz z hz', zero_mul]
    rw [heq]
    calc
      _ ≤ ∑ z ∈ T, |child req.left σ x z * child req.right σ z y| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _z ∈ T, CA * (2 * CB) := sum_le_sum fun z _ => by
        rw [abs_mul]
        exact mul_le_mul (hl z) (hr z) (abs_nonneg _) hCA
      _ = T.card * (CA * (2 * CB)) := by simp
      _ ≤ HP.K * (CA * (2 * CB)) := mul_le_mul_of_nonneg_right
        (by exact_mod_cast hT) (by positivity)
      _ = _ := by ring
  have ratioD : HierarchyTask.usageRatio (channels D) terminal req.direct y =
      gridMass P kt / gridMass P (max kt kb) :=
    usageRatio_grid D terminal req.direct kt (max kt kb) rfl (rate_min kt kb) y
  have ratioR : HierarchyTask.usageRatio (channels D) terminal req.right y =
      gridMass P kt / gridMass P (max kt kb) :=
    usageRatio_grid D terminal req.right kt (max kt kb) rfl (rate_min kt kb) y
  have dm : (dens {τ : Environment P J | mid.retains (channels D) τ y} : ℝ) =
      gridMass P km := channel_density D mid km rfl y
  change |rate kb * HierarchyTask.usageRatio (channels D) terminal req.direct y *
    child req.direct σ x y + rate kb * HierarchyTask.usageRatio (channels D) terminal
    req.right y * (rate km / (dens {τ | mid.retains (channels D) τ y} : ℝ)) *
      ∑ z, child req.left σ x z * child req.right σ z y| ≤ _
  rw [ratioD, ratioR, dm]
  have hc : 0 ≤ rate kb * (gridMass P kt / gridMass P (max kt kb)) := by
    unfold gridMass rate; positivity
  have hm : 0 ≤ rate km / gridMass P km := by unfold gridMass rate; positivity
  calc
    _ ≤ _ := abs_add_le _ _
    _ = rate kb * (gridMass P kt / gridMass P (max kt kb)) * |child req.direct σ x y| +
        (rate kb * (gridMass P kt / gridMass P (max kt kb)) * (rate km / gridMass P km)) *
          |∑ z, child req.left σ x z * child req.right σ z y| := by
      rw [abs_mul (rate kb * _) _, abs_mul (rate kb * _ * _) _,
        abs_of_nonneg hc, abs_of_nonneg (mul_nonneg hc hm)]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hd hc)
      (mul_le_mul_of_nonneg_left hp (mul_nonneg hc hm))
    _ = _ := by dsimp [CA]; ring

/-- Pointwise finite input bound for arbitrary earlier estimates. Width occurs only
in the rounded marginals; the midpoint product uses actual row support. -/
theorem estimatedResidualInput_abs_le
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (hK : 0 < HP.K)
    (D : ZMod P) (R : RoleProfile J) (l ks km kt n : ℕ)
    (ss sm st : List (ZMod P)) (kb : ℕ → ℕ) (Kc : ℕ) (cutoff : ℕ → ℝ → ℝ)
    (CB : ℕ → ℝ) (hCB : ∀ i, 0 ≤ CB i)
    (hcut : ∀ i v, cutoff i v ∈ Set.Icc 0 (CB i))
    (raw prep : ℕ → ℕ → HierarchyTask.Request HP.k (Fin J) (ZMod P) →
      Environment P J → Matrix (ZMod P) (ZMod P) ℝ)
    (maximum : ℕ → ℕ → HierarchyTask.Request HP.k (Fin J) (ZMod P) →
      Environment P J → ZMod P → ℝ)
    (precision : ℕ) (σ : Environment P J) (x y : ZMod P) :
    |estimatedResidualInput HP D id R l ks km kt n ss sm st kb Kc cutoff
      raw prep maximum precision σ x y| ≤ estimatedResidualBound HP P km kt n kb CB := by
  let source := gridChannel R.source ks ss
  let mid := gridChannel R.midpoint km sm
  let terminal := gridChannel R.terminal kt st
  let neg : HierarchyTask.Request HP.k (Fin J) (ZMod P) :=
    ⟨HierarchyTask.correctionAtomTask l false (Fin.last HP.k), source,
      {terminal with rate := rate km}, {terminal with rate := min terminal.rate (rate km)}⟩
  have ratio : HierarchyTask.usageRatio (channels D) terminal neg y =
      gridMass P kt / gridMass P (max kt km) :=
    usageRatio_grid D terminal neg kt (max kt km) rfl (rate_min kt km) y
  have hn : |HierarchyTask.rawNegativeSample (channels D) l 0 .residual source mid
      terminal (rate (kb 0)) (fun r => incomingChildren HP D id Kc (cutoff 0)
        (raw precision 0) (prep precision 0) (maximum precision 0) r σ) x y| ≤
      rate km * (gridMass P kt / gridMass P (max kt km)) *
        (2 * HP.Q HP.toHierarchyParams.atomCap) := by
    change |rate km * HierarchyTask.usageRatio (channels D) terminal neg y *
      incomingChildren HP D id Kc (cutoff 0) (raw precision 0) (prep precision 0)
        (maximum precision 0) neg σ x y| ≤ _
    rw [ratio, abs_mul, abs_of_nonneg (by unfold gridMass rate; positivity)]
    exact mul_le_mul_of_nonneg_left
      (incomingChildren_final_range HP D id Kc _ _ _ _ neg l rfl σ x y)
      (by unfold gridMass rate; positivity)
  unfold estimatedResidualInput estimatedResidualBound
  apply (abs_sub _ _).trans
  apply add_le_add _ hn
  exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ =>
    estimatedPositiveSample_abs_le HP hK D R l i ks km kt (kb i) ss sm st Kc
      (cutoff i) (hCB i) (hcut i) (raw precision i) (prep precision i)
      (maximum precision i) σ x y)

/-- Nonnegative finite payment; zero cutoffs and empty slices need no exceptional rule. -/
theorem estimatedResidualBound_nonneg
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (P km kt n : ℕ)
    (kb : ℕ → ℕ) (CB : ℕ → ℝ) (hCB : ∀ i, 0 ≤ CB i) :
    0 ≤ estimatedResidualBound HP P km kt n kb CB := by
  unfold estimatedResidualBound
  dsimp only
  have hQ := HP.Q_nonneg HP.toHierarchyParams.atomCap
  have hmass (k : ℕ) : 0 ≤ gridMass P k := by unfold gridMass; positivity
  have hr (k : ℕ) := (rate_pos k).le
  apply add_nonneg
  · exact sum_nonneg fun i _ => mul_nonneg
      (mul_nonneg (mul_nonneg (hr _) (div_nonneg (hmass _) (hmass _)))
        (mul_nonneg (by norm_num) (hCB i)))
      (add_nonneg zero_le_one (div_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg HP.K)
        (mul_nonneg (by norm_num) hQ)) (hr _)) (hmass _)))
  · exact mul_nonneg (mul_nonneg (hr _) (div_nonneg (hmass _) (hmass _)))
      (mul_nonneg (by norm_num) hQ)

/-- Fourth moment of the shared actual finite input, paid before walking. -/
theorem estimatedResidualInput_moment_le
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (hK : 0 < HP.K)
    (D : ZMod P) (R : RoleProfile J) (H : Horizon P)
    (l ks km kt n : ℕ) (hks : ks ≤ H.maxExponent)
    (ss sm st : List (ZMod P)) (kb : ℕ → ℕ) (Kc : ℕ) (cutoff : ℕ → ℝ → ℝ)
    (CB : ℕ → ℝ) (hCB : ∀ i, 0 ≤ CB i)
    (hcut : ∀ i v, cutoff i v ∈ Set.Icc 0 (CB i))
    (raw prep : ℕ → ℕ → HierarchyTask.Request HP.k (Fin J) (ZMod P) →
      Environment P J → Matrix (ZMod P) (ZMod P) ℝ)
    (maximum : ℕ → ℕ → HierarchyTask.Request HP.k (Fin J) (ZMod P) →
      Environment P J → ZMod P → ℝ) (precision : ℕ) :
    rowNormPow 4 P (rate ks) (NormalizedMoments.retainedMask R.source (side P ks) D ss)
      (NormalizedMoments.retainedMask R.terminal (side P kt) D st)
      (estimatedResidualInput HP D id R l ks km kt n ss sm st kb Kc cutoff
        raw prep maximum precision) ≤
      16 * P * (estimatedResidualBound HP P km kt n kb CB) ^ 4 := by
  exact grid_row_moment_le D R.source ks ss H hks _ _
    (estimatedResidualBound_nonneg HP P km kt n kb CB hCB)
    (estimatedResidualInput_abs_le HP hK D R l ks km kt n ss sm st kb Kc cutoff
      CB hCB hcut raw prep maximum precision)


/-- Centered RAW noise of the actual finite input, paid by its actual output ranges. -/
theorem estimatedResidualInput_noise_le
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (hK : 0 < HP.K)
    (D : ZMod P) (R : RoleProfile J) (H : Horizon P)
    (l ks km kt n : ℕ) (hks : ks ≤ H.maxExponent)
    (ss sm st : List (ZMod P)) (kb : ℕ → ℕ) (Kc : ℕ) (cutoff : ℕ → ℝ → ℝ)
    (CB : ℕ → ℝ) (hCB : ∀ i, 0 ≤ CB i)
    (hcut : ∀ i v, cutoff i v ∈ Set.Icc 0 (CB i))
    (raw prep : ℕ → ℕ → HierarchyTask.Request HP.k (Fin J) (ZMod P) →
      Environment P J → Matrix (ZMod P) (ZMod P) ℝ)
    (maximum : ℕ → ℕ → HierarchyTask.Request HP.k (Fin J) (ZMod P) →
      Environment P J → ZMod P → ℝ) (precision steps : ℕ) :
    let input := estimatedResidualInput HP D id R l ks km kt n ss sm st kb Kc cutoff
      raw prep maximum precision
    let F := conditionalWalk (NormalizedMoments.retainedMask R.source (side P ks) D ss)
        (NormalizedMoments.retainedMask R.terminal (side P kt) D st)
        (graph R.source R.terminal R.source_terminal (side P ks) (side P kt)
          (side_le P ks) (side_le P kt) (fun x => CopyPadding.identifier D ss x)
          (fun y => CopyPadding.identifier D st y)) (fun _ _ => steps)
        (estimatedResidualInput HP D id R l ks km kt n ss sm st kb Kc cutoff
          raw prep maximum precision)
    rowNormPow 4 P (rate ks) (NormalizedMoments.retainedMask R.source (side P ks) D ss)
      (NormalizedMoments.retainedMask R.terminal (side P kt) D st)
      (fun σ x y => F σ x y - rowSliceMean
        (NormalizedMoments.retainedMask R.source (side P ks) D ss)
        (NormalizedMoments.retainedMask R.terminal (side P kt) D st) input x y) ≤
      32 * (1 - 1 / (155648 * (J + 1) * (4 : ℝ) ^ 4)) ^ (2 * steps) *
        (16 * P * (estimatedResidualBound HP P km kt n kb CB) ^ 4) := by
  dsimp only
  have hn := noise R.source R.terminal R.source_terminal
    (side P ks) (side P kt) (side_le P ks) (side_le P kt)
    (fun x => CopyPadding.identifier D ss x) (fun y => CopyPadding.identifier D st y)
    (mul_nonneg (Nat.cast_nonneg P) (rate_pos ks).le) steps
    (estimatedResidualInput HP D id R l ks km kt n ss sm st kb Kc cutoff raw prep maximum precision)
  exact hn.trans (mul_le_mul_of_nonneg_left
    (estimatedResidualInput_moment_le HP hK D R H l ks km kt n hks ss sm st kb Kc
      cutoff CB hCB hcut raw prep maximum precision) (by rw [pow_mul]; positivity))


/-- Positive tolerance pays scaled centered RAW noise, for any factor `amplification ≥ 0` and at
least `spectralWalkLength` steps. One admissible factor is the second-envelope amplification
P * (|ζ| * (Lh + Lρ) / rate kt)^4, for any reals ζ, Lh and Lρ; no RAW units are canceled. -/
theorem estimatedResidualInput_scaled_noise_le_dyadic
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (hK : 0 < HP.K)
    (D : ZMod P) (R : RoleProfile J) (H : Horizon P)
    (l ks km kt n : ℕ) (hks : ks ≤ H.maxExponent)
    (ss sm st : List (ZMod P)) (kb : ℕ → ℕ) (Kc : ℕ) (cutoff : ℕ → ℝ → ℝ)
    (CB : ℕ → ℝ) (hCB : ∀ i, 0 ≤ CB i)
    (hcut : ∀ i v, cutoff i v ∈ Set.Icc 0 (CB i))
    (raw prep : ℕ → ℕ → HierarchyTask.Request HP.k (Fin J) (ZMod P) →
      Environment P J → Matrix (ZMod P) (ZMod P) ℝ)
    (maximum : ℕ → ℕ → HierarchyTask.Request HP.k (Fin J) (ZMod P) →
      Environment P J → ZMod P → ℝ) (precision steps : ℕ)
    {amplification ε : ℝ} (ha : 0 ≤ amplification) (hε : 0 < ε) (slack : ℕ)
    (hsteps : spectralWalkLength (1 - 1 / (155648 * (J + 1) * (4 : ℝ) ^ 4))
      (amplification * 32 * (16 * P * (estimatedResidualBound HP P km kt n kb CB) ^ 4))
      ε slack ≤ steps) :
    let input := estimatedResidualInput HP D id R l ks km kt n ss sm st kb Kc cutoff
      raw prep maximum precision
    let F := conditionalWalk (NormalizedMoments.retainedMask R.source (side P ks) D ss)
        (NormalizedMoments.retainedMask R.terminal (side P kt) D st)
        (graph R.source R.terminal R.source_terminal (side P ks) (side P kt)
          (side_le P ks) (side_le P kt) (fun x => CopyPadding.identifier D ss x)
          (fun y => CopyPadding.identifier D st y)) (fun _ _ => steps)
        (estimatedResidualInput HP D id R l ks km kt n ss sm st kb Kc cutoff
          raw prep maximum precision)
    amplification * rowNormPow 4 P (rate ks)
      (NormalizedMoments.retainedMask R.source (side P ks) D ss)
      (NormalizedMoments.retainedMask R.terminal (side P kt) D st)
      (fun σ x y => F σ x y - rowSliceMean
        (NormalizedMoments.retainedMask R.source (side P ks) D ss)
        (NormalizedMoments.retainedMask R.terminal (side P kt) D st) input x y) ≤
      (ε * (64 : ℝ)⁻¹ ^ slack) ^ 4 := by
  dsimp only
  have hden : (1 : ℝ) < 155648 * (J + 1) * (4 : ℝ) ^ 4 := by
    have : (0 : ℝ) ≤ J := Nat.cast_nonneg J
    nlinarith
  have hr : 0 < 1 - 1 / (155648 * (J + 1) * (4 : ℝ) ^ 4) :=
    sub_pos.mpr ((div_lt_one (by linarith)).mpr hden)
  have hp := spectralWalkLength_payment hr (sub_lt_self _ (by positivity))
    (show 0 ≤ amplification * 32 * (16 * P *
      (estimatedResidualBound HP P km kt n kb CB) ^ 4) from by positivity)
    hε slack steps hsteps
  have hn := mul_le_mul_of_nonneg_left
    (estimatedResidualInput_noise_le HP hK D R H l ks km kt n hks ss sm st kb Kc
      cutoff CB hCB hcut raw prep maximum precision steps) ha
  exact hn.trans (by convert hp using 1; ring)

end Matrix.HierarchyParams.H4RankEnvironment
