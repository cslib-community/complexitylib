/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate
public import CslibFrontier.Computability.LogSpaceDerandomization.NormalizedAtomRows.FiniteEnvelopePayment
public import CslibFrontier.Computability.LogSpaceDerandomization.NormalizedAtomRows.ActualMoment

/-!
# Conditional finite output from actual lower-child cost reserves

Completed full-terminal RAW walking precedes selected preparation and the narrower
preparation walk. Both signals enter the actual compatible-capacity compression iterate.
Only actual lower-child conditional-error-cost row moments are reserved. The finite
allocation retains visible horizon dependence and full B1 width/rate amplification.
This is an original finite assembly of the existing conditional output theorem.
Recursive reserve induction, copy routing and parameter/workspace growth remain open.
The output constant is chosen after HP, ζ, scale and the positive floor, before the
prime, environment width, horizon, prefix length or child families. Child accuracies may
therefore be chosen using that constant without depending circularly on those families.
This uniformity concerns the final output coefficient only; the displayed allocation and
walk lengths still retain their P, rate, bin and finite-horizon factors.
The row/normalization proof patterns are adapted from Samuel Schlesinger.

## Main results

* `actualEstimatedResidual_output_from_cost_reserves`: finite output fourth-root error
  bound from conditional lower-child cost moments, with both walk lengths chosen.
-/
public section
noncomputable section
namespace Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
open Finset Cslib Cslib.Probability Cslib.RowCompression
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {P J : ℕ} [Fact P.Prime]

private lemma allocation_max_le (m : ℕ) {a b ε : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hε : 0 ≤ ε) :
    let d := (ε / (2 * (m + 1))) ^ 4
    (m : ℝ) * max (a * (d / (1 + a + b)))
      (b * (8 * (d / (1 + b) + d / (1 + a + b)))) ≤ ε ^ 4 := by
  dsimp only
  let d := (ε / (2 * (m + 1))) ^ 4
  have hd : 0 ≤ d := by dsimp only [d]; positivity
  have ha' : a * (d / (1 + a + b)) ≤ d := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hb' : b * (d / (1 + a + b)) ≤ d := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hb'' : b * (d / (1 + b)) ≤ d := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hp : max (a * (d / (1 + a + b)))
      (b * (8 * (d / (1 + b) + d / (1 + a + b)))) ≤ 16 * d :=
    max_le (by linarith) (by nlinarith only [hb', hb''])
  apply (mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg m)).trans
  change (m : ℝ) * (16 * (ε / (2 * (m + 1))) ^ 4) ≤ ε ^ 4
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hm2 : (m : ℝ) + 1 ≤ ((m : ℝ) + 1) ^ 2 := by nlinarith
  have hm4 : (m : ℝ) ≤ ((m : ℝ) + 1) ^ 4 := by nlinarith [sq_nonneg (((m : ℝ) + 1) ^ 2 - 1)]
  calc
    _ = (m : ℝ) * ε ^ 4 / ((m : ℝ) + 1) ^ 4 := by
      rw [div_pow, mul_pow]
      field_simp
      ring
    _ ≤ ε ^ 4 := (div_le_iff₀ (by positivity)).mpr
      (by nlinarith [mul_le_mul_of_nonneg_right hm4 (pow_nonneg hε 4)])

set_option backward.isDefEq.respectTransparency false in
/-- Actual finite output at the genuine canonical residual, under explicit conditional
lower-child cost reserves. Common B, both endpoint ROW noises, nonnegativity, row mass
and zero extension are derived. No recursive growth or native RL=L endpoint is claimed. -/
theorem actualEstimatedResidual_output_from_cost_reserves
    (HP : FourthRootHierarchyParams 16 1 16 32 8)
    {ζ scale floor : ℝ} (hζ : 0 < ζ) (hs : 0 < scale) (hmargin : scale ≤ HP.η)
    (hsmall : ζ ≤ scale / 2) (hcapscale : scale ≤ HP.toHierarchyParams.atomCap / 10000)
    (hfloor : 0 < floor) (hfloors : floor ≤ scale) (hfloor1 : floor ≤ 1) (hfloorθ : floor ≤ HP.θ) :
    ∃ Cbound : ℝ, 0 ≤ Cbound ∧
    ∀ (P J : ℕ) [Fact P.Prime] (D : ZMod P)
    (_hD : D ≠ 0) (H : Horizon P) (R : RoleProfile J)
    (l ks km kt n : ℕ) (_ksH : ks ≤ H.maxExponent) (_hms : km ≤ ks)
    (ss sm st : List (ZMod P)) (kb : ℕ → ℕ)
    (_hbH : ∀ i ∈ range (n + 1), kb i ≤ H.maxExponent)
    (C : Matrix (ZMod P) (ZMod P) ℝ) (_hC : ∀ x y, 0 ≤ C x y) (_hC1 : C *ᵥ 1 ≤ 1)
    (_hCf : ∀ x y, C x y ≤ rate km)
    (χ : ℝ → ℝ) (_hχ : ∀ v, 1 ≤ v → χ v = 1)
    (h : ℕ → ℝ → ℝ) (ρ : ℝ → ℝ) (K : ℕ)
    (_hkh : ∀ i ∈ range (n + 1), ∀ v,
      routedBinCutoff χ (fun i => rate (kb i)) i (fun _ => 1) v ≠ 0 → h i v = 1)
    (_hρ0 : ∀ v, 0 ≤ ρ v) (_hρ1 : ∀ v, ρ v ≤ 1) {η : ℝ}
    (_hη : 0 < η) (_hρη : ∀ v, v ≤ η → ρ v = 1)
    (_hK : 2 * (1 + 32 / η) ≤ K)
    (_hχmono : Monotone χ) (_hχ0 : ∀ v, v ≤ 1 / 2 → χ v = 0)
    (_hχrange : ∀ v, χ v ∈ Set.Icc 0 1)
    (_hanti : Antitone (fun i => rate (kb i)))
    (_hratio : ∀ i, rate (kb i) / rate (kb (i + 1)) ≤ 16)
    {cap : ℝ} (_hcap : 0 ≤ cap) (_hCcap : ∀ z w, C z w ≤ cap * rate (kb 0))
    (Kc : ℕ)
    (_hcover : ∀ z y, C z y = 0 ∨ rate (kb n) ≤ C z y)
    (ku : ℕ) (_husage : kt ≤ ku) (_ktH : kt ≤ H.maxExponent)
    {Lh Lρ : ℝ} (_hLh : 0 ≤ Lh) (_hLρ : 0 ≤ Lρ)
    (_hh : ∀ a b, |polynomialPrepCutoff4 HP.θ a - polynomialPrepCutoff4 HP.θ b| ≤ Lh * |a - b|)
    (_hρ : ∀ a b, |HP.ρ a - HP.ρ b| ≤ Lρ * |a - b|)
    (m : ℕ) (_hm : 0 < m),
    ∀ (raw prep : ℕ → ℕ → HierarchyTask.Request HP.k (Fin J) (ZMod P) →
      Environment P J → Matrix (ZMod P) (ZMod P) ℝ)
    (maximum : ℕ → ℕ → HierarchyTask.Request HP.k (Fin J) (ZMod P) →
      Environment P J → ZMod P → ℝ),
    ∀ ε : ℝ, 0 < ε →
    let amplification : ℝ := P * (|ζ| * (Lh + Lρ) / rate kt) ^ 4
    let tolerance := ε / (2 * (m + 1))
    let r : ℝ := 1 - 1 / (155648 * (J + 1) * (4 : ℝ) ^ 4)
    let payment := 16 * P * (estimatedResidualBound HP P km kt n kb (estimatedBinCap cap)) ^ 4
    let rawSteps := fun j => max
      (spectralWalkLength r ((rate kt)⁻¹ ^ 4 * 32 * payment) ε (dyadicSlack m (j - 1)))
      (spectralWalkLength r ((1 + amplification) * 32 * payment) tolerance 0)
    let prepSteps := fun j => spectralWalkLength r (ζ ^ 4 * 512 * HP.K) ε (dyadicSlack m (j - 1))
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
        (fun y => CopyPadding.identifier D st y)) (fun _ _ => rawSteps j) (input j)
    let cost := fun j x y => HierarchyTask.conditionalChildCost channelsV (range (n + 1)) l
      source mid terminal (fun i => rate (kb i))
      (2 * HP.Q HP.toHierarchyParams.atomCap) (2 * max cap 16)
      (estimated (j + 1)) canonical x y
    let T := fun j σ x y => selectedPreparation HP D R st kt (F j) σ x y
    let W := fun j => conditionalWalk (retainedMask R.source (side P ks) D ss)
      (retainedMask R.terminal (side P ku) D st)
      (graph R.source R.terminal R.source_terminal (side P ks) (side P ku)
        (side_le P ks) (side_le P ku) (fun x => CopyPadding.identifier D ss x)
        (fun y => CopyPadding.identifier D st y)) (fun _ _ => prepSteps j) (T j)
    let Δ := firstSignalIncrement F kt (secondSignalIncrement W ζ)
    (∀ i < m, rowNormPow 4 P (rate ks) (retainedMask R.source (side P ks) D ss)
      (retainedMask R.terminal (side P kt) D st) (fun _ => cost i) ≤
        tolerance ^ 4 / (1 + (rate kt)⁻¹ ^ 4 + amplification)) →
    rowNormPow 4 P (rate ks) (retainedMask R.source (side P ks) D ss)
      (retainedMask R.terminal (side P ku) D st)
      (fun σ x y => actualNormalizedCompatible HP ζ floor R.terminal (side P ku) D st kt m
        Δ (fun _ _ _ _ => 0) σ x y ^ (4⁻¹ : ℝ) -
        genuineNormalizedRecipe HP R.source R.terminal (side P ks) (side P ku) D ss st kt G σ x y ^
          (4⁻¹ : ℝ)) ≤ Cbound * ε ^ 4 := by
  obtain ⟨_, _, hfloorbound⟩ := actual_normalized_fourth_moment_compatible HP hζ hs hmargin
    hsmall hcapscale
  obtain ⟨Cbound, hCbound, hout⟩ := hfloorbound floor hfloor hfloors hfloor1 hfloorθ
  refine ⟨Cbound, hCbound, ?_⟩
  intro P J inst D hD H R l ks km kt n ksH hms ss sm st kb hbH C hC hC1 hCf χ hχ h ρ K hkh
    hρ0 hρ1 η hη hρη hK hχmono hχ0 hχrange hanti hratio cap hcap hCcap Kc hcover ku husage ktH
    Lh Lρ hLh hLρ hh hρ m hm raw prep maximum ε hε
  extract_lets amplification tolerance r payment rawSteps prepSteps cutoff bounded source mid
    terminal
    estimated canonical channelsV input G F cost T W Δ
  intro hreserve
  have hHPK : 0 < HP.K := by
    have hg := HP.gate
    have hn : 0 ≤ 32 * (HP.k : ℝ) / HP.η :=
      div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) HP.η_pos.le
    have hk : (0 : ℝ) < HP.K := by linarith
    exact_mod_cast hk
  have htol : 0 < tolerance := by dsimp only [tolerance]; positivity
  have hamp : 0 ≤ amplification := by dsimp only [amplification]; positivity
  have hden : (1 : ℝ) < 155648 * (J + 1) * (4 : ℝ) ^ 4 := by
    have : (0 : ℝ) ≤ J := Nat.cast_nonneg J
    nlinarith
  have hr : 0 < r := sub_pos.mpr ((div_lt_one (by linarith)).mpr hden)
  have hr1 : r < 1 := sub_lt_self _ (by positivity)
  have hG : ∀ x y, 0 ≤ G x y := HP.toHierarchyParams.residual_nonneg (rate_pos km) hC
  let B := commonMeanEnvelope R D ss st ks kt ku m Lh Lρ ζ input F G
  have hrawpay (i : ℕ) (_hi : i < m) : 32 * r ^ (2 * rawSteps (i + 1)) * payment ≤
      tolerance ^ 4 / (1 + amplification) := by
    have hp := spectralWalkLength_payment hr hr1
      (by dsimp only [payment]; positivity : 0 ≤ (1 + amplification) * 32 * payment)
      htol 0 (rawSteps (i + 1)) (Nat.le_max_right _ _)
    simp only [pow_zero, mul_one] at hp
    apply (le_div_iff₀ (by positivity : 0 < 1 + amplification)).mpr
    nlinarith only [hp]
  have hBrow (ν : Fin 2) : rowNormPow 4 P (rate ks)
      (retainedMask R.source (side P ks) D ss)
      (retainedMask R.terminal (if ν = 0 then side P kt else side P ku) D st) (fun _ => B ν)
        ≤ ε ^ 4 := by
    have hp := actualEstimatedResidual_common_envelope_payment HP D hD H R l ks km kt n ksH hms
      ss sm st kb hbH C hC hC1 hCf χ hχ h ρ K hkh hρ0 hρ1 hη hρη hK
      hχmono hχ0 hχrange hanti hratio hcap hCcap Kc raw prep maximum hcover rawSteps ku husage
      hLh hLρ ζ m (tolerance ^ 4 / (1 + (rate kt)⁻¹ ^ 4 + amplification))
      (tolerance ^ 4 / (1 + amplification)) hreserve hrawpay ν
    change rowNormPow 4 P (rate ks) _ _ (fun _ => B ν) ≤ _ at hp
    have hnum := allocation_max_le (m := m) (a := (rate kt)⁻¹ ^ 4) (b := amplification)
      (by positivity) hamp hε.le
    simpa only [apply_ite] using hp.trans hnum
  apply hout P J R.source R.terminal R.source_terminal.symm (side P ks) (side P ku) D hD ss
    st H kt ktH
    (by
      rw [side_eq_ceil, side_eq_ceil]
      exact Nat.ceil_mono (mul_le_mul_of_nonneg_left
        (inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) husage)) (by positivity)))
    G hG (fun x => (HP.toHierarchyParams.residual_sum_le_one _ _ (rate_pos km) hC1 x).trans
      (by have := Nat.cast_nonneg (α := ℝ) HP.k; linarith)) P (rate ks) ε
    (mul_nonneg (Nat.cast_nonneg P) (rate_pos ks).le) hε.le m hm Δ (fun _ _ _ _ => 0) B
    (commonMeanEnvelope_nonneg R D ss st ks kt ku m Lh Lρ ζ input F G) ?_ hBrow ?_ ?_
  · exact actualTwoSignal_mean_le_common HP hHPK D R ks kt ku m husage ss st input rawSteps
      prepSteps
      hLρ hh hρ ζ G
  · intro ν i hi
    fin_cases ν
    · change rowNormPow 4 P (rate ks) (retainedMask R.source (side P ks) D ss)
        (retainedMask R.terminal (side P kt) D st)
        (actualNoiseEntry R.source R.terminal (side P ks) (side P kt) (side P kt) D ss st kt G
          Δ (fun _ _ _ _ => 0) 0 i) ≤ (ε * (1 / 64 : ℝ) ^ dyadicSlack m i) ^ 4
      simpa only [one_div] using actualEstimatedFirstSignal_noise_le_dyadic HP hHPK D R H l
        ks km kt n ksH ss sm st kb Kc
        bounded (estimatedBinCap cap) (fun i => by unfold estimatedBinCap; split_ifs <;> positivity)
        (boundedRoutedBinCutoff_grid_range χ kb hcap hχmono hχ0 hχ hχrange hanti hratio)
        raw prep maximum rawSteps G hG (secondSignalIncrement W ζ) (fun _ _ _ _ => 0)
        (by intros; rfl) i hε m (by simpa only [rawSteps, Nat.add_sub_cancel] using (Nat.le_max_left
          (spectralWalkLength r ((rate kt)⁻¹ ^ 4 * 32 * payment) ε (dyadicSlack m i))
          (spectralWalkLength r ((1 + amplification) * 32 * payment) tolerance 0)))
    · change rowNormPow 4 P (rate ks) (retainedMask R.source (side P ks) D ss)
        (retainedMask R.terminal (side P ku) D st)
        (actualNoiseEntry R.source R.terminal (side P ks) (side P kt) (side P ku) D ss st kt G
          Δ (fun _ _ _ _ => 0) 1 i) ≤ (ε * (1 / 64 : ℝ) ^ dyadicSlack m i) ^ 4
      simpa only [one_div] using actualSelectedSecondSignal_noise_le_dyadic HP hHPK D R H ks
        kt ku husage ksH ss st F F
        prepSteps ζ G i m hε (by simp only [prepSteps, Nat.add_sub_cancel]; exact le_rfl)
  · intro i σ x y hy
    exact (actualTwoSignal_zero_off R.source R.terminal (side P ks) (side P ku) D ss st
      (fun _ => graph R.source R.terminal R.source_terminal (side P ks) (side P ku)
        (side_le P ks) (side_le P ku) (fun x => CopyPadding.identifier D ss x)
        (fun y => CopyPadding.identifier D st y)) (fun j _ _ => prepSteps j) T F kt ζ σ x y hy).1 i

end Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
