/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate
public import Complexity.Foundations.Probability.NormalizedAtomRows.ReserveOutput
public import Complexity.Foundations.Probability.NormalizedAtomRows.ChildRootReserve

/-!
# Actual finite output from lower-child rooted errors

This discharges the conditional cost premise of `ReserveOutput` using bounded normalized
lower-child rooted moments on their own source and full terminal rank. The finite sufficient
allocation displays its environment cardinality, width, bin, rate and density costs.
It does not prove recursive accuracy, copy routing, parameter/workspace growth or RL=L.
The underlying row/normalization assembly is adapted from Samuel Schlesinger.
-/
public section
noncomputable section
namespace Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
open Finset Cslib Cslib.Probability Cslib.RowCompression
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {P J : ℕ} [Fact P.Prime]

set_option backward.isDefEq.respectTransparency false in
/-- Actual finite output from explicit per-request rooted-error budgets on bounded
normalized children. The lower-child conditional cost reserve is discharged. The allocation
is finite and conservative; recursive accuracy and parameter/workspace closure remain open. -/
theorem actualEstimatedResidual_output_from_root_budgets
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
    (ku : ℕ) (husage : kt ≤ ku) (ktH : kt ≤ H.maxExponent)
    {Lh Lρ : ℝ} (hLh : 0 ≤ Lh) (hLρ : 0 ≤ Lρ)
    (hh : ∀ a b, |polynomialPrepCutoff4 HP.θ a - polynomialPrepCutoff4 HP.θ b| ≤ Lh * |a - b|)
    (hρ : ∀ a b, |HP.ρ a - HP.ρ b| ≤ Lρ * |a - b|)
    {ζ scale floor : ℝ} (hζ : 0 < ζ) (hs : 0 < scale) (hmargin : scale ≤ HP.η)
    (hsmall : ζ ≤ scale / 2) (hcapscale : scale ≤ HP.toHierarchyParams.atomCap / 10000)
    (hfloor : 0 < floor) (hfloors : floor ≤ scale) (hfloor1 : floor ≤ 1) (hfloorθ : floor ≤ HP.θ)
    (m : ℕ) (hm : 0 < m) :
    ∃ Cbound : ℝ, 0 ≤ Cbound ∧ ∀ ε : ℝ, 0 < ε →
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
    let T := fun j σ x y => selectedPreparation HP D R st kt (F j) σ x y
    let W := fun j => conditionalWalk (retainedMask R.source (side P ks) D ss)
      (retainedMask R.terminal (side P ku) D st)
      (graph R.source R.terminal R.source_terminal (side P ks) (side P ku)
        (side_le P ks) (side_le P ku) (fun x => CopyPadding.identifier D ss x)
        (fun y => CopyPadding.identifier D st y)) (fun _ _ => prepSteps j) (T j)
    let Δ := firstSignalIncrement F kt (secondSignalIncrement W ζ)
    (∀ j < m, ∀ i r,
      (i, r) ∈ HierarchyTask.residualErrorCalls (k := HP.k) (range (n + 1)) l
        source mid terminal (fun i => rate (kb i)) →
      rootDistPow 4 P r.source.rate
        (fun σ x => r.source.retains channelsV σ x)
        (fun σ y => r.terminal.retains channelsV σ y)
        (fun σ => estimated (j + 1) i σ r) (fun σ => canonical i σ r) ≤
      ((tolerance ^ 4 / (1 + (rate kt)⁻¹ ^ 4 + amplification)) /
        (1 + (Fintype.card (ZMod P) : ℝ) ^ 2 / ((P : ℝ) * rate ks) *
          HierarchyTask.residualCostCoefficient (k := HP.k) channelsV (range (n + 1)) l
            source mid terminal (fun i => rate (kb i))
            (2 * HP.Q HP.toHierarchyParams.atomCap) (2 * max cap 16))) /
        (1 + (4 * (max (2 * HP.Q HP.toHierarchyParams.atomCap) (2 * max cap 16)) ^
          ((3 : ℝ) / 4)) ^ 4 * ((P : ℝ) * r.source.rate * Fintype.card (Environment P J)))) →
    rowNormPow 4 P (rate ks) (retainedMask R.source (side P ks) D ss)
      (retainedMask R.terminal (side P ku) D st)
      (fun σ x y => actualNormalizedCompatible HP ζ floor R.terminal (side P ku) D st kt m
        Δ (fun _ _ _ _ => 0) σ x y ^ (4⁻¹ : ℝ) -
        genuineNormalizedRecipe HP R.source R.terminal (side P ks) (side P ku) D ss st kt G σ x y ^
          (4⁻¹ : ℝ)) ≤ Cbound * ε ^ 4 := by
  obtain ⟨Cbound, hCbound, hout⟩ := actualEstimatedResidual_output_from_cost_reserves
    HP D hD H R l ks km kt n ksH hms ss sm st kb hbH C hC hC1 hCf χ hχ h ρ K hkh
    hρ0 hρ1 hη hρη hK hχmono hχ0 hχrange hanti hratio hcap hCcap Kc raw prep maximum hcover
    ku husage ktH hLh hLρ hh hρ hζ hs hmargin hsmall hcapscale hfloor hfloors hfloor1 hfloorθ m hm
  refine ⟨Cbound, hCbound, ?_⟩
  intro ε hε
  extract_lets amplification tolerance r payment rawSteps prepSteps cutoff bounded source mid
    terminal estimated canonical channelsV input G F T W Δ
  intro hroot
  apply hout ε hε
  intro j hj
  have hp := actual_conditionalChildCost_le_of_root_budgets HP D R l ks km kt n ss sm st kb
    C hC χ hχ h ρ K (fun v => ⟨hρ0 v, hρ1 v⟩) hχmono hχ0 hχrange hanti hratio hcap hCcap
    Kc (raw (j + 1)) (prep (j + 1)) (maximum (j + 1))
    (δ := tolerance ^ 4 / (1 + (rate kt)⁻¹ ^ 4 + amplification))
    (by dsimp only [amplification]; positivity)
    (hroot j hj)
  unfold HierarchyTask.conditionalChildCost at hp ⊢
  unfold retainedMask
  convert hp using 1;
    simp only [rowSliceMean, CorrectionRowTask.Channel.retains, channels, gridChannel,
      semanticSide_grid, id_eq]
  congr!

end Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
