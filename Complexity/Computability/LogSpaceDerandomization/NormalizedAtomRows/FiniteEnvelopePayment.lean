/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate
public import Complexity.Computability.LogSpaceDerandomization.NormalizedAtomRows.CommonEnvelope

/-!
# Common-envelope payment for the actual finite estimated residual

The lower-child conditional-error costs pay one common deterministic B for each channel.
The RAW walk requirement is a numerical spectral payment from the actual finite input
range, rather than a hypothesis about the final noise or common B. Finite coverage,
true-input cutoff/gate agreement and the narrower usage horizon remain explicit.
The original finite allocation costs m times the larger channel payment; it makes no
claim of convergent recursive reserves or parameter/workspace growth.
The row/normalization proof patterns are adapted from Samuel Schlesinger.

## Main results

* `actualEstimatedResidual_common_envelope_payment`: conditional lower-child costs and
  the actual finite RAW spectral payment pay both common deterministic matrices.
-/
public section
noncomputable section
namespace Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
open Finset Cslib Cslib.Probability Cslib.RowCompression
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {P J : ℕ} [Fact P.Prime]

set_option backward.isDefEq.respectTransparency false in
/-- Actual finite once-negative residual payment, deriving both common-B row moments
from actual conditional lower-child costs and a numerical RAW spectral payment.
Correction km and parent rank/normalization kt remain distinct. -/
theorem actualEstimatedResidual_common_envelope_payment
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
    {Lh Lρ : ℝ} (hLh : 0 ≤ Lh) (hLρ : 0 ≤ Lρ) (ζ : ℝ) (m : ℕ) (childBudget rawBudget : ℝ) :
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
    let cost := fun j x y => HierarchyTask.conditionalChildCost channelsV (range (n + 1)) l
      source mid terminal (fun i => rate (kb i))
      (2 * HP.Q HP.toHierarchyParams.atomCap) (2 * max cap 16)
      (estimated (j + 1)) canonical x y
    (∀ i < m, rowNormPow 4 P (rate ks) (retainedMask R.source (side P ks) D ss)
      (retainedMask R.terminal (side P kt) D st) (fun _ => cost i) ≤ childBudget) →
    (∀ i < m, 32 * (1 - 1 / (155648 * (J + 1) * (4 : ℝ) ^ 4)) ^ (2 * steps (i + 1)) *
      (16 * P * (estimatedResidualBound HP P km kt n kb (estimatedBinCap cap)) ^ 4) ≤ rawBudget) →
    ∀ ν : Fin 2, rowNormPow 4 P (rate ks) (retainedMask R.source (side P ks) D ss)
      (retainedMask R.terminal (side P (if ν = 0 then kt else ku)) D st)
      (fun _ => commonMeanEnvelope R D ss st ks kt ku m Lh Lρ ζ input F G ν) ≤
    m * max ((rate kt)⁻¹ ^ 4 * childBudget)
      (P * (|ζ| * (Lh + Lρ) / rate kt) ^ 4 * (8 * (rawBudget + childBudget))) := by
  extract_lets cutoff bounded source mid terminal estimated canonical channelsV input G F cost
  intro hc hz ν
  have hHPK : 0 < HP.K := by
    have hg := HP.gate
    have hn : 0 ≤ 32 * (HP.k : ℝ) / HP.η := div_nonneg (mul_nonneg (by norm_num)
      (Nat.cast_nonneg _)) HP.η_pos.le
    have hk : (0 : ℝ) < HP.K := by linarith
    exact_mod_cast hk
  apply commonMeanEnvelope_moment_le_cost R D ss st ks kt ku m husage hLh hLρ ζ input F G
    (HP.toHierarchyParams.residual_nonneg (rate_pos km) hC) cost ?_
    (mul_nonneg (Nat.cast_nonneg P) (rate_pos ks).le) hc ?_ ν
  · intro j _ x y
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
  · intro i hi
    exact (estimatedResidualInput_noise_le HP hHPK D R H l ks km kt n ksH ss sm st kb Kc
      bounded (estimatedBinCap cap) (fun i => by unfold estimatedBinCap; split_ifs <;> positivity)
      (boundedRoutedBinCutoff_grid_range χ kb hcap hχmono hχ0 hχ hχrange hanti hratio)
      raw prep maximum (i + 1) (steps (i + 1))).trans (hz i hi)

end Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
