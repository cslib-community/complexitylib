/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate
public import Complexity.Foundations.Probability.HierarchyEstimatedInput
public import Complexity.Foundations.Probability.HierarchyChildRootMoment

/-!
# Estimated-child mean error against the genuine finite residual

Actual bounded incoming children are compared to canonical requests, after proving that
bounded routed cutoffs preserve their true inputs. The top cap and adjacent ratio 16
provide the genuine dense range; the actual correction range pays the other coefficient.
The joint source × terminal mean subtracts the proved canonical residual mean, with positive
bins summed and exactly one negative error. No independence or desired-reference field is
used. Finite coverage, narrower source, all suffixes and horizons remain explicit.
This original finite absolute theorem does not establish recursive budgets or copy routing.
-/
public section
open Finset Cslib Cslib.Probability
open scoped BigOperators
noncomputable section
namespace Matrix.HierarchyParams.H4RankEnvironment
attribute [local instance] Classical.propDecidable
variable {P J : ℕ} [Fact P.Prime] {V : Type} [Fintype V]
  (HP : FourthRootHierarchyParams 16 1 16 32 8) (D : ZMod P) (ident : V → ZMod P)

/-- Actual finite absolute propagation from four per-request errors. The special negative
payment occurs once. The target is the genuine residual, never a clipped-bin target. -/
theorem estimated_residual_bins_mean_error
    (hD : D ≠ 0) (hid : Function.Injective ident) (H : Horizon P) (R : RoleProfile J)
    (l ks km kt n : ℕ) (ksH : ks ≤ H.maxExponent) (hms : km ≤ ks)
    (ss sm st : List (ZMod P)) (kb : ℕ → ℕ)
    (hbH : ∀ i ∈ range (n + 1), kb i ≤ H.maxExponent)
    (C : Matrix V V ℝ) (hC : ∀ x y, 0 ≤ C x y) (hC1 : C *ᵥ 1 ≤ 1)
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
    (raw prep : ℕ → HierarchyTask.Request HP.k (Fin J) (ZMod P) →
      Environment P J → Matrix V V ℝ)
    (maximum : ℕ → HierarchyTask.Request HP.k (Fin J) (ZMod P) →
      Environment P J → V → ℝ)
    (x y : V) (hcover : ∀ z, C z y = 0 ∨ rate (kb n) ≤ C z y) :
    let cutoff := fun i => routedBinCutoff χ (fun i => rate (kb i)) i (fun _ => 1)
    let bounded := fun i => boundedRoutedBinCutoff χ (fun i => rate (kb i)) cap i (fun _ => 1)
    let source := gridChannel R.source ks ss
    let mid := gridChannel R.midpoint km sm
    let terminal := gridChannel R.terminal kt st
    let estimated := fun i σ r => incomingChildren HP D ident Kc (bounded i)
      (raw i) (prep i) (maximum i) r σ
    let canonical := fun i σ r => canonicalRequestChild HP D ident C
      (cutoff i) (h i) ρ K r σ
    let channelsV := fun role b suffix σ v => channels D role b suffix σ (ident v)
    let S := ({σ : Environment P J | source.retains (channels D) σ (ident x) ∧
      terminal.retains (channels D) σ (ident y)} : Finset _)
    |(𝔼 σ ∈ S, estimatedResidualInput HP D ident R l ks km kt n ss sm st kb Kc
      bounded (fun _ => raw) (fun _ => prep) (fun _ => maximum) 0 σ x y) -
      HP.toHierarchyParams.residual (canonicalChannel ident (rate km))
        (canonicalChannel ident (rate km)) (rate km) C x y| ≤
    𝔼 σ ∈ S, ((∑ i ∈ range (n + 1), HierarchyTask.positiveChildError channelsV
      l i .residual source mid terminal (rate (kb i))
      (2 * HP.Q HP.toHierarchyParams.atomCap) (2 * max cap 16)
      (estimated i σ) (canonical i σ) x y) +
      HierarchyTask.negativeChildError channelsV l 0 .residual source mid terminal
        (rate (kb 0)) (estimated 0 σ) (canonical 0 σ) x y) := by
  dsimp only [estimatedResidualInput]
  have hm := canonical_residual_bins_mean HP D ident hD hid H R l ks km kt n ksH hms
    ss sm st kb hbH C hC hC1 hCf χ hχ h ρ K hkh hρ0 hρ1 hη hρη hK x y hcover
  dsimp only at hm
  rw [← hm]
  apply HierarchyTask.residual_bins_sub_le
  · intro i _ σ _ z
    exact incomingChildren_final_range HP D ident Kc _ (raw i) (prep i) (maximum i)
      _ l rfl σ x z
  · intro i _ σ _ z
    change |denseChild D ident _ _ (h i) ρ K C σ z y| ≤ 2 * max cap 16
    let r := (HierarchyTask.rawRequests (k := HP.k) l i .residual
      (gridChannel R.source ks ss) (gridChannel R.midpoint km sm)
      (gridChannel R.terminal kt st) (rate (kb i))).right
    have heq := denseChild_congr_cutoff D ident r C
      (routedBinCutoff χ (fun j => rate (kb j)) i (fun _ => 1))
      (boundedRoutedBinCutoff χ (fun j => rate (kb j)) cap i (fun _ => 1))
      (h i) ρ K (fun a b => (boundedRoutedBinCutoff_div_eq
        (fun j => rate_pos (kb j)) (hC a b) (hCcap a b) i).symm) σ
    rw [heq]
    exact denseChild_range D ident r C _ (h i) ρ K
      (le_trans hcap (le_max_left _ _))
      (boundedRoutedBinCutoff_mem_Icc hcap (le_trans hcap (le_max_left _ _))
        (le_max_left _ _) hχmono hχ0 hχ hχrange (fun j => rate_pos (kb j)) hanti
        (fun j => (hratio j).trans (le_max_right _ _))
        (fun _ => 1) (fun _ => ⟨zero_le_one, le_rfl⟩) i)
      (fun v => ⟨hρ0 v, hρ1 v⟩) σ z y

end Matrix.HierarchyParams.H4RankEnvironment
