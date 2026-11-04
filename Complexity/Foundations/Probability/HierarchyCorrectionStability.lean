/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate
public import Complexity.Foundations.Probability.HierarchyRankCutoffs

/-!
# Pilot-maximum sensitivity of actual correction requests

The actual incoming-normalized correction multiplies a bounded nonnegative coefficient
by the pilot cutoff. Fourth-root regularity of that cutoff therefore controls a change
in the completed pilot maximum, with raw and preparatory children held fixed. The
coefficient is uniform in the prime, channels, raw entries and preparatory estimates.
All functions use the same environment, including the source/usage normalizer.

This original local contract does not control changes to raw or preparatory children,
construct approximate pilot maxima, or close a recursive estimator. The underlying
normalization and bounded-range arguments retain Samuel Schlesinger's credit.

## Main results

* `correctionRequest_congr_normalizer`: preparation substitution using only joint means.
* `correctionRequest_multiplier`: exact factorization of the pilot multiplier.
* `correctionRequest_maximum_root_stability`: uniform pointwise fourth-root sensitivity.
* `correctionRequest_maximum_root_moment`: integrated sensitivity on the original masks.
-/
public section
noncomputable section
namespace Matrix.HierarchyParams.H4RankEnvironment
open Finset Cslib Cslib.Probability
attribute [local instance] Classical.propDecidable
variable {P J : ℕ} [Fact P.Prime] {V : Type*} [Fintype V]

/-- A correction reads its preparation only through the literal joint source/usage
normalizer. Equal means suffice even when the preparatory functions differ pointwise. -/
theorem correctionRequest_congr_normalizer {k : ℕ}
    (D : ZMod P) (ident : V → ZMod P)
    (r : HierarchyTask.Request k (Fin J) (ZMod P)) (hr : Admissible r)
    (I : ℝ → ℝ → ℝ) (τ ρ Q γ : ℝ → ℝ) (K Kc : ℕ)
    (raw prep prep' : Environment P J → Matrix V V ℝ)
    (maximum : Environment P J → V → ℝ) (x y : V)
    (hm : rowSliceMean (fun σ v => r.source.retains (channels D) σ (ident v))
      (fun σ v => r.usage.retains (channels D) σ (ident v)) prep x y =
      rowSliceMean (fun σ v => r.source.retains (channels D) σ (ident v))
        (fun σ v => r.usage.retains (channels D) σ (ident v)) prep' x y)
    (σ : Environment P J) :
    correctionRequest D ident r I τ ρ Q γ K Kc raw prep maximum σ x y =
      correctionRequest D ident r I τ ρ Q γ K Kc raw prep' maximum σ x y := by
  simp only [correctionRequest, dite_eq_left hr, CorrectionRowRecipe.normalized]
  rw [normalizer_full D ident r hr prep, normalizer_full D ident r hr prep', hm]

/-- Factor the completed pilot multiplier out of the actual request, keeping the original
raw ranks, incoming gate, usage mask and source/usage preparatory mean. -/
lemma correctionRequest_multiplier {k : ℕ}
    (D : ZMod P) (ident : V → ZMod P)
    (r : HierarchyTask.Request k (Fin J) (ZMod P))
    (I : ℝ → ℝ → ℝ) (τ ρ Q γ : ℝ → ℝ) (K Kc : ℕ)
    (raw prep : Environment P J → Matrix V V ℝ)
    (maximum : Environment P J → V → ℝ) (σ : Environment P J) (x y : V) :
    correctionRequest D ident r I τ ρ Q γ K Kc raw prep maximum σ x y =
      correctionRequest D ident r I τ ρ Q (fun _ => 1) K Kc raw prep
        (fun _ _ => 0) σ x y * γ (maximum σ y) := by
  unfold correctionRequest
  split_ifs
  · simp only [CorrectionRowRecipe.normalized]
    split_ifs <;> simp
  · simp

private lemma unitMultiplier_range {k : ℕ}
    (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (D : ZMod P) (ident : V → ZMod P)
    (r : HierarchyTask.Request k (Fin J) (ZMod P)) (Kc : ℕ)
    (raw prep : Environment P J → Matrix V V ℝ) (σ : Environment P J) (x y : V) :
    correctionRequest D ident r (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ
      HP.toHierarchyParams.atomCutoff (fun _ => 1) HP.K Kc raw prep (fun _ _ => 0) σ x y ∈
      Set.Icc 0 (2 * HP.Q HP.toHierarchyParams.atomCap) := by
  unfold correctionRequest
  split_ifs
  · exact CorrectionRowRecipe.normalized_mem_Icc _ _ _ _ _ _ _ _ _ _ _
      (HP.Q_nonneg _) HP.toHierarchyParams.atomCutoff_nonneg
      HP.toHierarchyParams.atomCutoff_le HP.ρ_nonneg HP.ρ_le_one
      HP.incomingCutoff_nonneg HP.incomingCutoff_le_one
      (fun _ => by norm_num) (fun _ => le_rfl) _ _ _ _ _ _
  · exact ⟨le_rfl, mul_nonneg (by norm_num) (HP.Q_nonneg _)⟩

/-- The actual correction request stays bounded for arbitrary computed children,
including inadmissible requests (which return zero). No accuracy premise is needed. -/
theorem correctionRequest_mem_Icc {k : ℕ}
    (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (D : ZMod P) (ident : V → ZMod P)
    (r : HierarchyTask.Request k (Fin J) (ZMod P)) (Kc : ℕ)
    (raw prep : Environment P J → Matrix V V ℝ)
    (maximum : Environment P J → V → ℝ) (σ : Environment P J) (x y : V) :
    correctionRequest D ident r (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ
      HP.toHierarchyParams.atomCutoff HP.γ HP.K Kc raw prep maximum σ x y ∈
      Set.Icc 0 (2 * HP.Q HP.toHierarchyParams.atomCap) := by
  rw [correctionRequest_multiplier]
  have h := unitMultiplier_range HP D ident r Kc raw prep σ x y
  exact ⟨mul_nonneg h.1 (HP.γ_nonneg _),
    (mul_le_mul_of_nonneg_left (HP.γ_le_one _) h.1).trans (by simpa using h.2)⟩

/-- Uniform fourth-root sensitivity to the completed pilot maximum. Only that child
changes; this is not a raw/preparation stability theorem or a recursive accuracy claim. -/
theorem correctionRequest_maximum_root_stability
    (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ∃ Lγ : ℝ, 0 ≤ Lγ ∧
    ∀ (P J : ℕ) [Fact P.Prime] (V : Type*) [Fintype V] (k : ℕ)
      (D : ZMod P) (ident : V → ZMod P)
      (r : HierarchyTask.Request k (Fin J) (ZMod P)) (Kc : ℕ)
      (raw prep : Environment P J → Matrix V V ℝ)
      (maximum maximum' : Environment P J → V → ℝ)
      (σ : Environment P J) (x y : V),
    |correctionRequest D ident r (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ
        HP.toHierarchyParams.atomCutoff HP.γ HP.K Kc raw prep maximum σ x y ^ (4⁻¹ : ℝ) -
      correctionRequest D ident r (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ
        HP.toHierarchyParams.atomCutoff HP.γ HP.K Kc raw prep maximum' σ x y ^ (4⁻¹ : ℝ)| ≤
      (2 * HP.Q HP.toHierarchyParams.atomCap) ^ (4⁻¹ : ℝ) * Lγ *
        |maximum σ y - maximum' σ y| := by
  obtain ⟨⟨Lγ, hγ⟩, _⟩ := HP.cutoff_roots HP.γ (by simp)
  refine ⟨Lγ, Lγ.coe_nonneg, ?_⟩
  intro P J inst V instV k D ident r Kc raw prep maximum maximum' σ x y
  rw [correctionRequest_multiplier D ident r (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff
    HP.ρ HP.toHierarchyParams.atomCutoff HP.γ HP.K Kc raw prep maximum,
    correctionRequest_multiplier D ident r (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff
      HP.ρ HP.toHierarchyParams.atomCutoff HP.γ HP.K Kc raw prep maximum']
  let b := correctionRequest D ident r (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ
    HP.toHierarchyParams.atomCutoff (fun _ => 1) HP.K Kc raw prep (fun _ _ => 0) σ x y
  have hb := unitMultiplier_range HP D ident r Kc raw prep σ x y
  change b ∈ Set.Icc 0 (2 * HP.Q HP.toHierarchyParams.atomCap) at hb
  rw [Real.mul_rpow hb.1 (HP.γ_nonneg _), Real.mul_rpow hb.1 (HP.γ_nonneg _),
    ← mul_sub, abs_mul, abs_of_nonneg (Real.rpow_nonneg hb.1 _)]
  have hroot := Real.rpow_le_rpow hb.1 hb.2 (by norm_num : (0 : ℝ) ≤ 4⁻¹)
  have hdist := hγ.dist_le_mul (maximum σ y) (maximum' σ y)
  simp only [Real.dist_eq] at hdist
  exact (mul_le_mul hroot hdist (abs_nonneg _)
    (Real.rpow_nonneg (mul_nonneg (by norm_num) (HP.Q_nonneg _)) _)).trans_eq (by ring)

set_option backward.isDefEq.respectTransparency false in
/-- Integrated actual-request root error from the pilot-maximum error on the same pairs.
No source release, independence, or change of environment is implicit in this estimate. -/
theorem correctionRequest_maximum_root_moment
    (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ∃ Lγ : ℝ, 0 ≤ Lγ ∧
    ∀ (P J : ℕ) [Fact P.Prime] (V : Type*) [Fintype V] (k : ℕ)
      (D : ZMod P) (ident : V → ZMod P)
      (r : HierarchyTask.Request k (Fin J) (ZMod P)) (Kc : ℕ)
      (raw prep : Environment P J → Matrix V V ℝ)
      (maximum maximum' : Environment P J → V → ℝ) (N u : ℝ), 0 ≤ N * u →
    rootDistPow 4 N u
      (fun σ x => r.source.retains (channels D) σ (ident x))
      (fun σ y => r.terminal.retains (channels D) σ (ident y))
      (correctionRequest D ident r (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ
        HP.toHierarchyParams.atomCutoff HP.γ HP.K Kc raw prep maximum)
      (correctionRequest D ident r (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ
        HP.toHierarchyParams.atomCutoff HP.γ HP.K Kc raw prep maximum') ≤
    ((2 * HP.Q HP.toHierarchyParams.atomCap) ^ (4⁻¹ : ℝ) * Lγ) ^ 4 *
      rowNormPow 4 N u
        (fun σ x => r.source.retains (channels D) σ (ident x))
        (fun σ y => r.terminal.retains (channels D) σ (ident y))
        (fun σ _ y => maximum σ y - maximum' σ y) := by
  obtain ⟨Lγ, hLγ, hdist⟩ := correctionRequest_maximum_root_stability HP
  refine ⟨Lγ, hLγ, ?_⟩
  intro P J inst V instV k D ident r Kc raw prep maximum maximum' N u hNu
  apply rowNormPow_le_mul hNu
  intro σ x y _ _
  simpa only [Nat.cast_ofNat, mul_pow] using pow_le_pow_left₀ (abs_nonneg _)
    (hdist P J V k D ident r Kc raw prep maximum maximum' σ x y) 4

end Matrix.HierarchyParams.H4RankEnvironment
