/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: local-only (tests of genuine correction means)

import Complexity.Foundations.Probability.HierarchyCorrectionMean
import ComplexityTests.HierarchyCutoffs

/-! Positive actual single-environment means and nonconstant finite-horizon channels. -/
set_option linter.privateModule false

namespace SingleRegression
open Finset Cslib Cslib.Probability Matrix Matrix.HierarchyParams
    Matrix.HierarchyParams.H4RankEnvironment
open scoped BigOperators
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

variable (HP : FourthRootHierarchyParams 16 1 16 32 8)

def request (k : ℕ) (u : ℕ := k) : HierarchyTask.Request HP.k (Fin 2) (ZMod 5) :=
  ⟨.row 0 (.normalized ⟨0,HP.k_pos⟩), gridChannel 0 k [1],
    gridChannel 1 k [2,3], gridChannel 1 u [2,3]⟩

lemma admissible (k : ℕ) (u : ℕ := k) : Admissible (request HP k u) := by
  exact ⟨by change (0 : Fin 2) ≠ 1; decide, rfl, rfl⟩

def identifier (_ : Unit) : ZMod 5 := 0
lemma identifier_injective : Function.Injective identifier := fun _ _ _ => Subsingleton.elim _ _

lemma one_lt_J : 1 < HP.J := by
  have hk : (1:ℝ) ≤ HP.k := by exact_mod_cast HP.k_pos
  have hm : (1:ℝ) ≤ HP.m := by
    have h := HP.copies_strict
    by_contra hh
    have hm0 : HP.m = 0 := by
      have : HP.m < 1 := by exact_mod_cast (lt_of_not_ge hh)
      omega
    rw [hm0] at h
    norm_num at h
    linarith
  have hprod : 1 ≤ (HP.m:ℝ) * HP.k * ((HP.k:ℝ)+1) :=
    by calc
      1 = (1:ℝ)*1*1 := by norm_num
      _ ≤ (HP.m:ℝ) * HP.k * ((HP.k:ℝ)+1) := by gcongr; linarith
  have hd : HP.δ₀ < 1 := by
    linarith [HP.δ₀_lt_δ₁, HP.δ₁_lt, HP.θ_lt_θ₂, HP.θ₂_lt]
  by_contra hh
  have hj : (HP.J:ℝ) ≤ 1 := by exact_mod_cast (not_lt.mp hh)
  have := HP.rank
  norm_num at this
  nlinarith [mul_le_mul_of_nonneg_left hj HP.δ₀_pos.le]

/-- P=5, H=4, any grid exponent, genuine positive singleton correction target. -/
theorem positive_target (k : ℕ) (u : ℕ := k) :
    0 < HP.toHierarchyParams.correctionIter
      (splitSource 1 identifier (request HP k u) (admissible HP k u))
      (splitTerminal 1 identifier (request HP k u))
      (request HP k u).terminal.rate (fun _ _ => rate k : Matrix Unit Unit ℝ) 1 () () := by
  erw [HP.toHierarchyParams.correctionIter_succ_apply (i := 0)]
  have hmax := PilotTask.value_maximum_eq_zero HP.toHierarchyParams
    (splitSource 1 identifier (request HP k u) (admissible HP k u))
    (splitTerminal 1 identifier (request HP k u))
    (request HP k u).terminal.rate (fun _ _ => rate k)
    (by simpa using one_lt_J HP) HP.k
  erw [PilotTask.value_maximum_last] at hmax
  erw [hmax]
  simp only [Pi.zero_apply, HP.γ_one 0 (by norm_num), mul_one]
  have hraw : HP.toHierarchyParams.correctionInput
      (splitSource 1 identifier (request HP k u) (admissible HP k u))
      (splitTerminal 1 identifier (request HP k u))
      (request HP k u).terminal.rate (fun _ _ => rate k) 0 () () = rate k := by
    change rate k + ∑ _ : Unit, (0:ℝ)*rate k = rate k
    simp
  rw [hraw]
  change 0 < rate k * HP.Q (rate k / rate k)
  rw [div_self (ne_of_gt (rate_pos k))]
  exact mul_pos (rate_pos k) (CutoffRegression.Q_one_pos HP)

/-- Strictly positive mean of the complete actual single-Ω correctionRequest at horizon zero.
Both source and terminal suffixes are nonempty and deliberately different. -/
theorem positive_actual_mean :
    0 < (𝔼 σ ∈ ({σ : Environment 5 2 |
      (request HP 0).source.retains (channels 1) σ (identifier ())} : Finset _),
      ((request HP 0).terminal.rate / (dens {σ : Environment 5 2 |
        (request HP 0).usage.retains (channels 1) σ (identifier ())} : ℝ)) *
      correctionRequest 1 identifier (request HP 0) (polynomialAuxCutoff4 HP.θ)
        HP.incomingCutoff HP.ρ HP.toHierarchyParams.atomCutoff HP.γ HP.K
        ⌈4 * (1 + 32 * HP.R)⌉₊
        (fun _ => genuineRaw HP 1 identifier (request HP 0) (admissible HP 0) (fun _ _ => 1) 0)
        (genuinePrep HP 1 identifier (request HP 0) (admissible HP 0) (fun _ _ => 1) 0)
        (fun _ => genuineMaximum HP 1 identifier (request HP 0) (admissible HP 0) (fun _ _ => 1))
        σ () ()) := by
  rw [genuine_request_mean_density HP 1 identifier (request HP 0) (admissible HP 0)
    (by norm_num) identifier_injective (zeroHorizon (P := 5)) (k := 0) (by decide)
    rfl rfl rfl (fun _ _ => (1:ℝ)) (by intros; norm_num)
    (by intro x; norm_num [Matrix.mulVec, dotProduct])
    (by intros; norm_num [request, gridChannel, rate]) HP.k_pos]
  simpa only [rate, pow_zero, inv_one, one_pow] using positive_target HP 0

/-- A second admissible horizon includes a nonconstant rank channel. -/
def oneHorizon : Horizon 5 := ⟨1,4,by decide,by decide⟩

/-- At k=1 the actual source marginal is 81/625, so neither a full nor an empty slice. -/
theorem nonconstant_density :
    (dens {σ : Environment 5 2 |
      (request HP 1).source.retains (channels 1) σ (identifier ())} : ℝ) = 81/625 := by
  rw [channel_density 1 (request HP 1).source 1 rfl]
  change ((3:ℝ)/5)^4 = 81/625
  norm_num

/-- Both projected channel laws remain instantiated at the nonconstant side-three slice. -/
theorem nonconstant_channels :
    RetentionChannels (splitSource 1 identifier (request HP 1) (admissible HP 1))
      (splitTerminal 1 identifier (request HP 1)) (rate 1) (((side 5 1 : ℝ) / 5) ^ 4) 1 16 32 8 ∧
    RetentionChannels (splitTerminal 1 identifier (request HP 1))
      (splitSource 1 identifier (request HP 1) (admissible HP 1))
      (rate 1) (((side 5 1 : ℝ) / 5) ^ 4) 1 16 32 8 :=
  split_channels 1 identifier (request HP 1) (admissible HP 1)
    (by norm_num) identifier_injective oneHorizon (k := 1) (by decide) rfl rfl

/-- Strictly positive mean of the complete actual single-Ω correctionRequest at the nonconstant
    horizon-one slice.
Both source and terminal suffixes are nonempty and deliberately different. -/
theorem positive_nonconstant_actual_mean :
    0 < (𝔼 σ ∈ ({σ : Environment 5 2 |
      (request HP 1).source.retains (channels 1) σ (identifier ())} : Finset _),
      ((request HP 1).terminal.rate / (dens {σ : Environment 5 2 |
        (request HP 1).usage.retains (channels 1) σ (identifier ())} : ℝ)) *
      correctionRequest 1 identifier (request HP 1) (polynomialAuxCutoff4 HP.θ)
        HP.incomingCutoff HP.ρ HP.toHierarchyParams.atomCutoff HP.γ HP.K
        ⌈4 * (1 + 32 * HP.R)⌉₊
        (fun _ => genuineRaw HP 1 identifier (request HP 1) (admissible HP 1) (fun _ _ => rate 1) 0)
        (genuinePrep HP 1 identifier (request HP 1) (admissible HP 1) (fun _ _ => rate 1) 0)
        (fun _ => genuineMaximum HP 1 identifier (request HP 1) (admissible HP 1)
          (fun _ _ => rate 1))
        σ () ()) := by
  rw [genuine_request_mean_density HP 1 identifier (request HP 1) (admissible HP 1)
    (by norm_num) identifier_injective oneHorizon (k := 1) (by decide)
    rfl rfl rfl (fun _ _ => rate 1) (by intros; norm_num [rate])
    (by intro x; norm_num [Matrix.mulVec, dotProduct, rate])
    (by intros; norm_num [request, gridChannel, rate]) HP.k_pos]
  simpa only [rate, pow_zero, inv_one, one_pow] using positive_target HP 1

/-- A genuine hierarchy witness realizes the positive horizon-one correction target. -/
example : ∃ HP : FourthRootHierarchyParams 16 1 16 32 8,
    0 < HP.toHierarchyParams.correctionIter
      (splitSource 1 identifier (request HP 1) (admissible HP 1))
      (splitTerminal 1 identifier (request HP 1))
      (request HP 1).terminal.rate (fun _ _ => rate 1 : Matrix Unit Unit ℝ) 1 () () := by
  let HP : FourthRootHierarchyParams 16 1 16 32 8 :=
    Classical.choice (FourthRootHierarchyParams.nonempty (by norm_num) (by norm_num))
  exact ⟨HP, positive_target HP 1⟩

/-- Same true source/rank stage, strictly narrower usage, and nonempty copy suffixes. -/
def narrowRequest : HierarchyTask.Request HP.k (Fin 2) (ZMod 5) :=
  request HP 1 2

lemma narrow_admissible : Admissible (narrowRequest HP) :=
  ⟨by change (0 : Fin 2) ≠ 1; decide, rfl, rfl⟩

/-- Both channels are nonconstant, with distinct actual densities. The usage exponent need
not be in the rank horizon: its marginal only needs a positive box side. -/
theorem narrow_densities :
    (dens {σ : Environment 5 2 |
      (narrowRequest HP).source.retains (channels 1) σ (identifier ())} : ℝ) = 81/625 ∧
    (dens {σ : Environment 5 2 |
      (narrowRequest HP).usage.retains (channels 1) σ (identifier ())} : ℝ) = 16/625 ∧
    (narrowRequest HP).usage.rate < (narrowRequest HP).terminal.rate := by
  rw [channel_density 1 (narrowRequest HP).source 1 rfl,
    channel_density 1 (narrowRequest HP).usage 2 rfl]
  norm_num [narrowRequest, request, gridChannel, side, rate, Nat.ceilDiv_eq_add_pred_div]

/-- Complete genuine request with narrower usage has positive mean, with its exact iterate
as target. The pilot is the genuine final maximum, not a supplied zero multiplier. -/
theorem positive_narrow_actual_mean :
    0 < (𝔼 σ ∈ ({σ : Environment 5 2 |
      (narrowRequest HP).source.retains (channels 1) σ (identifier ())} : Finset _),
      ((narrowRequest HP).terminal.rate / (dens {σ : Environment 5 2 |
        (narrowRequest HP).usage.retains (channels 1) σ (identifier ())} : ℝ)) *
      correctionRequest 1 identifier (narrowRequest HP) (polynomialAuxCutoff4 HP.θ)
        HP.incomingCutoff HP.ρ HP.toHierarchyParams.atomCutoff HP.γ HP.K
        ⌈4 * (1 + 32 * HP.R)⌉₊
        (fun _ => genuineRaw HP 1 identifier (narrowRequest HP) (narrow_admissible HP)
          (fun _ _ => rate 1) 0)
        (genuinePrep HP 1 identifier (narrowRequest HP) (narrow_admissible HP)
          (fun _ _ => rate 1) 0)
        (fun _ => genuineMaximum HP 1 identifier (narrowRequest HP) (narrow_admissible HP)
          (fun _ _ => rate 1)) σ () ()) := by
  rw [genuine_request_mean_usage HP 1 identifier (narrowRequest HP) (narrow_admissible HP)
    (by norm_num) identifier_injective oneHorizon (k := 1) (u := 2) (by decide)
    rfl rfl rfl (fun _ _ => rate 1) (by intros; norm_num [rate])
    (by intro x; norm_num [Matrix.mulVec, dotProduct, rate])
    (by intros; norm_num [narrowRequest, request, gridChannel, rate]) HP.k_pos]
  exact positive_target HP 1 2

/-- The full parameter hypotheses of the narrower-usage mean are inhabited. -/
example : ∃ HP : FourthRootHierarchyParams 16 1 16 32 8,
    Admissible (narrowRequest HP) ∧ (narrowRequest HP).usage.rate <
      (narrowRequest HP).terminal.rate := by
  let HP : FourthRootHierarchyParams 16 1 16 32 8 :=
    Classical.choice (FourthRootHierarchyParams.nonempty (by norm_num) (by norm_num))
  exact ⟨HP, narrow_admissible HP, (narrow_densities HP).2.2⟩

end
end SingleRegression
