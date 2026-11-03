/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyCorrectionMean

/-!
# Correction sampling with a separate source rate

The true source channel uses the terminal stage rate. The actual inherited source can
be narrower, and the usage channel can have any grid rate. Both genuine raw input and
final pilot use the true stage channels; preparation and normalization use the actual
conditioning source. Every spectator coordinate is retained in the single environment split.

This is an original specialization of the existing correction sampling laws, by Christian
Reitwiessner, retaining Samuel Schlesinger's hierarchy construction. It does not establish
arbitrary coarser-source rates, recursive estimator induction or native derandomization.
-/

public section
open Finset Cslib Cslib.Probability
open scoped BigOperators
noncomputable section

namespace Matrix.HierarchyParams.H4RankEnvironment
attribute [local instance] Classical.propDecidable
variable {P J : ℕ} [Fact P.Prime] {V : Type} [Fintype V]
  (HP : FourthRootHierarchyParams 16 1 16 32 8) (D : ZMod P) (ident : V → ZMod P)
  {n : ℕ} (r : HierarchyTask.Request n (Fin J) (ZMod P)) (hr : Admissible r)

/-- True source at the stage rate, with the inherited role and copy suffix unchanged. -/
@[expose] def stageSource (rest : Spectators P J r.terminal.role) (v : V) : Prop :=
  coordinate D {r.source with rate := r.terminal.rate}
    (rest ⟨r.source.role, hr.1⟩) (ident v)

/-- Genuine correction input formed with the true stage source, independently of sampling. -/
@[expose] def stageRaw (C : Matrix V V ℝ) (i : ℕ) : Matrix V V ℝ :=
  HP.toHierarchyParams.correctionInput (stageSource D ident r hr) (splitTerminal D ident r)
    r.terminal.rate C i

/-- Genuine final pilot formed with the true stage channels. -/
@[expose] def stageMaximum (C : Matrix V V ℝ) : V → ℝ :=
  PilotTask.value HP.toHierarchyParams (stageSource D ident r hr) (splitTerminal D ident r)
    r.terminal.rate C (.maximum HP.k)

/-- Genuine preparation uses the actual sampling source for its incoming gate. -/
@[expose] def sourcePreparation (C : Matrix V V ℝ) (i : ℕ)
    (σ : Environment P J) : Matrix V V ℝ :=
  CorrectionRowRecipe.preparation (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff
    (polynomialPrepCutoff4 HP.θ) HP.ρ HP.K ⌈4 * (1 + 32 * HP.R)⌉₊ r.terminal.rate
    (splitSource D ident r hr) (splitTerminal D ident r)
    (stageRaw HP D ident r hr C i) (terminalSplit r.terminal.role σ)

omit [Fintype V] in
/-- True stage channel laws are independent of the actual sampling-source rate. -/
theorem stage_channels (hD : D ≠ 0) (hid : Function.Injective ident)
    (H : Horizon P) {k : ℕ} (hk : k ≤ H.maxExponent)
    (ht : r.terminal.rate = rate k) :
    RetentionChannels (stageSource D ident r hr) (splitTerminal D ident r)
      (rate k) (((side P k : ℝ)/P)^4) 1 16 32 8 ∧
    RetentionChannels (splitTerminal D ident r) (stageSource D ident r hr)
      (rate k) (((side P k : ℝ)/P)^4) 1 16 32 8 := by
  convert split_channels D ident {r with source := {r.source with rate := r.terminal.rate}}
    hr hD hid H hk ht ht using 1 <;> rfl

omit [Fintype V] in
/-- Actual source frame counts at its own rate. No true source is replaced here. -/
theorem source_pair_count (hD : D ≠ 0) (hid : Function.Injective ident)
    (H : Horizon P) {s : ℕ} (hsH : s ≤ H.maxExponent)
    (hs : r.source.rate = rate s) (x w : V) (hw : w ≠ x) :
    (#{a | splitSource D ident r hr a x ∧ splitSource D ident r hr a w} : ℝ) ≤
      32 * rate s * #{a | splitSource D ident r hr a x} := by
  have hh := split_channels D ident {r with terminal := {r.terminal with rate := r.source.rate}}
    hr hD hid H hsH hs hs
  apply card_filter_and_le_of_dens_le
  convert hh.2.pair w x hw using 1 <;> congr 1

omit [Fintype V] in
/-- Positive actual source density, without identifying it with the true stage rate. -/
theorem source_nonempty (hD : D ≠ 0) (hid : Function.Injective ident)
    (H : Horizon P) {s : ℕ} (hsH : s ≤ H.maxExponent)
    (hs : r.source.rate = rate s) (x : V) :
    ({a | splitSource D ident r hr a x} : Finset _).Nonempty := by
  convert split_source_nonempty D ident
    {r with terminal := {r.terminal with rate := r.source.rate}}
    hr hD hid H hsH hs hs x using 1
  congr 1

/-- The bounded computational cutoff preserves the genuine stage input. This entry bound
uses the true recurrence, independently of the actual sampling-source rate. -/
theorem stage_atomCutoff_eq {C : Matrix V V ℝ} {i : ℕ}
    (hf : 0 < r.terminal.rate) (hC : ∀ x y, 0 ≤ C x y) (hC1 : C *ᵥ 1 ≤ 1)
    (hCf : ∀ x y, C x y ≤ r.terminal.rate) (hi : i ≤ HP.k) (x y : V) :
    HP.toHierarchyParams.atomCutoff (stageRaw HP D ident r hr C i x y / r.terminal.rate) =
      HP.Q (stageRaw HP D ident r hr C i x y / r.terminal.rate) := by
  have hb := HP.toHierarchyParams.correctionInput_bounds
    (X := stageSource D ident r hr) (Y := splitTerminal D ident r) hf hC hC1 hCf i
  apply HP.toHierarchyParams.atomCutoff_eq (div_nonneg (hb.1 x y) hf.le)
  apply (div_le_iff₀ hf).mpr
  exact (hb.2.2 x y).trans (mul_le_mul_of_nonneg_right
    (by exact_mod_cast Nat.add_le_add_right hi 1) hf.le)

/-- In particular, clipping preserves genuine nonvanishing, rather than defining a new target. -/
theorem stage_atomCutoff_ne_zero_iff {C : Matrix V V ℝ} {i : ℕ}
    (hf : 0 < r.terminal.rate) (hC : ∀ x y, 0 ≤ C x y) (hC1 : C *ᵥ 1 ≤ 1)
    (hCf : ∀ x y, C x y ≤ r.terminal.rate) (hi : i ≤ HP.k) (x y : V) :
    HP.toHierarchyParams.atomCutoff (stageRaw HP D ident r hr C i x y / r.terminal.rate) ≠ 0 ↔
      HP.Q (stageRaw HP D ident r hr C i x y / r.terminal.rate) ≠ 0 := by
  rw [stage_atomCutoff_eq HP D ident r hr hf hC hC1 hCf hi]

/-- The preparatory normalizer is the actual single-environment joint source/usage mean.
It has no importance factor and does not average over a second full environment. -/
theorem source_normalizer (C : Matrix V V ℝ) (i : ℕ) (x y : V) :
    CorrectionRowRecipe.normalizer (splitSource D ident r hr) (splitUsage D ident r)
      (fun p => sourcePreparation HP D ident r hr C i
        ((terminalSplit r.terminal.role).symm p)) x y =
    rowSliceMean (fun σ v => r.source.retains (channels D) σ (ident v))
      (fun σ v => r.usage.retains (channels D) σ (ident v))
      (sourcePreparation HP D ident r hr C i) x y := by
  convert normalizer_full D ident r hr (sourcePreparation HP D ident r hr C i) x y using 1
  rfl

/-- Pointwise actual request identity with true stage children and actual conditioning.
The preparatory denominator is its joint actual source/usage mean. -/
theorem source_request_eq (C : Matrix V V ℝ) (i : ℕ)
    (σ : Environment P J) (x y : V) :
    correctionRequest D ident r (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ
      HP.toHierarchyParams.atomCutoff HP.γ HP.K ⌈4 * (1 + 32 * HP.R)⌉₊
      (fun _ => stageRaw HP D ident r hr C i) (sourcePreparation HP D ident r hr C i)
      (fun _ => stageMaximum HP D ident r hr C) σ x y =
    CorrectionRowRecipe.normalized (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ
      HP.toHierarchyParams.atomCutoff HP.γ HP.K ⌈4 * (1 + 32 * HP.R)⌉₊ r.terminal.rate
      (splitSource D ident r hr) (splitTerminal D ident r) (splitUsage D ident r)
      (stageRaw HP D ident r hr C i)
      (CorrectionRowRecipe.preparation (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff
        (polynomialPrepCutoff4 HP.θ) HP.ρ HP.K ⌈4 * (1 + 32 * HP.R)⌉₊ r.terminal.rate
        (splitSource D ident r hr) (splitTerminal D ident r) (stageRaw HP D ident r hr C i))
      (stageMaximum HP D ident r hr C) (terminalSplit r.terminal.role σ) x y := by
  exact correctionRequest_eq_split HP D ident r hr _ _ _ σ x y

/-- Honest incoming cost at an arbitrary sampling-source rate: relative to the true stage
budget it grows by fs/ft. A coarser source therefore needs additional rank margin before
this generic argument can establish its mean with the fixed selected incoming rank. -/
theorem source_incoming_cost_le (hD : D ≠ 0) (hid : Function.Injective ident)
    (H : Horizon P) {k s : ℕ} (hk : k ≤ H.maxExponent)
    (hs : r.source.rate = rate s) (ht : r.terminal.rate = rate k)
    {C : Matrix V V ℝ} (hC : ∀ x y, 0 ≤ C x y) (hC1 : C *ᵥ 1 ≤ 1)
    {i : ℕ} (hi : i < HP.k) {y : V}
    (hg : HP.γ (stageMaximum HP D ident r hr C y) ≠ 0) :
    32 * r.source.rate *
        (#({w | HP.δ₁ < stageRaw HP D ident r hr C i w y / r.terminal.rate} : Finset V) : ℝ) ≤
      32 * HP.R * (r.source.rate / r.terminal.rate) := by
  have hh := stage_channels D ident r hr hD hid H hk ht
  rw [← ht] at hh
  have hf : 0 < r.terminal.rate := ht ▸ rate_pos k
  have hs0 : 0 ≤ r.source.rate := (hs ▸ rate_pos s).le
  have hg' : HP.γ (HP.toHierarchyParams.pilot
      (stageSource D ident r hr) (splitTerminal D ident r) r.terminal.rate C y) ≠ 0 := by
    simpa only [stageMaximum, PilotTask.value_maximum_last] using hg
  have hc := HP.toHierarchyParams.correctionInput_count_le
    (stageSource D ident r hr) (splitTerminal D ident r) hh.1 hf
    (by norm_num) (by norm_num) hC hC1 hi hg'
  have hsub : ({w | HP.δ₁ < stageRaw HP D ident r hr C i w y / r.terminal.rate} : Finset V) ⊆
      ({w | HP.δ₁ * r.terminal.rate ≤ stageRaw HP D ident r hr C i w y} : Finset V) := by
    intro w hw
    simp only [mem_filter, mem_univ, true_and] at hw ⊢
    exact ((lt_div_iff₀ hf).mp hw).le
  have hn : (#({w | HP.δ₁ < stageRaw HP D ident r hr C i w y / r.terminal.rate} : Finset V) : ℝ)
      ≤ HP.R / r.terminal.rate := by
    have hcard : (#({w | HP.δ₁ < stageRaw HP D ident r hr C i w y / r.terminal.rate} :
        Finset V) : ℝ) ≤
        #({w | HP.δ₁ * r.terminal.rate ≤ stageRaw HP D ident r hr C i w y} : Finset V) := by
      exact_mod_cast card_le_card hsub
    exact hcard.trans hc
  calc
    _ ≤ 32 * r.source.rate * (HP.R / r.terminal.rate) :=
      mul_le_mul_of_nonneg_left hn (mul_nonneg (by norm_num) hs0)
    _ = _ := by ring

/-- The actual single-Ω mean equals the existing true-stage correction recurrence.
A narrower sampling source fits the unchanged incoming budget. Its own exponent is
within the frame horizon; usage needs only a positive box side and may have any exponent. -/
theorem source_request_mean (hD : D ≠ 0) (hid : Function.Injective ident)
    (H : Horizon P) {k s u : ℕ} (hsH : s ≤ H.maxExponent) (hks : k ≤ s)
    (hs : r.source.rate = rate s) (ht : r.terminal.rate = rate k)
    (hu : r.usage.rate = rate u)
    (C : Matrix V V ℝ) (hC : ∀ x y, 0 ≤ C x y) (hC1 : C *ᵥ 1 ≤ 1)
    (hCf : ∀ x y, C x y ≤ r.terminal.rate) {i : ℕ} (hi : i < HP.k) (x y : V) :
    (𝔼 σ ∈ ({σ | r.source.retains (channels D) σ (ident x)} : Finset _),
      (r.terminal.rate / (dens {σ : Environment P J |
        r.usage.retains (channels D) σ (ident y)} : ℝ)) *
        correctionRequest D ident r (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ
          HP.toHierarchyParams.atomCutoff HP.γ HP.K ⌈4 * (1 + 32 * HP.R)⌉₊
          (fun _ => stageRaw HP D ident r hr C i) (sourcePreparation HP D ident r hr C i)
          (fun _ => stageMaximum HP D ident r hr C) σ x y) =
      HP.toHierarchyParams.correctionIter (stageSource D ident r hr) (splitTerminal D ident r)
        r.terminal.rate C (i + 1) x y := by
  have hk := hks.trans hsH
  have hh := stage_channels D ident r hr hD hid H hk ht
  rw [← ht] at hh
  have hf : 0 < r.terminal.rate := ht ▸ rate_pos k
  have hπ : 0 < (((side P k : ℝ)/P)^4) := by linarith [hh.1.lower]
  have huπ : 0 < (((side P u : ℝ)/P)^4) := by
    have : (0 : ℝ) < P := by exact_mod_cast (Fact.out : P.Prime).pos
    have : (0 : ℝ) < side P u := by
      exact_mod_cast side_pos P u (Fact.out : P.Prime).pos
    positivity
  let A := HP.correctionSampling (stageSource D ident r hr) (splitTerminal D ident r)
    hh.1 hh.2 hf hπ hC hC1 hi
  have hp : ∀ x w, w ≠ x →
      (#{a | splitSource D ident r hr a x ∧ splitSource D ident r hr a w} : ℝ) ≤
        A.p * #{a | splitSource D ident r hr a x} := by
    rw [show A.p = 32 * r.terminal.rate from
      HP.selected_p _ _ hh.1 hh.2 hf hπ hC hC1 hi]
    intro x w hw
    exact (source_pair_count D ident r hr hD hid H hsH hs x w hw).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (ht ▸ rate_antitone hks) (by norm_num)) (by positivity))
  let B := A.withSource (splitSource D ident r hr) hp
  have htP : ∀ z w, w ≠ z →
      (#{t | splitUsage D ident r t z ∧ splitTerminal D ident r t w} : ℝ) ≤
        B.c * r.terminal.rate * #{t | splitUsage D ident r t z} := by
    change ∀ z w, w ≠ z → _ ≤ A.c * r.terminal.rate * _
    rw [show A.c = 32 from HP.selected_c _ _ hh.1 hh.2 hf hπ hC hC1 hi]
    exact split_usage_pair D ident r hr hD hid H hk ht hu
  let T := B.withUsage (splitUsage D ident r) _ huπ
    (split_usage_density D ident r hu) htP
  have hm := T.expect_normalizedRecipe hf hC hC1 hCf hi.le
    (source_nonempty D ident r hr hD hid H hsH hs x) y
  unfold HierarchyParams.CorrectionSampling.normalizedRecipe
    HierarchyParams.CorrectionSampling.preparationRecipe at hm
  rw [channel_density D r.usage u hu, source_expect_split D ident r hr]
  simp_rw [source_request_eq HP D ident r hr C i, Equiv.apply_symm_apply]
  simpa only [T, B, HierarchyParams.CorrectionSampling.withUsage_π,
    HierarchyParams.CorrectionSampling.withUsage_I,
    HierarchyParams.CorrectionSampling.withUsage_τ,
    HierarchyParams.CorrectionSampling.withUsage_h,
    HierarchyParams.CorrectionSampling.withUsage_ρ,
    HierarchyParams.CorrectionSampling.withUsage_K,
    HierarchyParams.CorrectionSampling.withUsage_Kc,
    HierarchyParams.CorrectionSampling.withSource,
    A, FourthRootHierarchyParams.selected_I, FourthRootHierarchyParams.selected_τ,
    FourthRootHierarchyParams.selected_h, FourthRootHierarchyParams.selected_ρ,
    FourthRootHierarchyParams.selected_K, FourthRootHierarchyParams.selected_Kc,
    stageRaw, stageMaximum] using hm

end Matrix.HierarchyParams.H4RankEnvironment
