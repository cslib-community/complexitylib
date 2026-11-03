/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyRankCutoffs
/-!
# Genuine same-rate correction means on one H4 environment

The exact terminal split transports the source-conditioned uniform measure to all spectator
frames times the terminal frame. The target is the existing correction iterate on these
transported channels, with the genuine raw, preparation and final pilot children.
The mean requires equal source, terminal and usage grid rates, nonzero padding, injective
identifiers, an admissible finite horizon and nonnegative substochastic C bounded by the rate.
It does not assemble the entire recursive hierarchy or prove mixed-rate means.

The selected hierarchy construction/proofs are Samuel Schlesinger's; the split transport
and concrete request specialization are Christian Reitwiessner's original work. -/
public section
namespace Matrix.HierarchyParams.H4RankEnvironment
open Finset Cslib Cslib.Probability Matrix Matrix.HierarchyParams
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
variable {P J : ℕ} [Fact P.Prime] {V : Type} [Fintype V]

/-- All spectator frames, including every role other than the terminal. -/
abbrev Spectators (P J : ℕ) (t : Fin J) := {j : Fin J // j ≠ t} → FrameChannel P 4 1

/-- The actual Ω is equivalent to Γ×Ζ, not Ω×Ω. -/
def terminalSplit (t : Fin J) : Environment P J ≃ Spectators P J t × FrameChannel P 4 1 :=
  (Equiv.piSplitAt t (fun _ : Fin J => FrameChannel P 4 1)).trans (Equiv.prodComm _ _)

omit [Fintype V] in
/-- Lift one seed marginal through an arbitrary finite coordinate. This preserves the
entire event distribution, including detector tails and pair events. -/
theorem coordinate_channels {A B R : Type} [Fintype A] [Nonempty A]
    [Fintype B] [Fintype R] [DecidableEq R]
    (j : R) (X : A → V → Prop) (Y : B → V → Prop)
    [∀ a v, Decidable (X a v)] [∀ b v, Decidable (Y b v)]
    {f π : ℝ} (hXY : RetentionChannels X Y f π 1 16 32 8)
    (hYX : RetentionChannels Y X f π 1 16 32 8) :
    RetentionChannels (fun (σ : R → A) v => X (σ j) v) Y f π 1 16 32 8 ∧
      RetentionChannels Y (fun (σ : R → A) v => X (σ j) v) f π 1 16 32 8 := by
  constructor
  · refine ⟨?_, hXY.dens_Y, hXY.lower, hXY.upper, hXY.pair, ?_⟩
    · intro v
      rw [dens_filter_pi_eval j (fun a => X a v)]
      exact hXY.dens_X v
    · intro S hS
      rw [dens_filter_pi_eval j (fun a =>
        2 * (#{v ∈ S | X a v} : ℝ) < #S * π)]
      exact hXY.tail S hS
  · refine ⟨hYX.dens_X, ?_, hYX.lower, hYX.upper, ?_, hYX.tail⟩
    · intro v
      rw [dens_filter_pi_eval j (fun a => X a v)]
      exact hYX.dens_Y v
    · intro w y hwy
      rw [dens_filter_pi_eval j (fun a => X a w ∧ X a y),
        dens_filter_pi_eval j (fun a => X a y)]
      exact hYX.pair w y hwy

variable (HP : FourthRootHierarchyParams 16 1 16 32 8)
  (D : ZMod P) (ident : V → ZMod P)
  {n : ℕ} (r : HierarchyTask.Request n (Fin J) (ZMod P)) (hr : Admissible r)

/-- Inherited source coordinate on Γ, with its actual copy suffix. -/
def splitSource (rest : Spectators P J r.terminal.role) (v : V) : Prop :=
  coordinate D r.source (rest ⟨r.source.role, hr.1⟩) (ident v)

/-- Terminal coordinate on Ζ, with its actual copy suffix. -/
def splitTerminal (A : FrameChannel P 4 1) (v : V) : Prop :=
  coordinate D r.terminal A (ident v)

omit [Fintype V] in
/-- Exact pushforward of source-conditioned uniform Ω to conditioned Γ times all Ζ.
No target or true-mean premise occurs in this finite-measure identity. -/
theorem source_expect_split (F : Environment P J → ℝ) (x : V) :
    (𝔼 σ ∈ ({σ | r.source.retains (channels D) σ (ident x)} : Finset _), F σ) =
      𝔼 p ∈ ({rest | splitSource D ident r hr rest x} : Finset _) ×ˢ
        (univ : Finset (FrameChannel P 4 1)), F ((terminalSplit r.terminal.role).symm p) := by
  apply Finset.expect_equiv (terminalSplit r.terminal.role)
  · intro σ
    simp [terminalSplit, splitSource, coordinate, CorrectionRowTask.Channel.retains, channels]
  · intro σ _
    rw [Equiv.symm_apply_apply]

omit [Fintype V] in
/-- Projected-coordinate frame laws for Γ and Ζ at one common grid rate.
Both padded identifier maps are checked separately. -/
theorem split_channels (hD : D ≠ 0) (hid : Function.Injective ident)
    (H : Horizon P) {k : ℕ} (hk : k ≤ H.maxExponent)
    (hs : r.source.rate = rate k) (ht : r.terminal.rate = rate k) :
    RetentionChannels (splitSource D ident r hr) (splitTerminal D ident r)
      (rate k) (((side P k : ℝ)/P)^4) 1 16 32 8 ∧
    RetentionChannels (splitTerminal D ident r) (splitSource D ident r hr)
      (rate k) (((side P k : ℝ)/P)^4) 1 16 32 8 := by
  let is := fun v => CopyPadding.identifier D r.source.suffix (ident v)
  let it := fun v => CopyPadding.identifier D r.terminal.suffix (ident v)
  have ha : ((2 : ℝ) ^ k)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have hS := retentionChannels_frameRetains_of_lt
    ((CopyPadding.identifier_injective hD r.source.suffix).comp hid)
    (H := 4) (r := 1) (by decide) (by decide) (horizon_admissible H hk) ha
  have hT := retentionChannels_frameRetains_of_lt
    ((CopyPadding.identifier_injective hD r.terminal.suffix).comp hid)
    (H := 4) (r := 1) (by decide) (by decide) (horizon_admissible H hk) ha
  have hST : RetentionChannels
      (fun (A : FrameChannel P 4 1) v => frameRetains P 4 (side P k) A (is v))
      (fun (A : FrameChannel P 4 1) v => frameRetains P 4 (side P k) A (it v))
      (rate k) (((side P k : ℝ)/P)^4) 1 16 32 8 := by
    norm_num only [← side_eq_ceil] at hS hT
    exact ⟨hS.dens_X, hT.dens_Y, hS.lower, hS.upper, hT.pair, hS.tail⟩
  have hTS : RetentionChannels
      (fun (A : FrameChannel P 4 1) v => frameRetains P 4 (side P k) A (it v))
      (fun (A : FrameChannel P 4 1) v => frameRetains P 4 (side P k) A (is v))
      (rate k) (((side P k : ℝ)/P)^4) 1 16 32 8 := by
    norm_num only [← side_eq_ceil] at hS hT
    exact ⟨hT.dens_X, hS.dens_Y, hT.lower, hT.upper, hS.pair, hT.tail⟩
  unfold splitSource splitTerminal coordinate
  simp only [hs, ht, semanticSide_grid]
  exact coordinate_channels (⟨r.source.role, hr.1⟩ : {j : Fin J // j ≠ r.terminal.role})
      _ _ hST hTS

/-- Genuine earlier raw child C+E_i C in matrix units, using the actual split channels. -/
def genuineRaw (C : Matrix V V ℝ) (i : ℕ) : Matrix V V ℝ :=
  HP.toHierarchyParams.correctionInput (splitSource D ident r hr) (splitTerminal D ident r)
    r.terminal.rate C i

/-- Genuine preparation child pulled back from Γ×Ζ to the single Ω. -/
def genuinePrep (C : Matrix V V ℝ) (i : ℕ) (σ : Environment P J) : Matrix V V ℝ :=
  CorrectionRowRecipe.preparation (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff
    (polynomialPrepCutoff4 HP.θ) HP.ρ HP.K ⌈4 * (1 + 32 * HP.R)⌉₊ r.terminal.rate
    (splitSource D ident r hr) (splitTerminal D ident r)
    (genuineRaw HP D ident r hr C i) (terminalSplit r.terminal.role σ)

/-- The final genuine pilot maximum, not an arbitrary multiplier callback. -/
def genuineMaximum (C : Matrix V V ℝ) : V → ℝ :=
  PilotTask.value HP.toHierarchyParams (splitSource D ident r hr) (splitTerminal D ident r)
    r.terminal.rate C (.maximum HP.k)

/-- Pointwise actual-request identification, including the exact split, padding and usage.
Only equal terminal/usage rates are required for this identity; source can be narrower. -/
theorem genuine_request_eq (hu : r.usage.rate = r.terminal.rate)
    (C : Matrix V V ℝ) (i : ℕ) (σ : Environment P J) (x y : V) :
    correctionRequest D ident r (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ
      HP.toHierarchyParams.atomCutoff HP.γ HP.K ⌈4 * (1 + 32 * HP.R)⌉₊
      (fun _ => genuineRaw HP D ident r hr C i) (genuinePrep HP D ident r hr C i)
      (fun _ => genuineMaximum HP D ident r hr C) σ x y =
    CorrectionRowRecipe.normalized (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ
      HP.toHierarchyParams.atomCutoff HP.γ HP.K ⌈4 * (1 + 32 * HP.R)⌉₊ r.terminal.rate
      (splitSource D ident r hr) (splitTerminal D ident r) (splitTerminal D ident r)
      (genuineRaw HP D ident r hr C i)
      (CorrectionRowRecipe.preparation (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff
        (polynomialPrepCutoff4 HP.θ) HP.ρ HP.K ⌈4 * (1 + 32 * HP.R)⌉₊ r.terminal.rate
        (splitSource D ident r hr) (splitTerminal D ident r) (genuineRaw HP D ident r hr C i))
      (genuineMaximum HP D ident r hr C) (terminalSplit r.terminal.role σ) x y := by
  simp only [correctionRequest, dite_eq_left hr]
  have husage : (fun A v => coordinate D r.usage A (ident v)) = splitTerminal D ident r := by
    funext A v
    simp only [coordinate, splitTerminal, hu, hr.2.2]
  simp only [husage]
  have hprep : (fun p => genuinePrep HP D ident r hr C i
      ((Equiv.piSplitAt r.terminal.role (fun _ : Fin J => FrameChannel P 4 1)).symm (p.2, p.1))) =
      CorrectionRowRecipe.preparation (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff
        (polynomialPrepCutoff4 HP.θ) HP.ρ HP.K ⌈4 * (1 + 32 * HP.R)⌉₊ r.terminal.rate
        (splitSource D ident r hr) (splitTerminal D ident r) (genuineRaw HP D ident r hr C i) := by
    funext p
    simp [genuinePrep, terminalSplit]
  rw [hprep]
  rfl

/-- Same-rate genuine actual correction requests have the true correction-iterate mean
on ONE environment. The incoming count and normalizer laws come from the frame channel
constructor. No target mean is assumed. Mixed source/rank rates or narrower usage are not
covered by the present ofChannels constructor. -/
theorem genuine_request_mean (hD : D ≠ 0) (hid : Function.Injective ident)
    (H : Horizon P) {k : ℕ} (hk : k ≤ H.maxExponent)
    (hs : r.source.rate = rate k) (ht : r.terminal.rate = rate k)
    (hu : r.usage.rate = r.terminal.rate)
    (C : Matrix V V ℝ) (hC : ∀ x y, 0 ≤ C x y) (hC1 : C *ᵥ 1 ≤ 1)
    (hCf : ∀ x y, C x y ≤ r.terminal.rate) {i : ℕ} (hi : i < HP.k)
    {x : V} (hx : ({rest | splitSource D ident r hr rest x} : Finset _).Nonempty) (y : V) :
    (𝔼 σ ∈ ({σ | r.source.retains (channels D) σ (ident x)} : Finset _),
      (r.terminal.rate / (((side P k : ℝ)/P)^4)) *
        correctionRequest D ident r (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ
          HP.toHierarchyParams.atomCutoff HP.γ HP.K ⌈4 * (1 + 32 * HP.R)⌉₊
          (fun _ => genuineRaw HP D ident r hr C i) (genuinePrep HP D ident r hr C i)
          (fun _ => genuineMaximum HP D ident r hr C) σ x y) =
      HP.toHierarchyParams.correctionIter (splitSource D ident r hr) (splitTerminal D ident r)
        r.terminal.rate C (i + 1) x y := by
  have hh := split_channels D ident r hr hD hid H hk hs ht
  rw [← ht] at hh
  have hf : 0 < r.terminal.rate := ht ▸ rate_pos k
  have hπ : 0 < (((side P k : ℝ)/P)^4) := by
    have h := hh.1.lower
    linarith
  rw [source_expect_split D ident r hr]
  simp_rw [genuine_request_eq HP D ident r hr hu C i, Equiv.apply_symm_apply]
  have hm := HP.correction_mean (splitSource D ident r hr) (splitTerminal D ident r)
    hh.1 hh.2 hf hπ hC hC1 hi hCf hx y
  dsimp only at hm
  rw [HP.selected_pi, HP.selected_normalized, HP.selected_preparation] at hm
  exact hm

omit [Fintype V] in
/-- Positivity of the frame marginal supplies an inhabited actual source slice. -/
theorem split_source_nonempty (hD : D ≠ 0) (hid : Function.Injective ident)
    (H : Horizon P) {k : ℕ} (hk : k ≤ H.maxExponent)
    (hs : r.source.rate = rate k) (ht : r.terminal.rate = rate k) (x : V) :
    ({rest | splitSource D ident r hr rest x} : Finset _).Nonempty := by
  have hh := split_channels D ident r hr hD hid H hk hs ht
  have hp : 0 < (((side P k : ℝ)/P)^4) := by
    have h := hh.1.lower
    have hf := rate_pos k
    linarith
  have hd := hh.1.dens_X x
  have hd' : 0 < (dens {rest | splitSource D ident r hr rest x} : ℝ) := by rwa [hd]
  exact Finset.dens_pos.mp (by exact_mod_cast hd')

/-- The scale uses the measured usage density on the actual single Ω, and source
inhabitedness is derived. The mean target is the genuine actual correction recurrence. -/
theorem genuine_request_mean_density (hD : D ≠ 0) (hid : Function.Injective ident)
    (H : Horizon P) {k : ℕ} (hk : k ≤ H.maxExponent)
    (hs : r.source.rate = rate k) (ht : r.terminal.rate = rate k)
    (hu : r.usage.rate = r.terminal.rate)
    (C : Matrix V V ℝ) (hC : ∀ x y, 0 ≤ C x y) (hC1 : C *ᵥ 1 ≤ 1)
    (hCf : ∀ x y, C x y ≤ r.terminal.rate) {i : ℕ} (hi : i < HP.k) (x y : V) :
    (𝔼 σ ∈ ({σ | r.source.retains (channels D) σ (ident x)} : Finset _),
      (r.terminal.rate / (dens {σ : Environment P J |
        r.usage.retains (channels D) σ (ident y)} : ℝ)) *
        correctionRequest D ident r (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ
          HP.toHierarchyParams.atomCutoff HP.γ HP.K ⌈4 * (1 + 32 * HP.R)⌉₊
          (fun _ => genuineRaw HP D ident r hr C i) (genuinePrep HP D ident r hr C i)
          (fun _ => genuineMaximum HP D ident r hr C) σ x y) =
      HP.toHierarchyParams.correctionIter (splitSource D ident r hr) (splitTerminal D ident r)
        r.terminal.rate C (i + 1) x y := by
  rw [channel_density D r.usage k (hu.trans ht)]
  exact genuine_request_mean HP D ident r hr hD hid H hk hs ht hu C hC hC1 hCf hi
    (split_source_nonempty D ident r hr hD hid H hk hs ht x) y

end
end Matrix.HierarchyParams.H4RankEnvironment
