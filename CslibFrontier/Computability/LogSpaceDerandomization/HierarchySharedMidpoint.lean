/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import CslibFrontier.Computability.LogSpaceDerandomization.HierarchyDenseChildren
public import CslibFrontier.Foundations.Probability.CoordinateFactorization

/-!
# Actual shared-midpoint correction and dense children

The correction reads the old source and midpoint frames; the genuine dense right child
reads only the terminal frame after its joint normalizer is computed. All three roles
belong to one full environment, including free spectators. The original correction
iteration, actual usage factors and midpoint density are retained.

This proves a genuine single-path conditional product mean. `HierarchySignedMean` uses it
to derive the actual signed raw-sample mean and finite bin residual with one special negative
request. Estimated-child perturbation, recursive mean envelopes and native endpoints remain open.

The assembly is original work by Christian Reitwiessner, using Samuel Schlesinger's
hierarchy construction. This does not establish recursive error envelopes or RL=L.
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

/-- The actual genuine correction request, with its true hierarchy raw input and final
pilot, and preparation using the actual (possibly narrower) sampling source. -/
@[expose] def sourceChild (C : Matrix V V ℝ) (i : ℕ)
    (σ : Environment P J) : Matrix V V ℝ :=
  correctionRequest D ident r (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ
    HP.toHierarchyParams.atomCutoff HP.γ HP.K ⌈4 * (1 + 32 * HP.R)⌉₊
    (fun _ => stageRaw HP D ident r hr C i) (sourcePreparation HP D ident r hr C i)
    (fun _ => stageMaximum HP D ident r hr C) σ

/-- A genuine left correction uses its source and midpoint frame, retaining the midpoint
hit, row rank and incoming rank. It cannot read the distinct parent terminal frame. -/
theorem sourceChild_roles (C : Matrix V V ℝ) (i : ℕ)
    (σ τ : Environment P J) (hs : σ r.source.role = τ r.source.role)
    (ht : σ r.terminal.role = τ r.terminal.role) (x z : V) :
    sourceChild HP D ident r hr C i σ x z = sourceChild HP D ident r hr C i τ x z := by
  simp only [sourceChild, correctionRequest, dite_eq_left hr, CorrectionRowRecipe.normalized,
    Equiv.piSplitAt_apply]
  simp only [show (fun w => coordinate D r.source (σ r.source.role) (ident w)) =
      (fun w => coordinate D r.source (τ r.source.role) (ident w)) from by rw [hs], ht]

/-- The actual shared-midpoint product factors on the old source AND terminal event.
The left factor still contains its midpoint hit; the right factor is obtained from the
actual joint dense normalization. Source and midpoint are distinct by `hr`, and both
are distinct from the terminal. Every other role is integrated, not fixed. -/
theorem sourceChild_mul_denseChild_factor
    (d : HierarchyTask.Request n (Fin J) (ZMod P)) (hd : Admissible d)
    (hst : r.source.role ≠ d.terminal.role) (hmt : r.terminal.role ≠ d.terminal.role)
    (C B : Matrix V V ℝ) (i : ℕ) (cutoff h ρ : ℝ → ℝ) (K : ℕ)
    (q : FrameChannel P 4 1 → Prop) [DecidablePred q]
    (x z y : V) (hz : ({a | splitSource D ident d hd a z} : Finset _).Nonempty) :
    (𝔼 σ ∈ ({σ : Environment P J |
      r.source.retains (channels D) σ (ident x) ∧ q (σ d.terminal.role)} : Finset _),
      sourceChild HP D ident r hr C i σ x z *
        denseChild D ident d cutoff h ρ K B σ z y) =
    (𝔼 σ ∈ ({σ : Environment P J |
      r.source.retains (channels D) σ (ident x)} : Finset _),
      sourceChild HP D ident r hr C i σ x z) *
    (𝔼 A ∈ ({A | q A} : Finset _),
      denseAtom (splitTerminal D ident d) (splitUsage D ident d)
        cutoff h ρ K d.terminal.rate B A z y) := by
  let L : Spectators P J d.terminal.role → ℝ := fun rest =>
    sourceChild HP D ident r hr C i
      ((terminalSplit d.terminal.role).symm (rest, Classical.arbitrary _)) x z
  have hL (σ : Environment P J) :
      L (fun j => σ j) = sourceChild HP D ident r hr C i σ x z := by
    apply sourceChild_roles
    · simp [terminalSplit, Equiv.piSplitAt, hst]
    · simp [terminalSplit, Equiv.piSplitAt, hmt]
  simp_rw [denseChild_eq D ident d hd cutoff h ρ K B _ z y hz, ← hL]
  exact expect_pi_split_mul_filter r.source.role d.terminal.role hst
    (fun A => coordinate D r.source A (ident x)) q L
    (fun A => denseAtom (splitTerminal D ident d) (splitUsage D ident d)
      cutoff h ρ K d.terminal.rate B A z y)

/-- Genuine single-path conditional product mean. The literal midpoint density remains
in the left coefficient. The right child resets the entire source tuple to that midpoint;
its actual dense one-child mean supplies the bin value. No child mean is assumed. -/
theorem sourceChild_mul_denseChild_mean
    (d : HierarchyTask.Request n (Fin J) (ZMod P)) (hd : Admissible d)
    (hdsource : d.source = r.terminal) (husage : r.usage = r.terminal)
    (hst : r.source.role ≠ d.terminal.role) (hmt : r.terminal.role ≠ d.terminal.role)
    (hD : D ≠ 0) (hid : Function.Injective ident) (H : Horizon P)
    {k s b u : ℕ} (hsH : s ≤ H.maxExponent) (hks : k ≤ s)
    (hs : r.source.rate = rate s) (ht : r.terminal.rate = rate k)
    (hbH : b ≤ H.maxExponent) (hb : d.terminal.rate = rate b)
    (hu : d.usage.rate = rate u)
    (C : Matrix V V ℝ) (hC : ∀ x y, 0 ≤ C x y) (hC1 : C *ᵥ 1 ≤ 1)
    (hCf : ∀ x y, C x y ≤ r.terminal.rate) {i : ℕ} (hi : i < HP.k)
    (cutoff h ρ : ℝ → ℝ) (K : ℕ)
    (q : FrameChannel P 4 1 → Prop) [DecidablePred q]
    (x z y : V) (hsub : ∀ A, splitUsage D ident d A y → q A)
    (hkh : ∀ v, cutoff v ≠ 0 → h v = 1)
    (hρ0 : ∀ v, 0 ≤ ρ v) (hρ1 : ∀ v, ρ v ≤ 1) {η : ℝ}
    (hη : 0 < η) (hρη : ∀ v, v ≤ η → ρ v = 1)
    (hK : 2 * (1 + 32 / η) ≤ K) :
    (𝔼 σ ∈ ({σ : Environment P J |
      r.source.retains (channels D) σ (ident x) ∧ q (σ d.terminal.role)} : Finset _),
      (r.terminal.rate / (dens {τ : Environment P J |
        r.terminal.retains (channels D) τ (ident y)} : ℝ)) *
        sourceChild HP D ident r hr C i σ x z *
      (d.terminal.rate * ((dens {τ : Environment P J | q (τ d.terminal.role)} : ℝ) /
        dens {τ : Environment P J | d.usage.retains (channels D) τ (ident y)})) *
        denseChild D ident d cutoff h ρ K C σ z y) =
    HP.toHierarchyParams.correctionIter (canonicalChannel ident r.terminal.rate)
      (canonicalChannel ident r.terminal.rate) r.terminal.rate C (i + 1) x z *
        (d.terminal.rate * cutoff (C z y / d.terminal.rate)) := by
  have hz := source_nonempty D ident d hd hD hid H (hks.trans hsH)
    (hdsource ▸ ht) z
  have hleft := source_request_mean_canonical HP D ident r hr hD hid H hsH hks
    hs ht (husage ▸ ht) C hC hC1 hCf hi x z
  change (𝔼 σ ∈ ({σ : Environment P J |
    r.source.retains (channels D) σ (ident x)} : Finset _),
    (r.terminal.rate / (dens {τ : Environment P J |
      r.usage.retains (channels D) τ (ident z)} : ℝ)) *
      sourceChild HP D ident r hr C i σ x z) = _ at hleft
  rw [husage, ← mul_expect] at hleft
  have hmid : (dens {τ : Environment P J |
      r.terminal.retains (channels D) τ (ident z)} : ℝ) =
      dens {τ : Environment P J | r.terminal.retains (channels D) τ (ident y)} := by
    rw [channel_density D r.terminal k ht, channel_density D r.terminal k ht]
  rw [hmid] at hleft
  have hrow : ∑ w, C z w ≤ 1 := by simpa [Matrix.mulVec, dotProduct] using hC1 z
  have hright := dense_terminal_mean D ident d hd hD hid H hbH hb hu
    cutoff h ρ K C q z y hsub hkh hρ0 hρ1 hη hρη (hC z) hrow (by simpa only [mul_one] using hK)
  rw [← mul_expect] at hright
  have hq : (dens {τ : Environment P J | q (τ d.terminal.role)} : ℝ) =
      dens {A | q A} := by rw [dens_filter_pi_eval d.terminal.role q]
  have hdu : (dens {τ : Environment P J |
      d.usage.retains (channels D) τ (ident y)} : ℝ) =
      dens {A | splitUsage D ident d A y} := by
    rw [channel_density D d.usage u hu, split_usage_density D ident d hu]
  rw [← hq, ← hdu] at hright
  have hfactor := sourceChild_mul_denseChild_factor HP D ident r hr d hd hst hmt
    C C i cutoff h ρ K q x z y hz
  let a := r.terminal.rate / (dens {τ : Environment P J |
    r.terminal.retains (channels D) τ (ident y)} : ℝ)
  let c := d.terminal.rate * ((dens {τ : Environment P J | q (τ d.terminal.role)} : ℝ) /
    dens {τ : Environment P J | d.usage.retains (channels D) τ (ident y)})
  calc
    _ = (a * c) * (𝔼 σ ∈ ({σ : Environment P J |
        r.source.retains (channels D) σ (ident x) ∧ q (σ d.terminal.role)} : Finset _),
        sourceChild HP D ident r hr C i σ x z *
          denseChild D ident d cutoff h ρ K C σ z y) := by
      rw [mul_expect]
      apply expect_congr rfl
      intro σ _
      dsimp only [a, c]
      ring
    _ = _ := by rw [hfactor]; calc
      _ = (a * (𝔼 σ ∈ ({σ : Environment P J |
          r.source.retains (channels D) σ (ident x)} : Finset _),
          sourceChild HP D ident r hr C i σ x z)) *
        (c * (𝔼 A ∈ ({A | q A} : Finset _),
          denseAtom (splitTerminal D ident d) (splitUsage D ident d)
            cutoff h ρ K d.terminal.rate C A z y)) := by ring
      _ = _ := by rw [hleft, hright]

end Matrix.HierarchyParams.H4RankEnvironment
