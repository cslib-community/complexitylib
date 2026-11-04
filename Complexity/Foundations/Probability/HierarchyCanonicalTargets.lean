/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyChannelTransport
public import Complexity.Foundations.Probability.HierarchySourceSampling

/-!
# Canonical correction targets across actual request roles

Genuine request targets are independent of their source and terminal role labels and
of inherited copy suffixes. We integrate the actual source spectators and use the existing
affine frame permutation for each suffix. The result is the same correction recurrence on
unpadded single-frame channels, with the original terminal stage rate and matrix units.
No equality of samples at the same environment is claimed.

This is a prerequisite milestone for canonical residual sampling, not a conditional-mean
identity for `HierarchyTask.rawSample`. Shared-midpoint product transport and canonical dense
and correction child assembly remain open, as do propagation of estimated child errors and
recursive derandomization. The transport is Christian Reitwiessner's original work, retaining
Samuel Schlesinger's adapted hierarchy construction.
-/

public section
open Finset Cslib Cslib.Probability
open scoped BigOperators
noncomputable section

namespace Matrix.HierarchyParams.H4RankEnvironment
attribute [local instance] Classical.propDecidable
variable {P J : ℕ} [Fact P.Prime] {V : Type} [Fintype V]
  (HP : FourthRootHierarchyParams 16 1 16 32 8) (D : ZMod P) (ident : V → ZMod P)

/-- The canonical stage channel, using an unpadded identifier on one frame.
The stage rate remains explicit; roles and copy suffixes are transported by permutations. -/
@[expose] def canonicalChannel (b : ℝ) (A : FrameChannel P 4 1) (v : V) : Prop :=
  frameRetains P 4 (semanticSide P b) A (ident v)

omit [Fintype V] in
/-- Copy padding is removed by an actual permutation of the frame seed, preserving all
vertices jointly. No pointwise equality on an unchanged seed is asserted. -/
theorem coordinate_padding (hD : D ≠ 0) (ch : Channel P J)
    (A : FrameChannel P 4 1) (v : V) :
    coordinate D ch A (ident v) ↔
      canonicalChannel ident ch.rate
        (FrameChannel.affineSubstEquiv (CopyPadding.identifier D ch.suffix 0)
          (pow_ne_zero ch.suffix.length hD) A) v := by
  unfold coordinate canonicalChannel frameRetains
  rw [FrameChannel.affineSubstEquiv_apply, FrameChannel.eval_affineSubst,
    ← CopyPadding.identifier_affine D ch.suffix (ident v)]

variable {n : ℕ} (r : HierarchyTask.Request n (Fin J) (ZMod P)) (hr : Admissible r)

/-- The true stage detector has one canonical target after integrating spectators
and transporting both copy suffixes. This does not identify approximate samples. -/
theorem stage_columnDetector_eq_canonical (hD : D ≠ 0) (C : Matrix V V ℝ) :
    columnDetector (stageSource D ident r hr) (splitTerminal D ident r)
      HP.ϕ HP.ρ HP.J HP.K r.terminal.rate C =
    columnDetector (canonicalChannel ident r.terminal.rate)
      (canonicalChannel ident r.terminal.rate) HP.ϕ HP.ρ HP.J HP.K r.terminal.rate C := by
  unfold stageSource splitTerminal
  rw [columnDetector_source_pi
    (fun A v => coordinate D {r.source with rate := r.terminal.rate} A (ident v))
    (fun A v => coordinate D r.terminal A (ident v))
    (⟨r.source.role, hr.1⟩ : {j : Fin J // j ≠ r.terminal.role})
    HP.ϕ HP.ρ HP.J HP.K r.terminal.rate C]
  exact columnDetector_equiv _ _
    (FrameChannel.affineSubstEquiv (CopyPadding.identifier D r.source.suffix 0)
      (pow_ne_zero r.source.suffix.length hD))
    (FrameChannel.affineSubstEquiv (CopyPadding.identifier D r.terminal.suffix 0)
      (pow_ne_zero r.terminal.suffix.length hD))
    _ _ (coordinate_padding D ident hD {r.source with rate := r.terminal.rate})
    (coordinate_padding D ident hD r.terminal) HP.ϕ HP.ρ HP.J HP.K r.terminal.rate C

/-- Integrate the actual source spectators and transport both suffixes. This identifies
the genuine stage pilot with one common canonical pilot, for every admissible request. -/
theorem stage_pilot_eq_canonical (hD : D ≠ 0) (C : Matrix V V ℝ) :
    HP.toHierarchyParams.pilot (stageSource D ident r hr) (splitTerminal D ident r)
      r.terminal.rate C =
    HP.toHierarchyParams.pilot (canonicalChannel ident r.terminal.rate)
      (canonicalChannel ident r.terminal.rate) r.terminal.rate C := by
  simp only [pilot_eq]
  congr 1
  funext G
  exact stage_columnDetector_eq_canonical HP D ident r hr hD G

/-- All genuine correction iterates use the same canonical target, with every role and
suffix retained until its measure-preserving transport has been proved. Usage does not
enter this deterministic target; it still enters the actual request's normalization. -/
theorem stage_correctionIter_eq_canonical (hD : D ≠ 0) (C : Matrix V V ℝ) (i : ℕ) :
    HP.toHierarchyParams.correctionIter (stageSource D ident r hr) (splitTerminal D ident r)
      r.terminal.rate C i =
    HP.toHierarchyParams.correctionIter (canonicalChannel ident r.terminal.rate)
      (canonicalChannel ident r.terminal.rate) r.terminal.rate C i := by
  simp only [correctionIter, stage_pilot_eq_canonical HP D ident r hr hD C]

/-- Source resets and terminal-role changes preserve the true correction target at the
same stage rate, even with different sampling/usage rates and arbitrary copy suffixes. -/
theorem stage_correctionIter_eq_of_terminal_rate
    (r' : HierarchyTask.Request n (Fin J) (ZMod P)) (hr' : Admissible r')
    (hD : D ≠ 0) (ht : r.terminal.rate = r'.terminal.rate) (C : Matrix V V ℝ) (i : ℕ) :
    HP.toHierarchyParams.correctionIter (stageSource D ident r hr) (splitTerminal D ident r)
      r.terminal.rate C i =
    HP.toHierarchyParams.correctionIter (stageSource D ident r' hr') (splitTerminal D ident r')
      r'.terminal.rate C i := by
  rw [stage_correctionIter_eq_canonical HP D ident r hr hD,
    stage_correctionIter_eq_canonical HP D ident r' hr' hD, ht]

/-- The actual final pilot child has the canonical target as well. -/
theorem stageMaximum_eq_canonical (hD : D ≠ 0) (C : Matrix V V ℝ) :
    stageMaximum HP D ident r hr C =
    HP.toHierarchyParams.pilot (canonicalChannel ident r.terminal.rate)
      (canonicalChannel ident r.terminal.rate) r.terminal.rate C := by
  rw [stageMaximum, PilotTask.value_maximum_last,
    stage_pilot_eq_canonical HP D ident r hr hD C]

/-- The genuine hierarchy residual is transported as C-E+EC, including its negative term.
This target identity does not average a stochastic residual sample. -/
theorem stage_residual_eq_canonical (hD : D ≠ 0) (C : Matrix V V ℝ) :
    HP.toHierarchyParams.residual (stageSource D ident r hr) (splitTerminal D ident r)
      r.terminal.rate C =
    HP.toHierarchyParams.residual (canonicalChannel ident r.terminal.rate)
      (canonicalChannel ident r.terminal.rate) r.terminal.rate C := by
  simp only [HierarchyParams.residual_eq, ← correctionIter_last,
    stage_correctionIter_eq_canonical HP D ident r hr hD]

/-- The true raw correction child is C+E_i C on the same canonical stage, in matrix units. -/
theorem stageRaw_eq_canonical (hD : D ≠ 0) (C : Matrix V V ℝ) (i : ℕ) :
    stageRaw HP D ident r hr C i =
    HP.toHierarchyParams.correctionInput (canonicalChannel ident r.terminal.rate)
      (canonicalChannel ident r.terminal.rate) r.terminal.rate C i := by
  simp only [stageRaw, correctionInput, stage_correctionIter_eq_canonical HP D ident r hr hD]

/-- The existing full-Ω correction mean has one canonical target across role resets and
copy suffixes. The original source/rank/usage rates and density divisor are unchanged.
This is a single correction child, not a product or residual raw-sample mean. -/
theorem source_request_mean_canonical (hD : D ≠ 0) (hid : Function.Injective ident)
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
      HP.toHierarchyParams.correctionIter (canonicalChannel ident r.terminal.rate)
        (canonicalChannel ident r.terminal.rate) r.terminal.rate C (i + 1) x y := by
  rw [source_request_mean HP D ident r hr hD hid H hsH hks hs ht hu C hC hC1 hCf hi,
    stage_correctionIter_eq_canonical HP D ident r hr hD C]

end Matrix.HierarchyParams.H4RankEnvironment
