/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate
public import Complexity.Computability.LogSpaceDerandomization.HierarchyCorrectionRawStability
public import Complexity.Computability.LogSpaceDerandomization.PilotDetectorTransport
public import Complexity.Computability.LogSpaceDerandomization.HierarchySourceSampling

/-!
# Paying actual correction error from running-maximum children

This original local client composes correction stability with the actual clipped
running-maximum recipe. It pays the previous maximum and current detector children,
rather than assuming a final pilot error. RAW and PREP remain on their original masks,
with the existing width and rate costs. Child functions may share every environment
coordinate. The detector payment is transported through the exact terminal split, with the rank
source reset to the terminal stage rate. Composing actual score stability pays signed
raw-child moments. Iterating these contracts with allocated accuracies is still open.

## Main results

* `Matrix.HierarchyParams.H4RankEnvironment.stageDetector_row_moment`: full-frame score payment.
* `Matrix.HierarchyParams.H4RankEnvironment.stageDetector_raw_row_moment`: fixed-HP raw payment.
* `Matrix.HierarchyParams.H4RankEnvironment.correctionRequest_stageDetector_root_moment`:
  combined RAW/PREP/previous-maximum and current score/detector payment.

* `Matrix.HierarchyParams.H4RankEnvironment.correctionRequest_pilot_children_root_moment`:
  actual correction root error paid from four changing child classes.
-/
public section
noncomputable section
namespace Matrix.HierarchyParams.H4RankEnvironment
open Finset Cslib
open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Actual stage detector payment on one full rank environment. The child's source is
reset to the terminal stage rate while retaining the original source role and suffix;
the terminal role and suffix are unchanged. Its score can depend on every outer
coordinate and the terminal frame. The detector integrates its source spectators
literally; this statement does not replace them by independently seeded child calls. -/
theorem stageDetector_row_moment
    {P J : ℕ} [Fact P.Prime] {V : Type} [Fintype V] {k : ℕ}
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (D : ZMod P) (ident : V → ZMod P)
    (r : HierarchyTask.Request k (Fin J) (ZMod P)) (hr : Admissible r)
    {N u π : ℝ} (hN : 0 < N) (hu : 0 < u) (hf : 0 < r.terminal.rate) (hπ : 0 < π)
    (hY : ∀ y, π ≤ (dens {t | splitTerminal D ident r t y} : ℝ))
    (A B : Environment P J → Cslib.Probability.FrameChannel P 4 1 → Matrix V V ℝ) :
    rowNormPow 4 N u
      (fun σ x => r.source.retains (channels D) σ (ident x))
      (fun σ y => r.terminal.retains (channels D) σ (ident y))
      (fun σ _ y => PilotRowRecipe.detector HP.toHierarchyParams
        (stageSource D ident r hr) (splitTerminal D ident r) (A σ) y -
        PilotRowRecipe.detector HP.toHierarchyParams
          (stageSource D ident r hr) (splitTerminal D ident r) (B σ) y) ≤
    (Fintype.card V : ℝ) * r.terminal.rate / (u * π) *
      rowNormPow 4 N r.terminal.rate
        (fun (p : Environment P J × Environment P J) x =>
          ({r.source with rate := r.terminal.rate}).retains (channels D) p.2 (ident x))
        (fun p y => r.terminal.retains (channels D) p.2 (ident y))
        (fun p x y => A p.1 (p.2 r.terminal.role) x y -
          B p.1 (p.2 r.terminal.role) x y) := by
  have h := PilotRowRecipe.detector_row_moment_transport HP.toHierarchyParams
    (stageSource D ident r hr) (splitTerminal D ident r)
    (fun σ x => r.source.retains (channels D) σ (ident x))
    (fun σ y => r.terminal.retains (channels D) σ (ident y))
    hN hu hf hπ hY A B
  apply h.trans_eq
  congr 1
  unfold rowNormPow
  congr 1
  apply Fintype.expect_equiv
    (Equiv.prodCongr (Equiv.refl (Environment P J)) (terminalSplit r.terminal.role).symm)
  intro p
  simp [hr.1, Equiv.prodCongr_apply, stageSource, splitTerminal, terminalSplit, coordinate,
    CorrectionRowTask.Channel.retains, channels]

set_option backward.isDefEq.respectTransparency false in
/-- The fixed-HP score contract and actual stage detector compose without an assumed
score error. Raw children remain signed and terminal-dependent. The two displayed
width factors pay parent rows and the raw terminal rank, respectively. Precision
allocation, bin assembly and closure of lower raw calls remain separate obligations. -/
theorem stageDetector_raw_row_moment
    (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ∃ C : ℝ, 0 ≤ C ∧
    ∀ (P J : ℕ) [Fact P.Prime] (V : Type) [Fintype V] (k : ℕ)
      (D : ZMod P) (ident : V → ZMod P)
      (r : HierarchyTask.Request k (Fin J) (ZMod P)) (hr : Admissible r)
      (N u π : ℝ), 0 < N → 0 < u → 0 < r.terminal.rate → 0 < π →
    (∀ y, π ≤ (dens {t | splitTerminal D ident r t y} : ℝ)) →
    ∀ (A B : Environment P J → Cslib.Probability.FrameChannel P 4 1 → Matrix V V ℝ),
    let score := fun raw σ t => PilotRowRecipe.score HP.toHierarchyParams
      (splitTerminal D ident r) r.terminal.rate (raw σ t) t
    rowNormPow 4 N u
      (fun σ x => r.source.retains (channels D) σ (ident x))
      (fun σ y => r.terminal.retains (channels D) σ (ident y))
      (fun σ _ y => PilotRowRecipe.detector HP.toHierarchyParams
        (stageSource D ident r hr) (splitTerminal D ident r) (score A σ) y -
        PilotRowRecipe.detector HP.toHierarchyParams
          (stageSource D ident r hr) (splitTerminal D ident r) (score B σ) y) ≤
    ((Fintype.card V : ℝ) * r.terminal.rate / (u * π)) *
      ((Fintype.card V : ℝ) * (C / r.terminal.rate) ^ 4) *
      rowNormPow 4 N r.terminal.rate
        (fun (p : Environment P J × Environment P J) x =>
          ({r.source with rate := r.terminal.rate}).retains (channels D) p.2 (ident x))
        (fun p y => r.terminal.retains (channels D) p.2 (ident y))
        (fun p x y => A p.1 (p.2 r.terminal.role) x y -
          B p.1 (p.2 r.terminal.role) x y) := by
  obtain ⟨Lϕ, Lρ, hLϕ, hLρ, hϕ, hρ⟩ := HP.pilot_score_stability_constants
  refine ⟨Lϕ + Lρ, add_nonneg hLϕ hLρ, ?_⟩
  intro P J instP V instV k D ident r hr N u π hN hu hf hπ hY A B score
  apply (stageDetector_row_moment HP D ident r hr hN hu hf hπ hY
    (score A) (score B)).trans
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have h := PilotRowRecipe.score_row_moment HP.toHierarchyParams
    (fun (p : Environment P J × Environment P J) x =>
      ({r.source with rate := r.terminal.rate}).retains (channels D) p.2 (ident x))
    (fun p y => r.terminal.retains (channels D) p.2 (ident y))
    HP.ρ_nonneg hLϕ hLρ hϕ hρ (FourthRootHierarchyParams.NormalizedRow.rank_pos HP) hf
    (mul_pos hN hf).le
    (fun p => A p.1 (p.2 r.terminal.role))
    (fun p => B p.1 (p.2 r.terminal.role))
  simpa only [score, PilotRowRecipe.score, splitTerminal, coordinate,
    CorrectionRowTask.Channel.retains, channels] using h

/-- The actual correction consumes the completed running maximum of two supplied
children. Both are paid by their ordinary fourth moments on the same original pairs.
The current detector may be paid using `PilotRowRecipe.detector_row_moment`.
Constants are selected before prime, width, structural request, rates or child functions. -/
theorem correctionRequest_pilot_children_root_moment
    (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ∃ Cr Cp Cm : ℝ, 0 ≤ Cr ∧ 0 ≤ Cp ∧ 0 ≤ Cm ∧
    ∀ (P J : ℕ) [Fact P.Prime] (V : Type*) [Fintype V] (k : ℕ)
      (D : ZMod P) (ident : V → ZMod P)
      (r : HierarchyTask.Request k (Fin J) (ZMod P)) (_hr : Admissible r),
    0 < r.terminal.rate → ∀ (Kc : ℕ), 0 < Kc →
    ∀ (raw raw' prep prep' : Environment P J → Matrix V V ℝ)
      (previous current previous' current' : Environment P J → V → ℝ) (N u : ℝ),
    0 ≤ N * u →
    (∀ σ y, r.usage.retains (channels D) σ (ident y) →
      r.terminal.retains (channels D) σ (ident y)) →
    let X := fun σ x => r.source.retains (channels D) σ (ident x)
    let Y := fun σ y => r.terminal.retains (channels D) σ (ident y)
    let U := fun σ y => r.usage.retains (channels D) σ (ident y)
    rootDistPow 4 N u X Y
      (correctionRequest D ident r (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ
        HP.toHierarchyParams.atomCutoff HP.γ HP.K Kc raw prep
        (fun σ => PilotRowRecipe.maximum (previous σ) (current σ)))
      (correctionRequest D ident r (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ
        HP.toHierarchyParams.atomCutoff HP.γ HP.K Kc raw' prep'
        (fun σ => PilotRowRecipe.maximum (previous' σ) (current' σ))) ≤
    64 * ((Cr / r.terminal.rate) ^ 4 * (Fintype.card V : ℝ) ^ 2 *
        rowNormPow 4 N u X Y (fun σ x y => raw σ x y - raw' σ x y) +
      Cp ^ 4 * rowNormPow 4 N u X U (fun σ x y => prep σ x y - prep' σ x y) +
      Cm ^ 4 * (rowNormPow 4 N u X Y (fun σ _ y => previous σ y - previous' σ y) +
        rowNormPow 4 N u X Y (fun σ _ y => current σ y - current' σ y))) := by
  obtain ⟨Cr, Cp, Cm, hCr, hCp, hCm, hc⟩ := correctionRequest_children_root_moment HP
  refine ⟨Cr, Cp, Cm, hCr, hCp, hCm, ?_⟩
  intro P J instP V instV k D ident r hr hf Kc hKc raw raw' prep prep'
    previous current previous' current' N u hNu hUY
  have h := hc P J V k D ident r hr hf Kc hKc raw raw' prep prep'
    (fun σ => PilotRowRecipe.maximum (previous σ) (current σ))
    (fun σ => PilotRowRecipe.maximum (previous' σ) (current' σ)) N u hNu hUY
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 64)
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hCm 4)
  exact PilotRowRecipe.maximum_row_moment _ _ previous current previous' current' hNu

/-- Full local pipeline: changing RAW/PREP correction children and a running maximum
whose current child is the actual score/detector composition. All constants are fixed
before requests and child functions. The previous maximum still requires its own local
moment; no final pilot-error premise is introduced. -/
theorem correctionRequest_stageDetector_root_moment
    (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ∃ Cr Cp Cm C : ℝ, 0 ≤ Cr ∧ 0 ≤ Cp ∧ 0 ≤ Cm ∧ 0 ≤ C ∧
    ∀ (P J : ℕ) [Fact P.Prime] (V : Type) [Fintype V] (k : ℕ)
      (D : ZMod P) (ident : V → ZMod P)
      (r : HierarchyTask.Request k (Fin J) (ZMod P)) (hr : Admissible r)
      (N u π : ℝ), 0 < N → 0 < u → 0 < r.terminal.rate → 0 < π →
    (∀ y, π ≤ (dens {t | splitTerminal D ident r t y} : ℝ)) →
    ∀ (Kc : ℕ), 0 < Kc →
    ∀ (raw raw' prep prep' : Environment P J → Matrix V V ℝ)
      (previous previous' : Environment P J → V → ℝ)
      (A B : Environment P J → Cslib.Probability.FrameChannel P 4 1 → Matrix V V ℝ),
    (∀ σ y, r.usage.retains (channels D) σ (ident y) →
      r.terminal.retains (channels D) σ (ident y)) →
    let X := fun σ x => r.source.retains (channels D) σ (ident x)
    let Y := fun σ y => r.terminal.retains (channels D) σ (ident y)
    let U := fun σ y => r.usage.retains (channels D) σ (ident y)
    let current := fun raw σ => PilotRowRecipe.detector HP.toHierarchyParams
      (stageSource D ident r hr) (splitTerminal D ident r)
      (fun t => PilotRowRecipe.score HP.toHierarchyParams (splitTerminal D ident r)
        r.terminal.rate (raw σ t) t)
    rootDistPow 4 N u X Y
      (correctionRequest D ident r (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ
        HP.toHierarchyParams.atomCutoff HP.γ HP.K Kc raw prep
        (fun σ => PilotRowRecipe.maximum (previous σ) (current A σ)))
      (correctionRequest D ident r (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ
        HP.toHierarchyParams.atomCutoff HP.γ HP.K Kc raw' prep'
        (fun σ => PilotRowRecipe.maximum (previous' σ) (current B σ))) ≤
    64 * ((Cr / r.terminal.rate) ^ 4 * (Fintype.card V : ℝ) ^ 2 *
        rowNormPow 4 N u X Y (fun σ x y => raw σ x y - raw' σ x y) +
      Cp ^ 4 * rowNormPow 4 N u X U (fun σ x y => prep σ x y - prep' σ x y) +
      Cm ^ 4 * (rowNormPow 4 N u X Y (fun σ _ y => previous σ y - previous' σ y) +
        ((Fintype.card V : ℝ) * r.terminal.rate / (u * π)) *
          ((Fintype.card V : ℝ) * (C / r.terminal.rate) ^ 4) *
          rowNormPow 4 N r.terminal.rate
            (fun (p : Environment P J × Environment P J) x =>
              ({r.source with rate := r.terminal.rate}).retains (channels D) p.2 (ident x))
            (fun p y => r.terminal.retains (channels D) p.2 (ident y))
            (fun p x y => A p.1 (p.2 r.terminal.role) x y -
              B p.1 (p.2 r.terminal.role) x y))) := by
  obtain ⟨Cr, Cp, Cm, hCr, hCp, hCm, hc⟩ :=
    correctionRequest_pilot_children_root_moment HP
  obtain ⟨C, hC, hd⟩ := stageDetector_raw_row_moment HP
  refine ⟨Cr, Cp, Cm, C, hCr, hCp, hCm, hC, ?_⟩
  intro P J instP V instV k D ident r hr N u π hN hu hf hπ hY Kc hKc
    raw raw' prep prep' previous previous' A B hUY X Y U current
  apply (hc P J V k D ident r hr hf Kc hKc raw raw' prep prep'
    previous (current A) previous' (current B) N u (mul_pos hN hu).le hUY).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 64)
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hCm 4)
  apply add_le_add le_rfl
  exact hd P J V k D ident r hr N u π hN hu hf hπ hY A B

end Matrix.HierarchyParams.H4RankEnvironment
