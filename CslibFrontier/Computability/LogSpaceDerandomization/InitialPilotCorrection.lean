/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate

public import CslibFrontier.Computability.LogSpaceDerandomization.InitialPilotDetector
public import CslibFrontier.Computability.LogSpaceDerandomization.HierarchyPilotStability

/-!
# Computed children of the first positive pilot correction

Preparation recomputes the actual incoming recipe on the completed RAW table and
then runs the conditional walk on the inherited source/usage slice. Normalization
consumes this computed preparation, the completed RAW table and the clipped initial
maximum, all on the original environment. No true-input preparation oracle is used.

The deterministic `pilotCorrection` constructor and its stochastic `pilotNormalized`
child are distinct: the former applies the bounded cutoff directly, while the latter
has incoming gates and a conditional preparatory denominator. The definitions below
retain both. The direct constructor has allocated accuracy under the covering single-bin
hypotheses. The normalized child has allocated accuracy against the original true
normalized request. `InitialPilotCompleted` separately completes its outer walk to the
canonical first correction under common source/rank/usage rates; recursive closure remains open.

## Main results

* `initialPilotNormalized_accuracy`: allocated normalized-child accuracy.
* `initialPilotPreparationWalk_mean`: exact stationarity of its original normalizer.
* `initialPilotNormalized_raw_detector_moment`: RAW and detector payments without PREP noise.
* `initialPilotNormalized_root_moment`: pre-walk preparation perturbation bound.
* `initialPilotCorrection_accuracy`: allocated accuracy from genuine completed lower calls.
* `initialTrueCorrection_eq_canonical`: canonical target of the first direct correction.

## Main definitions

* `initialPilotPreparation`: the incoming recipe computed from completed RAW.
* `initialPilotPreparationWalk`: its actual source/usage conditional walk.
* `initialPilotMaximum`: the clipped running maximum of zero and the computed detector.
* `initialPilotNormalized`: the actual normalized pilot child.
* `initialPilotCorrection`: the direct first positive pilot constructor.
-/
public section
noncomputable section
open Finset Cslib Cslib.Probability
open scoped BigOperators
namespace Matrix.HierarchyParams.H4RankEnvironment
attribute [local instance] Classical.propDecidable
variable {P J : ℕ} [Fact P.Prime]

/-- The selected incoming preparation is recomputed from the completed lower RAW call.
Both finite rank sets retain their actual roles, sides and copy suffixes. -/
@[expose] def initialPilotPreparation
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (D : ZMod P) (R : RoleProfile J)
    (bin ks kt kb : ℕ) (ss st : List (ZMod P))
    (cutoff h : ℝ → ℝ) (C : Matrix (ZMod P) (ZMod P) ℝ) (rawSteps : ℕ)
    (σ : Environment P J) : Matrix (ZMod P) (ZMod P) ℝ :=
  correctionPrep (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.K
    ⌈4 * (1 + 32 * HP.R)⌉₊ (rate kt)
    (initialPilotWalk HP D R bin ks kt kb ss st cutoff h C rawSteps σ)
    (polynomialPrepCutoff4 HP.θ) HP.ρ
    {x | X R.source (side P ks) (CopyPadding.identifier D ss) σ x}
    {y | Y R.terminal (side P kt) (CopyPadding.identifier D st) σ y}

/-- The preparatory child uses the actual full-coordinate H4 conditional walk.
Its input is the recipe of the computed RAW table, rather than preparation of a true value. -/
@[expose] def initialPilotPreparationWalk
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (D : ZMod P) (R : RoleProfile J)
    (bin ks kt kb : ℕ) (ss st : List (ZMod P))
    (cutoff h : ℝ → ℝ) (C : Matrix (ZMod P) (ZMod P) ℝ) (rawSteps prepSteps : ℕ) :=
  conditionalWalk (X R.source (side P ks) (CopyPadding.identifier D ss))
    (Y R.terminal (side P kt) (CopyPadding.identifier D st))
    (graph R.source R.terminal R.source_terminal (side P ks) (side P kt)
      (side_le P ks) (side_le P kt) (CopyPadding.identifier D ss)
      (CopyPadding.identifier D st)) (fun _ _ => prepSteps)
    (initialPilotPreparation HP D R bin ks kt kb ss st cutoff h C rawSteps)

/-- The actual preparation walk preserves the original joint source/usage normalizer.
This is stationarity on the same full environment, without a pointwise PREP limit. -/
theorem initialPilotPreparationWalk_mean
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (D : ZMod P) (R : RoleProfile J)
    (bin ks kt kb : ℕ) (ss st : List (ZMod P))
    (cutoff h : ℝ → ℝ) (C : Matrix (ZMod P) (ZMod P) ℝ) (rawSteps prepSteps : ℕ)
    (x y : ZMod P) :
    rowSliceMean (X R.source (side P ks) (CopyPadding.identifier D ss))
      (Y R.terminal (side P kt) (CopyPadding.identifier D st))
      (initialPilotPreparationWalk HP D R bin ks kt kb ss st cutoff h C rawSteps prepSteps)
      x y =
    rowSliceMean (X R.source (side P ks) (CopyPadding.identifier D ss))
      (Y R.terminal (side P kt) (CopyPadding.identifier D st))
      (initialPilotPreparation HP D R bin ks kt kb ss st cutoff h C rawSteps) x y :=
  rowSliceMean_conditionalWalk _ _ _ _ _ x y

/-- Initial maximum, after the actual source-aware detector has completed.
The detector's RAW allocation may differ from that of the parent RAW child. -/
@[expose] def initialPilotMaximum
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (D : ZMod P) (R : RoleProfile J)
    (bin ks kt kb : ℕ) (ss st : List (ZMod P))
    (cutoff h : ℝ → ℝ) (C : Matrix (ZMod P) (ZMod P) ℝ) (detectorSteps : ℕ) :=
  PilotRowRecipe.maximum 0
    (initialPilotDetector HP D R bin ks kt kb ss st cutoff h C detectorSteps)

/-- The actual first normalized pilot child, including its computed preparation and
literal conditional source/usage normalizer. Usage equals the stage rate in this fragment. -/
@[expose] def initialPilotNormalized
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (D : ZMod P) (R : RoleProfile J)
    (bin ks kt kb : ℕ) (ss st : List (ZMod P))
    (cutoff h : ℝ → ℝ) (C : Matrix (ZMod P) (ZMod P) ℝ)
    (rawSteps prepSteps detectorSteps : ℕ) :=
  let r : HierarchyTask.Request HP.k (Fin J) (ZMod P) :=
    ⟨.row 0 (.pilotNormalized ⟨0, HP.k_pos⟩), gridChannel R.source ks ss,
      gridChannel R.terminal kt st, gridChannel R.terminal kt st⟩
  correctionRequest D id r (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ
    HP.toHierarchyParams.atomCutoff HP.γ HP.K ⌈4 * (1 + 32 * HP.R)⌉₊
    (initialPilotWalk HP D R bin ks kt kb ss st cutoff h C rawSteps)
    (initialPilotPreparationWalk HP D R bin ks kt kb ss st cutoff h C rawSteps prepSteps)
    (fun _ => initialPilotMaximum HP D R bin ks kt kb ss st cutoff h C detectorSteps)

set_option backward.isDefEq.respectTransparency false in
/-- Walking preparation changes no value of the actual normalized child: the request
uses only its stationary source/usage mean. The walk itself is still computed. -/
theorem initialPilotNormalized_eq_unwalked
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (D : ZMod P) (R : RoleProfile J)
    (bin ks kt kb : ℕ) (ss st : List (ZMod P))
    (cutoff h : ℝ → ℝ) (C : Matrix (ZMod P) (ZMod P) ℝ)
    (rawSteps prepSteps detectorSteps : ℕ) (σ : Environment P J) (x y : ZMod P) :
    let r : HierarchyTask.Request HP.k (Fin J) (ZMod P) :=
      ⟨.row 0 (.pilotNormalized ⟨0, HP.k_pos⟩), gridChannel R.source ks ss,
        gridChannel R.terminal kt st, gridChannel R.terminal kt st⟩
    initialPilotNormalized HP D R bin ks kt kb ss st cutoff h C
      rawSteps prepSteps detectorSteps σ x y =
    correctionRequest D id r (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ
      HP.toHierarchyParams.atomCutoff HP.γ HP.K ⌈4 * (1 + 32 * HP.R)⌉₊
      (initialPilotWalk HP D R bin ks kt kb ss st cutoff h C rawSteps)
      (initialPilotPreparation HP D R bin ks kt kb ss st cutoff h C rawSteps)
      (fun _ => initialPilotMaximum HP D R bin ks kt kb ss st cutoff h C detectorSteps)
      σ x y := by
  intro r
  apply correctionRequest_congr_normalizer D id r ⟨R.source_terminal, rfl, rfl⟩
  have hm := initialPilotPreparationWalk_mean HP D R bin ks kt kb ss st cutoff h C
    rawSteps prepSteps x y
  have he : ({σ : Environment P J | r.source.retains (channels D) σ (id x) ∧
      r.usage.retains (channels D) σ (id y)} : Finset _) =
      ({σ | X R.source (side P ks) (CopyPadding.identifier D ss) σ x ∧
        Y R.terminal (side P kt) (CopyPadding.identifier D st) σ y} : Finset _) := by
    ext σ
    simp only [mem_filter, mem_univ, true_and, r, gridChannel,
      CorrectionRowTask.Channel.retains, channels, semanticSide_grid, X, Y, id_eq]
  unfold rowSliceMean at hm ⊢
  rw [he]
  exact hm

set_option backward.isDefEq.respectTransparency false in
/-- Optional coarse bound using the walked preparation error. Its pointwise PREP
moment need not decay; `initialPilotNormalized_accuracy` instead uses exact normalizer
stationarity and pays only the pre-walk RAW perturbation. -/
theorem initialPilotNormalized_root_moment_coarse
    (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ∃ Cr Cp Cm : ℝ, 0 ≤ Cr ∧ 0 ≤ Cp ∧ 0 ≤ Cm ∧
    ∀ (P J : ℕ) [Fact P.Prime] (D : ZMod P) (R : RoleProfile J)
      (bin ks kt kb : ℕ) (ss st : List (ZMod P))
      (cutoff h : ℝ → ℝ) (C : Matrix (ZMod P) (ZMod P) ℝ)
      (rawSteps prepSteps detectorSteps : ℕ),
    let r : HierarchyTask.Request HP.k (Fin J) (ZMod P) :=
      ⟨.row 0 (.pilotNormalized ⟨0, HP.k_pos⟩), gridChannel R.source ks ss,
        gridChannel R.terminal kt st, gridChannel R.terminal kt st⟩
    let X := fun σ v => r.source.retains (channels D) σ (id v)
    let Y := fun σ v => r.terminal.retains (channels D) σ (id v)
    let truePrep := fun σ => correctionPrep (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff
      HP.K ⌈4 * (1 + 32 * HP.R)⌉₊ (rate kt) C (polynomialPrepCutoff4 HP.θ) HP.ρ
      {v | X σ v} {v | Y σ v}
    rootDistPow 4 P (rate ks) X Y
      (initialPilotNormalized HP D R bin ks kt kb ss st cutoff h C
        rawSteps prepSteps detectorSteps)
      (correctionRequest D id r (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ
        HP.toHierarchyParams.atomCutoff HP.γ HP.K ⌈4 * (1 + 32 * HP.R)⌉₊
        (fun _ => C) truePrep
        (fun _ => PilotRowRecipe.maximum 0 (initialTrueDetector HP D R ks kt ss st C))) ≤
    64 * (((Cr / rate kt) ^ 4 * (P : ℝ) ^ 2) *
      rowNormPow 4 P (rate ks) X Y (fun σ x y =>
        initialPilotWalk HP D R bin ks kt kb ss st cutoff h C rawSteps σ x y - C x y) +
      Cp ^ 4 * rowNormPow 4 P (rate ks) X Y (fun σ x y =>
        initialPilotPreparationWalk HP D R bin ks kt kb ss st cutoff h C
          rawSteps prepSteps σ x y - truePrep σ x y) +
      Cm ^ 4 * rowNormPow 4 P (rate ks) X Y (fun _ _ y =>
        initialPilotDetector HP D R bin ks kt kb ss st cutoff h C detectorSteps y -
          initialTrueDetector HP D R ks kt ss st C y)) := by
  obtain ⟨Cr, Cp, Cm, hCr, hCp, hCm, hc⟩ := correctionRequest_pilot_children_root_moment HP
  refine ⟨Cr, Cp, Cm, hCr, hCp, hCm, ?_⟩
  intro P J inst D R bin ks kt kb ss st cutoff h C rawSteps prepSteps detectorSteps r X Y truePrep
  have hr : Admissible r := ⟨R.source_terminal, rfl, rfl⟩
  have hKc : 0 < ⌈4 * (1 + 32 * HP.R)⌉₊ := by
    have hj : (0:ℝ) < HP.J := by exact_mod_cast HP.J_pos
    have hR := HP.R_rank
    norm_num only [one_mul] at hR
    apply Nat.ceil_pos.mpr
    linarith
  have hp := hc P J (ZMod P) HP.k D id r hr (rate_pos kt) _ hKc
    (initialPilotWalk HP D R bin ks kt kb ss st cutoff h C rawSteps) (fun _ => C)
    (initialPilotPreparationWalk HP D R bin ks kt kb ss st cutoff h C rawSteps prepSteps)
    truePrep (fun _ _ => 0)
    (fun _ => initialPilotDetector HP D R bin ks kt kb ss st cutoff h C detectorSteps)
    (fun _ _ => 0) (fun _ => initialTrueDetector HP D R ks kt ss st C)
    P (rate ks) (mul_nonneg (Nat.cast_nonneg _) (rate_pos ks).le) (fun _ _ hy => hy)
  have hz : rowNormPow 4 P (rate ks)
      (fun σ v => r.source.retains (channels D) σ (id v))
      (fun σ v => r.terminal.retains (channels D) σ (id v)) (fun _ _ _ => (0:ℝ)) = 0 := by
    simp [rowNormPow]
  simp only [sub_self, ZMod.card] at hp
  rw [hz, zero_add] at hp
  simpa only [initialPilotNormalized, initialPilotMaximum, X, Y, r, gridChannel,
    ← Pi.zero_def] using hp

set_option backward.isDefEq.respectTransparency false in
/-- The normalized child pays only the pre-walk preparation perturbation.
Stationarity removes preparation-walk noise from the normalizer exactly. This local
bound is suitable for RAW allocation; the coarse pointwise PREP bound is optional. -/
theorem initialPilotNormalized_root_moment
    (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ∃ Cr Cp Cm : ℝ, 0 ≤ Cr ∧ 0 ≤ Cp ∧ 0 ≤ Cm ∧
    ∀ (P J : ℕ) [Fact P.Prime] (D : ZMod P) (R : RoleProfile J)
      (bin ks kt kb : ℕ) (ss st : List (ZMod P))
      (cutoff h : ℝ → ℝ) (C : Matrix (ZMod P) (ZMod P) ℝ)
      (rawSteps prepSteps detectorSteps : ℕ),
    let r : HierarchyTask.Request HP.k (Fin J) (ZMod P) :=
      ⟨.row 0 (.pilotNormalized ⟨0, HP.k_pos⟩), gridChannel R.source ks ss,
        gridChannel R.terminal kt st, gridChannel R.terminal kt st⟩
    let X := fun σ v => r.source.retains (channels D) σ (id v)
    let Y := fun σ v => r.terminal.retains (channels D) σ (id v)
    let truePrep := fun σ => correctionPrep (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff
      HP.K ⌈4 * (1 + 32 * HP.R)⌉₊ (rate kt) C (polynomialPrepCutoff4 HP.θ) HP.ρ
      {v | X σ v} {v | Y σ v}
    rootDistPow 4 P (rate ks) X Y
      (initialPilotNormalized HP D R bin ks kt kb ss st cutoff h C
        rawSteps prepSteps detectorSteps)
      (correctionRequest D id r (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ
        HP.toHierarchyParams.atomCutoff HP.γ HP.K ⌈4 * (1 + 32 * HP.R)⌉₊
        (fun _ => C) truePrep
        (fun _ => PilotRowRecipe.maximum 0 (initialTrueDetector HP D R ks kt ss st C))) ≤
    64 * (((Cr / rate kt) ^ 4 * (P : ℝ) ^ 2) *
      rowNormPow 4 P (rate ks) X Y (fun σ x y =>
        initialPilotWalk HP D R bin ks kt kb ss st cutoff h C rawSteps σ x y - C x y) +
      Cp ^ 4 * rowNormPow 4 P (rate ks) X Y (fun σ x y =>
        initialPilotPreparation HP D R bin ks kt kb ss st cutoff h C
          rawSteps σ x y - truePrep σ x y) +
      Cm ^ 4 * rowNormPow 4 P (rate ks) X Y (fun _ _ y =>
        initialPilotDetector HP D R bin ks kt kb ss st cutoff h C detectorSteps y -
          initialTrueDetector HP D R ks kt ss st C y)) := by
  obtain ⟨Cr, Cp, Cm, hCr, hCp, hCm, hc⟩ := correctionRequest_pilot_children_root_moment HP
  refine ⟨Cr, Cp, Cm, hCr, hCp, hCm, ?_⟩
  intro P J inst D R bin ks kt kb ss st cutoff h C rawSteps prepSteps detectorSteps r X Y truePrep
  have hr : Admissible r := ⟨R.source_terminal, rfl, rfl⟩
  have hKc : 0 < ⌈4 * (1 + 32 * HP.R)⌉₊ := by
    have hj : (0:ℝ) < HP.J := by exact_mod_cast HP.J_pos
    have hR := HP.R_rank
    norm_num only [one_mul] at hR
    apply Nat.ceil_pos.mpr
    linarith
  have hp := hc P J (ZMod P) HP.k D id r hr (rate_pos kt) _ hKc
    (initialPilotWalk HP D R bin ks kt kb ss st cutoff h C rawSteps) (fun _ => C)
    (initialPilotPreparation HP D R bin ks kt kb ss st cutoff h C rawSteps)
    truePrep (fun _ _ => 0)
    (fun _ => initialPilotDetector HP D R bin ks kt kb ss st cutoff h C detectorSteps)
    (fun _ _ => 0) (fun _ => initialTrueDetector HP D R ks kt ss st C)
    P (rate ks) (mul_nonneg (Nat.cast_nonneg _) (rate_pos ks).le) (fun _ _ hy => hy)
  have hz : rowNormPow 4 P (rate ks)
      (fun σ v => r.source.retains (channels D) σ (id v))
      (fun σ v => r.terminal.retains (channels D) σ (id v)) (fun _ _ _ => (0:ℝ)) = 0 := by
    simp [rowNormPow]
  simp only [sub_self, ZMod.card] at hp
  rw [hz, zero_add] at hp
  have heq : initialPilotNormalized HP D R bin ks kt kb ss st cutoff h C
      rawSteps prepSteps detectorSteps =
      correctionRequest D id r (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ
        HP.toHierarchyParams.atomCutoff HP.γ HP.K ⌈4 * (1 + 32 * HP.R)⌉₊
        (initialPilotWalk HP D R bin ks kt kb ss st cutoff h C rawSteps)
        (initialPilotPreparation HP D R bin ks kt kb ss st cutoff h C rawSteps)
        (fun _ => initialPilotMaximum HP D R bin ks kt kb ss st cutoff h C detectorSteps) := by
    funext σ x y
    exact initialPilotNormalized_eq_unwalked HP D R bin ks kt kb ss st cutoff h C
      rawSteps prepSteps detectorSteps σ x y
  rw [heq]
  simpa only [initialPilotMaximum, X, Y, r, gridChannel, ← Pi.zero_def] using hp

set_option backward.isDefEq.respectTransparency false in
/-- The actual normalized child is paid only by its computed RAW and detector errors.
Preparation is removed by same-slice stationarity and its actual RAW perturbation;
conditional Jensen and rectangle maxima pay explicit width/rate costs. -/
theorem initialPilotNormalized_raw_detector_moment
    (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ∃ Cr Cp Cm Lp : ℝ, 0 ≤ Cr ∧ 0 ≤ Cp ∧ 0 ≤ Cm ∧ 0 ≤ Lp ∧
    ∀ (P J : ℕ) [Fact P.Prime] (D : ZMod P) (R : RoleProfile J)
      (bin ks kt kb : ℕ) (ss st : List (ZMod P))
      (cutoff h : ℝ → ℝ) (C : Matrix (ZMod P) (ZMod P) ℝ)
      (rawSteps prepSteps detectorSteps : ℕ),
    let r : HierarchyTask.Request HP.k (Fin J) (ZMod P) :=
      ⟨.row 0 (.pilotNormalized ⟨0, HP.k_pos⟩), gridChannel R.source ks ss,
        gridChannel R.terminal kt st, gridChannel R.terminal kt st⟩
    let X := fun σ v => r.source.retains (channels D) σ (id v)
    let Y := fun σ v => r.terminal.retains (channels D) σ (id v)
    let truePrep := fun σ => correctionPrep (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff
      HP.K ⌈4 * (1 + 32 * HP.R)⌉₊ (rate kt) C (polynomialPrepCutoff4 HP.θ) HP.ρ
      {v | X σ v} {v | Y σ v}
    rootDistPow 4 P (rate ks) X Y
      (initialPilotNormalized HP D R bin ks kt kb ss st cutoff h C
        rawSteps prepSteps detectorSteps)
      (correctionRequest D id r (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ
        HP.toHierarchyParams.atomCutoff HP.γ HP.K ⌈4 * (1 + 32 * HP.R)⌉₊
        (fun _ => C) truePrep
        (fun _ => PilotRowRecipe.maximum 0 (initialTrueDetector HP D R ks kt ss st C))) ≤
    64 * ((((Cr / rate kt) ^ 4 + Cp ^ 4 * (Lp / rate kt) ^ 4) * (P : ℝ) ^ 2) *
      rowNormPow 4 P (rate ks) X Y (fun σ x y =>
        initialPilotWalk HP D R bin ks kt kb ss st cutoff h C rawSteps σ x y - C x y) +
      Cm ^ 4 * rowNormPow 4 P (rate ks) X Y (fun _ _ y =>
        initialPilotDetector HP D R bin ks kt kb ss st cutoff h C detectorSteps y -
          initialTrueDetector HP D R ks kt ss st C y)) := by
  obtain ⟨Cr, Cp, Cm, hCr, hCp, hCm, hc⟩ := initialPilotNormalized_root_moment HP
  obtain ⟨Lp, hLp, hp⟩ := HP.correction_preparation_row_moment
  refine ⟨Cr, Cp, Cm, Lp, hCr, hCp, hCm, hLp, ?_⟩
  intro P J inst D R bin ks kt kb ss st cutoff h C rawSteps prepSteps detectorSteps r X Y truePrep
  have hKc : 0 < ⌈4 * (1 + 32 * HP.R)⌉₊ := by
    have hj : (0:ℝ) < HP.J := by exact_mod_cast HP.J_pos
    have hR := HP.R_rank
    norm_num only [one_mul] at hR
    apply Nat.ceil_pos.mpr
    linarith
  have hprep := hp (Environment P J) (ZMod P)
    (H4RankEnvironment.X R.source (side P ks) (CopyPadding.identifier D ss))
    (H4RankEnvironment.Y R.terminal (side P kt) (CopyPadding.identifier D st))
    _ hKc _ (rate_pos kt)
    (initialPilotWalk HP D R bin ks kt kb ss st cutoff h C rawSteps) (fun _ => C)
    P (rate ks) (mul_nonneg (Nat.cast_nonneg _) (rate_pos ks).le)
  have hprep' : rowNormPow 4 P (rate ks) X Y (fun σ x y =>
      initialPilotPreparation HP D R bin ks kt kb ss st cutoff h C rawSteps σ x y -
        truePrep σ x y) ≤
      (Lp / rate kt) ^ 4 * (P : ℝ) ^ 2 *
        rowNormPow 4 P (rate ks) X Y (fun σ x y =>
          initialPilotWalk HP D R bin ks kt kb ss st cutoff h C rawSteps σ x y - C x y) := by
    simpa only [rowNormPow, initialPilotPreparation, truePrep, X, Y, r, gridChannel,
      CorrectionRowTask.Channel.retains, channels, semanticSide_grid, id_eq, ZMod.card,
      H4RankEnvironment.X, H4RankEnvironment.Y] using hprep
  apply (hc P J D R bin ks kt kb ss st cutoff h C rawSteps prepSteps detectorSteps).trans
  apply (mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left hprep' (pow_nonneg hCp 4)))
      le_rfl) (by norm_num : (0:ℝ) ≤ 64)).trans_eq
  ring

/-- The deterministic first positive pilot constructor, in matrix units. This is the
literal direct constructor of `hierarchyTaskEval`, distinct from its normalized child. -/
@[expose] def initialPilotCorrection
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (D : ZMod P) (R : RoleProfile J)
    (bin ks kt kb : ℕ) (ss st : List (ZMod P))
    (cutoff h : ℝ → ℝ) (C : Matrix (ZMod P) (ZMod P) ℝ)
    (rawSteps detectorSteps : ℕ) (σ : Environment P J) (x y : ZMod P) : ℝ :=
  rate kt * HP.toHierarchyParams.atomCutoff
    (initialPilotWalk HP D R bin ks kt kb ss st cutoff h C rawSteps σ x y / rate kt) *
      HP.γ (initialPilotMaximum HP D R bin ks kt kb ss st cutoff h C detectorSteps y)

/-- Every actual local dependency of the first normalized pilot is strictly earlier.
No statistical accuracy parameter changes HP.k or the task order. -/
theorem initialPilotNormalized_ranks (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    (HierarchyTask.row (k := HP.k) 0 (.pilotInput ⟨0, HP.k_pos⟩)).rank <
      (HierarchyTask.row 0 (.pilotPreparation ⟨0, HP.k_pos⟩)).rank ∧
    ∀ child ∈ (HierarchyTask.row (k := HP.k) 0
      (.pilotNormalized ⟨0, HP.k_pos⟩)).children,
      child.rank < (HierarchyTask.row 0 (.pilotNormalized ⟨0, HP.k_pos⟩)).rank := by
  constructor
  · apply HierarchyTask.rank_lt_of_mem_children
    simp [HierarchyTask.children, BoundedRowTask.children]
  · intro child hc
    exact HierarchyTask.rank_lt_of_mem_children hc

/-- The direct first correction remains bounded for arbitrary signed computed children. -/
theorem initialPilotCorrection_mem_Icc
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (D : ZMod P) (R : RoleProfile J)
    (bin ks kt kb : ℕ) (ss st : List (ZMod P))
    (cutoff h : ℝ → ℝ) (C : Matrix (ZMod P) (ZMod P) ℝ)
    (rawSteps detectorSteps : ℕ) (σ : Environment P J) (x y : ZMod P) :
    initialPilotCorrection HP D R bin ks kt kb ss st cutoff h C rawSteps detectorSteps σ x y ∈
      Set.Icc 0 (rate kt * HP.Q HP.toHierarchyParams.atomCap) := by
  unfold initialPilotCorrection
  exact ⟨mul_nonneg (mul_nonneg (rate_pos kt).le
    (HP.toHierarchyParams.atomCutoff_nonneg _)) (HP.γ_nonneg _),
    (mul_le_of_le_one_right (mul_nonneg (rate_pos kt).le
      (HP.toHierarchyParams.atomCutoff_nonneg _)) (HP.γ_le_one _)).trans
      (mul_le_mul_of_nonneg_left (HP.toHierarchyParams.atomCutoff_le _) (rate_pos kt).le)⟩

/-- Global root constants for the direct pilot constructor are fixed before the
prime, rates, requests and child functions. Only the scalar source cutoff is clipped. -/
theorem initialPilotCorrection_constants
    (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ∃ Lq Lg : ℝ, 0 ≤ Lq ∧ 0 ≤ Lg ∧ ∀ a b m n : ℝ,
      |(HP.toHierarchyParams.atomCutoff a * HP.γ m) ^ (4⁻¹ : ℝ) -
        (HP.toHierarchyParams.atomCutoff b * HP.γ n) ^ (4⁻¹ : ℝ)| ≤
      Lq * |a - b| + Lg * |m - n| := by
  obtain ⟨Lq, hq⟩ := HP.Q_root
  obtain ⟨⟨Lg, hg⟩, _⟩ := HP.cutoff_roots HP.γ (by simp)
  let B := HP.Q HP.toHierarchyParams.atomCap ^ (4⁻¹ : ℝ)
  refine ⟨Lq, B * Lg, Lq.coe_nonneg, mul_nonneg
    (Real.rpow_nonneg (HP.Q_nonneg _) _) Lg.coe_nonneg, ?_⟩
  intro a b m n
  have hc : |min HP.toHierarchyParams.atomCap (max 0 a) -
      min HP.toHierarchyParams.atomCap (max 0 b)| ≤ |a-b| := by
    apply (abs_min_sub_min_le_max _ _ _ _).trans
    apply max_le
    · simpa only [sub_self, abs_zero] using abs_nonneg (a-b)
    · apply (abs_max_sub_max_le_max _ _ _ _).trans
      exact max_le (by simpa only [sub_self, abs_zero] using abs_nonneg (a-b)) le_rfl
  have hq' : |HP.toHierarchyParams.atomCutoff a ^ (4⁻¹ : ℝ) -
      HP.toHierarchyParams.atomCutoff b ^ (4⁻¹ : ℝ)| ≤ Lq * |a-b| := by
    have h := hq.dist_le_mul (min HP.toHierarchyParams.atomCap (max 0 a))
      (min HP.toHierarchyParams.atomCap (max 0 b))
    simp only [Real.dist_eq] at h
    exact h.trans (mul_le_mul_of_nonneg_left hc Lq.coe_nonneg)
  have hg' := hg.dist_le_mul m n
  simp only [Real.dist_eq] at hg'
  have hb : HP.toHierarchyParams.atomCutoff b ^ (4⁻¹ : ℝ) ≤ B :=
    Real.rpow_le_rpow (HP.toHierarchyParams.atomCutoff_nonneg _)
      (HP.toHierarchyParams.atomCutoff_le _) (by norm_num)
  have hm : HP.γ m ^ (4⁻¹ : ℝ) ≤ 1 :=
    Real.rpow_le_one (HP.γ_nonneg _) (HP.γ_le_one _) (by norm_num)
  rw [Real.mul_rpow (HP.toHierarchyParams.atomCutoff_nonneg _) (HP.γ_nonneg _),
    Real.mul_rpow (HP.toHierarchyParams.atomCutoff_nonneg _) (HP.γ_nonneg _)]
  have he : HP.toHierarchyParams.atomCutoff a ^ (4⁻¹ : ℝ) * HP.γ m ^ (4⁻¹ : ℝ) -
      HP.toHierarchyParams.atomCutoff b ^ (4⁻¹ : ℝ) * HP.γ n ^ (4⁻¹ : ℝ) =
      (HP.toHierarchyParams.atomCutoff a ^ (4⁻¹ : ℝ) -
        HP.toHierarchyParams.atomCutoff b ^ (4⁻¹ : ℝ)) * HP.γ m ^ (4⁻¹ : ℝ) +
      HP.toHierarchyParams.atomCutoff b ^ (4⁻¹ : ℝ) *
        (HP.γ m ^ (4⁻¹ : ℝ) - HP.γ n ^ (4⁻¹ : ℝ)) := by ring
  rw [he]
  apply (abs_add_le _ _).trans
  rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg (HP.γ_nonneg _) _),
    abs_of_nonneg (Real.rpow_nonneg (HP.toHierarchyParams.atomCutoff_nonneg _) _)]
  exact add_le_add
    ((mul_le_of_le_one_right (abs_nonneg _) hm).trans hq')
    ((mul_le_mul hb hg' (abs_nonneg _) (Real.rpow_nonneg (HP.Q_nonneg _) _)).trans_eq
      (by ring))

/-- Error of the literal direct constructor is paid by its two genuine completed
children. The initial maximum is assembled here, rather than assumed accurate. -/
theorem initialPilotCorrection_root_moment
    (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ∃ Lq Lg : ℝ, 0 ≤ Lq ∧ 0 ≤ Lg ∧
    ∀ (P J : ℕ) [Fact P.Prime] (D : ZMod P) (R : RoleProfile J)
      (bin ks kt kb : ℕ) (ss st : List (ZMod P))
      (cutoff h : ℝ → ℝ) (C : Matrix (ZMod P) (ZMod P) ℝ)
      (rawSteps detectorSteps : ℕ),
    let X := X R.source (side P ks) (CopyPadding.identifier D ss)
    let Y := Y R.terminal (side P kt) (CopyPadding.identifier D st)
    let M := PilotRowRecipe.maximum 0 (initialTrueDetector HP D R ks kt ss st C)
    let target := fun (_ : Environment P J) x y =>
      rate kt * HP.toHierarchyParams.atomCutoff (C x y / rate kt) * HP.γ (M y)
    rootDistPow 4 P (rate ks) X Y
      (initialPilotCorrection HP D R bin ks kt kb ss st cutoff h C rawSteps detectorSteps)
      target ≤
    64 * (((rate kt) ^ (4⁻¹ : ℝ) * Lq / rate kt) ^ 4 *
      rowNormPow 4 P (rate ks) X Y (fun σ x y =>
        initialPilotWalk HP D R bin ks kt kb ss st cutoff h C rawSteps σ x y - C x y) +
      ((rate kt) ^ (4⁻¹ : ℝ) * Lg) ^ 4 *
        rowNormPow 4 P (rate ks) X Y (fun _ _ y =>
          initialPilotDetector HP D R bin ks kt kb ss st cutoff h C detectorSteps y -
            initialTrueDetector HP D R ks kt ss st C y)) := by
  obtain ⟨Lq, Lg, hq, hg, hc⟩ := initialPilotCorrection_constants HP
  refine ⟨Lq, Lg, hq, hg, ?_⟩
  intro P J inst D R bin ks kt kb ss st cutoff h C rawSteps detectorSteps X Y M target
  let A := initialPilotWalk HP D R bin ks kt kb ss st cutoff h C rawSteps
  let d := initialPilotDetector HP D R bin ks kt kb ss st cutoff h C detectorSteps
  let t := initialTrueDetector HP D R ks kt ss st C
  let ar := (rate kt) ^ (4⁻¹ : ℝ) * Lq / rate kt
  let ag := (rate kt) ^ (4⁻¹ : ℝ) * Lg
  let F := fun σ x y => ar * |A σ x y - C x y|
  let G := fun (_ : Environment P J) (_ : ZMod P) y => ag * |d y - t y|
  have har : 0 ≤ ar := div_nonneg
    (mul_nonneg (Real.rpow_nonneg (rate_pos kt).le _) hq) (rate_pos kt).le
  have hag : 0 ≤ ag := mul_nonneg (Real.rpow_nonneg (rate_pos kt).le _) hg
  have hNu : 0 ≤ (P : ℝ) * rate ks := mul_nonneg (Nat.cast_nonneg _) (rate_pos ks).le
  have he (σ : Environment P J) (x y : ZMod P) :
      |initialPilotCorrection HP D R bin ks kt kb ss st cutoff h C rawSteps detectorSteps
        σ x y ^ (4⁻¹ : ℝ) - target σ x y ^ (4⁻¹ : ℝ)| ≤ F σ x y + G σ x y + 0 := by
    have hm := PilotRowRecipe.maximum_stability (0 : ZMod P → ℝ) d 0 t y
    simp only [Pi.zero_apply, sub_self, abs_zero] at hm
    rw [max_eq_right (abs_nonneg (d y - t y))] at hm
    have hh := hc (A σ x y / rate kt) (C x y / rate kt)
      (PilotRowRecipe.maximum 0 d y) (M y)
    rw [← sub_div, abs_div, abs_of_pos (rate_pos kt)] at hh
    have hr (q g : ℝ) (hq : 0 ≤ q) (hg : 0 ≤ g) :
        (rate kt * q * g) ^ (4⁻¹ : ℝ) =
          (rate kt) ^ (4⁻¹ : ℝ) * (q * g) ^ (4⁻¹ : ℝ) := by
      rw [mul_assoc, Real.mul_rpow (rate_pos kt).le (mul_nonneg hq hg)]
    dsimp only [initialPilotCorrection, target]
    rw [hr _ _ (HP.toHierarchyParams.atomCutoff_nonneg _) (HP.γ_nonneg _),
      hr _ _ (HP.toHierarchyParams.atomCutoff_nonneg _) (HP.γ_nonneg _),
      ← mul_sub, abs_mul, abs_of_nonneg (Real.rpow_nonneg (rate_pos kt).le _)]
    apply (mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg (rate_pos kt).le _)).trans
    have hh' := mul_le_mul_of_nonneg_left hm hg
    dsimp only [F, G, ar, ag]
    have ht := mul_le_mul_of_nonneg_left hh'
      (Real.rpow_nonneg (rate_pos kt).le (4⁻¹ : ℝ))
    change _ ≤ _ at ht
    convert add_le_add_left ht
      ((rate kt) ^ (4⁻¹ : ℝ) * Lq / rate kt * |A σ x y - C x y|) using 1 <;>
      dsimp only [M, t] <;> ring
  have hb := rowNormPow_le_three (X := X) (Y := Y) hNu
    (fun σ x y => initialPilotCorrection HP D R bin ks kt kb ss st cutoff h C
      rawSteps detectorSteps σ x y ^ (4⁻¹ : ℝ) - target σ x y ^ (4⁻¹ : ℝ))
    F G (fun _ _ _ => 0)
    (fun _ _ _ => mul_nonneg har (abs_nonneg _))
    (fun _ _ _ => mul_nonneg hag (abs_nonneg _)) (fun _ _ _ => le_rfl)
    (fun σ x y _ _ => he σ x y)
  have hf : rowNormPow 4 P (rate ks) X Y F =
      ar ^ 4 * rowNormPow 4 P (rate ks) X Y (fun σ x y => A σ x y - C x y) := by
    rw [show F = (fun σ x y => ar * |A σ x y - C x y|) from rfl, rowNormPow_mul har]
    simp only [rowNormPow, abs_abs]
  have hg' : rowNormPow 4 P (rate ks) X Y G =
      ag ^ 4 * rowNormPow 4 P (rate ks) X Y (fun _ _ y => d y - t y) := by
    rw [show G = (fun _ _ y => ag * |d y - t y|) from rfl, rowNormPow_mul hag]
    simp only [rowNormPow, abs_abs]
  have hz : rowNormPow 4 P (rate ks) X Y (fun _ _ _ => (0 : ℝ)) = 0 := by
    simp [rowNormPow]
  simpa only [rootDistPow, hf, hg', hz, add_zero, Nat.cast_ofNat] using hb

/-- Allocate RAW directly from its genuine dense input moment. The tolerance is
chosen before completing the call; no final RAW error is part of the input. -/
@[expose] def initialPilotRawSteps
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (D : ZMod P) (R : RoleProfile J)
    (bin ks kt kb : ℕ) (ss st : List (ZMod P))
    (cutoff h : ℝ → ℝ) (C : Matrix (ZMod P) (ZMod P) ℝ) (ε : ℝ) : ℕ :=
  max 1 (spectralWalkLength (1 - 1 / (155648 * (J+1) * (4:ℝ)^4))
    (32 * rowNormPow 4 P (rate ks)
      (X R.source (side P ks) (CopyPadding.identifier D ss))
      (Y R.terminal (side P kt) (CopyPadding.identifier D st))
      (initialPilotRaw HP D R bin ks kt kb ss st cutoff h C)) ε 0)

/-- The RAW allocation pays the actual full-coordinate walk against its literal mean. -/
theorem initialPilotRaw_allocated
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (D : ZMod P) (R : RoleProfile J)
    (bin ks kt kb : ℕ) (ss st : List (ZMod P))
    (cutoff h : ℝ → ℝ) (C : Matrix (ZMod P) (ZMod P) ℝ) {ε : ℝ} (hε : 0 < ε) :
    let X := X R.source (side P ks) (CopyPadding.identifier D ss)
    let Y := Y R.terminal (side P kt) (CopyPadding.identifier D st)
    let input := initialPilotRaw HP D R bin ks kt kb ss st cutoff h C
    let steps := initialPilotRawSteps HP D R bin ks kt kb ss st cutoff h C ε
    0 < steps ∧ rowNormPow 4 P (rate ks) X Y (fun σ x y =>
      initialPilotWalk HP D R bin ks kt kb ss st cutoff h C steps σ x y -
        rowSliceMean X Y input x y) ≤ ε ^ 4 := by
  intro X Y input steps
  have hNu : 0 ≤ (P : ℝ) * rate ks := mul_nonneg (Nat.cast_nonneg _) (rate_pos ks).le
  have hden : (1:ℝ) < 155648 * (J+1) * (4:ℝ)^4 := by
    have := Nat.cast_nonneg (α := ℝ) J; nlinarith
  have hr : 0 < 1 - 1 / (155648 * (J+1) * (4:ℝ)^4) :=
    sub_pos.mpr ((div_lt_one (by linarith)).mpr hden)
  have hp := spectralWalkLength_payment hr (sub_lt_self _ (by positivity))
    (mul_nonneg (by norm_num) (rowNormPow_nonneg hNu input)) hε 0 steps
    (Nat.le_max_right _ _)
  simp only [pow_zero, mul_one] at hp
  refine ⟨lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left _ _), ?_⟩
  have hn := noise R.source R.terminal R.source_terminal (side P ks) (side P kt)
    (side_le P ks) (side_le P kt) (CopyPadding.identifier D ss)
    (CopyPadding.identifier D st) hNu steps input
  exact hn.trans (by nlinarith only [hp])

set_option backward.isDefEq.respectTransparency false in
/-- Positive tolerances for both genuine children are fixed before their calls.
The reference uses the true initial detector, identified with the canonical one below.
The explicit single-bin mean hypotheses are inherited from the computed dense RAW law.
This theorem is for the direct pilot constructor; normalized-child accuracy is separate. -/
theorem initialPilotCorrection_accuracy
    (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ∃ L Lq Lg : ℝ, 0 ≤ L ∧ 0 ≤ Lq ∧ 0 ≤ Lg ∧
    ∀ (P J : ℕ) [Fact P.Prime] (D : ZMod P), D ≠ 0 →
    ∀ (R : RoleProfile J) (H : Horizon P) (bin ks kt : ℕ),
    ks ≤ H.maxExponent → kt ≤ H.maxExponent →
    ∀ (ss st : List (ZMod P)) (cutoff h : ℝ → ℝ)
      (C : Matrix (ZMod P) (ZMod P) ℝ),
    (∀ v, cutoff v ≠ 0 → h v = 1) →
    ∀ η : ℝ, 0 < η → (∀ v, v ≤ η → HP.ρ v = 1) →
    2 * (1 + 32 / η) ≤ HP.K →
    (∀ x y, 0 ≤ C x y) → C *ᵥ 1 ≤ 1 →
    (∀ x y, rate kt * cutoff (C x y / rate kt) = C x y) →
    ∀ π : ℝ, 0 < π →
    (∀ y, π ≤ (dens {t : FrameChannel P 4 1 | frameRetains P 4 (side P kt) t
      (CopyPadding.identifier D st y)} : ℝ)) →
    ∀ ε : ℝ, 0 < ε →
    let payment := 64 * (((rate kt) ^ (4⁻¹ : ℝ) * Lq / rate kt) ^ 4 +
      ((rate kt) ^ (4⁻¹ : ℝ) * Lg) ^ 4)
    let tolerance := ε / (1 + payment)
    let detectorPayment := (P : ℝ) * rate kt / (rate ks * π)
    let rawSteps := initialPilotRawSteps HP D R bin ks kt kt ss st cutoff h C tolerance
    let detectorSteps := initialPilotSteps HP L D R bin kt kt kt ss st cutoff h C
      (tolerance / (1 + detectorPayment))
    0 < rawSteps ∧ 0 < detectorSteps ∧
    rootDistPow 4 P (rate ks)
      (X R.source (side P ks) (CopyPadding.identifier D ss))
      (Y R.terminal (side P kt) (CopyPadding.identifier D st))
      (initialPilotCorrection HP D R bin ks kt kt ss st cutoff h C rawSteps detectorSteps)
      (fun _ x y => rate kt * HP.toHierarchyParams.atomCutoff (C x y / rate kt) *
        HP.γ (PilotRowRecipe.maximum 0 (initialTrueDetector HP D R ks kt ss st C) y)) ≤ ε ^ 4 := by
  obtain ⟨L, hL, hd⟩ := initialPilotDetector_accuracy HP
  obtain ⟨Lq, Lg, hq, hg, hc⟩ := initialPilotCorrection_root_moment HP
  refine ⟨L, Lq, Lg, hL, hq, hg, ?_⟩
  intro P J inst D hD R H bin ks kt hks hkt ss st cutoff h C hkh η hη hρη hK hC hC1
    hcover π hπ hY ε hε payment tolerance detectorPayment rawSteps detectorSteps
  have hp0 : 0 ≤ payment := mul_nonneg (by norm_num)
    (add_nonneg (pow_nonneg (div_nonneg
      (mul_nonneg (Real.rpow_nonneg (rate_pos kt).le _) hq) (rate_pos kt).le) 4)
      (pow_nonneg (mul_nonneg (Real.rpow_nonneg (rate_pos kt).le _) hg) 4))
  have hden : 0 < 1 + payment := by linarith
  have ht : 0 < tolerance := div_pos hε hden
  obtain ⟨hrs, hr⟩ := initialPilotRaw_allocated HP D R bin ks kt kt ss st cutoff h C ht
  have hm : rowSliceMean
      (X R.source (side P ks) (CopyPadding.identifier D ss))
      (Y R.terminal (side P kt) (CopyPadding.identifier D st))
      (initialPilotRaw HP D R bin ks kt kt ss st cutoff h C) = C := by
    funext x y
    exact (initialPilotRaw_mean HP D hD R H bin ks kt hks hkt ss st cutoff h C hkh hη
      hρη hK hC hC1 x y).trans (hcover x y)
  rw [hm] at hr
  obtain ⟨hds, he⟩ := hd P J D hD R H bin ks kt hkt ss st cutoff h C hkh η hη hρη hK
    hC hC1 hcover π hπ hY tolerance ht
  refine ⟨hrs, hds, (hc P J D R bin ks kt kt ss st cutoff h C rawSteps detectorSteps).trans ?_⟩
  have hb : _ ≤ payment * tolerance ^ 4 := mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left hr
        (pow_nonneg (div_nonneg
          (mul_nonneg (Real.rpow_nonneg (rate_pos kt).le _) hq)
          (rate_pos kt).le) 4))
      (mul_le_mul_of_nonneg_left he
        (pow_nonneg (mul_nonneg (Real.rpow_nonneg (rate_pos kt).le _) hg) 4)))
    (by norm_num : (0:ℝ) ≤ 64)
    |>.trans_eq (by dsimp only [payment]; ring)
  apply hb.trans
  exact calibrated_fourth_moment hp0 hε

set_option backward.isDefEq.respectTransparency false in
/-- Allocated root accuracy for the genuine normalized child. Positive RAW/detector
tolerances precede the calls; preparation uses parameter one (two actual graph steps).
Its joint normalizer is paid by RAW perturbation and conditional Jensen, without a
pointwise PREP accuracy premise. The target is the original true normalized request;
identification and payment of its completed outer walk are in `InitialPilotCompleted`. -/
theorem initialPilotNormalized_accuracy
    (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ∃ L Cr Cp Cm Lp : ℝ, 0 ≤ L ∧ 0 ≤ Cr ∧ 0 ≤ Cp ∧ 0 ≤ Cm ∧ 0 ≤ Lp ∧
    ∀ (P J : ℕ) [Fact P.Prime] (D : ZMod P), D ≠ 0 →
    ∀ (R : RoleProfile J) (H : Horizon P) (bin ks kt : ℕ),
    ks ≤ H.maxExponent → kt ≤ H.maxExponent →
    ∀ (ss st : List (ZMod P)) (cutoff h : ℝ → ℝ)
      (C : Matrix (ZMod P) (ZMod P) ℝ),
    (∀ v, cutoff v ≠ 0 → h v = 1) →
    ∀ η : ℝ, 0 < η → (∀ v, v ≤ η → HP.ρ v = 1) →
    2 * (1 + 32 / η) ≤ HP.K →
    (∀ x y, 0 ≤ C x y) → C *ᵥ 1 ≤ 1 →
    (∀ x y, rate kt * cutoff (C x y / rate kt) = C x y) →
    ∀ π : ℝ, 0 < π →
    (∀ y, π ≤ (dens {t : FrameChannel P 4 1 | frameRetains P 4 (side P kt) t
      (CopyPadding.identifier D st y)} : ℝ)) →
    ∀ ε : ℝ, 0 < ε →
    let payment := 64 * ((((Cr / rate kt) ^ 4 + Cp ^ 4 * (Lp / rate kt) ^ 4) *
      (P : ℝ) ^ 2) + Cm ^ 4)
    let tolerance := ε / (1 + payment)
    let detectorPayment := (P : ℝ) * rate kt / (rate ks * π)
    let rawSteps := initialPilotRawSteps HP D R bin ks kt kt ss st cutoff h C tolerance
    let detectorSteps := initialPilotSteps HP L D R bin kt kt kt ss st cutoff h C
      (tolerance / (1 + detectorPayment))
    let r : HierarchyTask.Request HP.k (Fin J) (ZMod P) :=
      ⟨.row 0 (.pilotNormalized ⟨0, HP.k_pos⟩), gridChannel R.source ks ss,
        gridChannel R.terminal kt st, gridChannel R.terminal kt st⟩
    let truePrep := fun σ => correctionPrep (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff
      HP.K ⌈4 * (1 + 32 * HP.R)⌉₊ (rate kt) C (polynomialPrepCutoff4 HP.θ) HP.ρ
      {x | X R.source (side P ks) (CopyPadding.identifier D ss) σ x}
      {y | Y R.terminal (side P kt) (CopyPadding.identifier D st) σ y}
    0 < rawSteps ∧ 0 < detectorSteps ∧
    rootDistPow 4 P (rate ks)
      (X R.source (side P ks) (CopyPadding.identifier D ss))
      (Y R.terminal (side P kt) (CopyPadding.identifier D st))
      (initialPilotNormalized HP D R bin ks kt kt ss st cutoff h C rawSteps 1 detectorSteps)
      (correctionRequest D id r (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ
        HP.toHierarchyParams.atomCutoff HP.γ HP.K ⌈4 * (1 + 32 * HP.R)⌉₊
        (fun _ => C) truePrep
        (fun _ => PilotRowRecipe.maximum 0 (initialTrueDetector HP D R ks kt ss st C))) ≤
      ε ^ 4 := by
  obtain ⟨L, hL, hd⟩ := initialPilotDetector_accuracy HP
  obtain ⟨Cr, Cp, Cm, Lp, hCr, hCp, hCm, hLp, hc⟩ :=
    initialPilotNormalized_raw_detector_moment HP
  refine ⟨L, Cr, Cp, Cm, Lp, hL, hCr, hCp, hCm, hLp, ?_⟩
  intro P J inst D hD R H bin ks kt hks hkt ss st cutoff h C hkh η hη hρη hK hC hC1
    hcover π hπ hY ε hε payment tolerance detectorPayment rawSteps detectorSteps r truePrep
  have hp0 : 0 ≤ payment := by dsimp only [payment]; positivity
  have ht : 0 < tolerance := div_pos hε (by linarith : 0 < 1 + payment)
  obtain ⟨hrs, hr⟩ := initialPilotRaw_allocated HP D R bin ks kt kt ss st cutoff h C ht
  have hm : rowSliceMean
      (X R.source (side P ks) (CopyPadding.identifier D ss))
      (Y R.terminal (side P kt) (CopyPadding.identifier D st))
      (initialPilotRaw HP D R bin ks kt kt ss st cutoff h C) = C := by
    funext x y
    exact (initialPilotRaw_mean HP D hD R H bin ks kt hks hkt ss st cutoff h C hkh hη
      hρη hK hC hC1 x y).trans (hcover x y)
  rw [hm] at hr
  obtain ⟨hds, he⟩ := hd P J D hD R H bin ks kt hkt ss st cutoff h C hkh η hη hρη hK
    hC hC1 hcover π hπ hY tolerance ht
  have hb := hc P J D R bin ks kt kt ss st cutoff h C rawSteps 1 detectorSteps
  dsimp only at hb
  have hb' : rootDistPow 4 P (rate ks)
      (X R.source (side P ks) (CopyPadding.identifier D ss))
      (Y R.terminal (side P kt) (CopyPadding.identifier D st))
      (initialPilotNormalized HP D R bin ks kt kt ss st cutoff h C rawSteps 1 detectorSteps)
      (correctionRequest D id r (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ
        HP.toHierarchyParams.atomCutoff HP.γ HP.K ⌈4 * (1 + 32 * HP.R)⌉₊
        (fun _ => C) truePrep
        (fun _ => PilotRowRecipe.maximum 0 (initialTrueDetector HP D R ks kt ss st C))) ≤
        payment * tolerance ^ 4 := by
    have hr' : rowNormPow 4 P (rate ks)
        (fun σ v => r.source.retains (channels D) σ (id v))
        (fun σ v => r.terminal.retains (channels D) σ (id v))
        (fun σ x y => initialPilotWalk HP D R bin ks kt kt ss st cutoff h C
          rawSteps σ x y - C x y) ≤ tolerance ^ 4 := by
      simpa only [rowNormPow, r, gridChannel, CorrectionRowTask.Channel.retains,
        channels, semanticSide_grid, X, Y, id_eq] using hr
    have he' : rowNormPow 4 P (rate ks)
        (fun σ v => r.source.retains (channels D) σ (id v))
        (fun σ v => r.terminal.retains (channels D) σ (id v))
        (fun _ _ y => initialPilotDetector HP D R bin ks kt kt ss st cutoff h C
          detectorSteps y - initialTrueDetector HP D R ks kt ss st C y) ≤ tolerance ^ 4 := by
      simpa only [rowNormPow, r, gridChannel, CorrectionRowTask.Channel.retains,
        channels, semanticSide_grid, X, Y, id_eq] using he
    have hp := hb.trans (mul_le_mul_of_nonneg_left
      (add_le_add (mul_le_mul_of_nonneg_left hr' (by positivity))
        (mul_le_mul_of_nonneg_left he' (pow_nonneg hCm 4)))
        (by norm_num : (0:ℝ) ≤ 64))
    simpa only [rootDistPow, rowNormPow, r, truePrep, gridChannel,
      CorrectionRowTask.Channel.retains, channels, semanticSide_grid, X, Y, id_eq,
      show 64 * (((Cr / rate kt) ^ 4 + Cp ^ 4 * (Lp / rate kt) ^ 4) * (P:ℝ)^2 *
        tolerance^4 + Cm^4 * tolerance^4) = payment * tolerance^4 by
          dsimp only [payment]; ring] using hp
  exact ⟨hrs, hds, hb'.trans (calibrated_fourth_moment hp0 hε)⟩

/-- The genuine first correction target is the canonical pilot correction, including
its actual stage rate and newly completed maximum. -/
theorem initialTrueCorrection_eq_canonical
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (D : ZMod P) (hD : D ≠ 0)
    (R : RoleProfile J) (ks kt : ℕ) (ss st : List (ZMod P))
    (C : Matrix (ZMod P) (ZMod P) ℝ)
    (hC : ∀ x y, 0 ≤ C x y) (hCf : ∀ x y, C x y ≤ rate kt) (x y : ZMod P) :
    rate kt * HP.toHierarchyParams.atomCutoff (C x y / rate kt) *
      HP.γ (PilotRowRecipe.maximum 0 (initialTrueDetector HP D R ks kt ss st C) y) =
    pilotCorrection (HP.toHierarchyParams.cutoff (rate kt)) HP.γ
      (columnDetector (canonicalChannel id (rate kt)) (canonicalChannel id (rate kt))
        HP.ϕ HP.ρ HP.J HP.K (rate kt)) C 1 x y := by
  have ht : initialTrueDetector HP D R ks kt ss st C y ≤ 1 := by
    change min 1 (max 0 _) ≤ 1
    exact min_le_left _ _
  rw [PilotRowRecipe.maximum, Pi.zero_apply,
    min_eq_right (max_le zero_le_one (max_le zero_le_one ht))]
  rw [initialTrueDetector_eq_canonical HP D hD R ks kt ss st C,
    HP.toHierarchyParams.atomCutoff_eq (div_nonneg (hC x y) (rate_pos kt).le)
      ((div_le_one (rate_pos kt)).mpr (hCf x y) |>.trans (by
        have := Nat.cast_nonneg (α := ℝ) HP.k; linarith))]
  rw [pilotCorrection_succ_apply, pilotMax_succ, pilotMax_zero]
  simp only [pilotInput, pilotCorrection_zero, zero_mul, add_zero,
    Pi.sup_apply, Pi.zero_apply, HP.toHierarchyParams.cutoff_apply, ← max_assoc, max_self]

end Matrix.HierarchyParams.H4RankEnvironment
