/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate
public import CslibFrontier.Computability.LogSpaceDerandomization.InitialPilotCorrectionMean
import CslibFrontier.Computability.LogSpaceDerandomization.RootMetric.FiniteError

/-!
# Completed first stochastic pilot correction

The outer walk averages the actual computed normalized child on its original full
source/usage environment slice, then multiplies by the stage rate to recover matrix
units. Usage equals the terminal rate in this bounded client. The allocated error
is an ordinary fourth moment, obtained from centered walk noise and root-paid mean
bias. No desired mean, pointwise preparation accuracy or independent reseeding is
assumed. The common-rate, covering-single-bin scope does not supply later iterations,
full bin assembly, recursive closure, effective parameter bounds or native space bounds.

## Main definitions

* `initialPilotCompleted`: actual outer conditional walk in parent matrix units.
* `initialPilotOuterSteps`: range-based positive outer allocation.

## Main results

* `initialPilotOuter_allocated`: centered-noise payment from the known range.
* `initialPilotCompleted_error`: centered noise plus root-paid mean bias.
* `initialPilotCompleted_accuracy`: allocated accuracy toward the canonical first correction.
-/
public section
noncomputable section
open Finset Cslib Cslib.Probability
open scoped BigOperators
namespace Matrix.HierarchyParams.H4RankEnvironment
attribute [local instance] Classical.propDecidable
variable {P J : ℕ} [Fact P.Prime]

/-- Complete the normalized child on the original source/usage slice, with the
literal stage-rate factor converting its conditional mean to parent matrix units. -/
@[expose] def initialPilotCompleted
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (D : ZMod P) (R : RoleProfile J)
    (bin ks kt kb : ℕ) (ss st : List (ZMod P))
    (cutoff h : ℝ → ℝ) (C : Matrix (ZMod P) (ZMod P) ℝ)
    (rawSteps prepSteps detectorSteps outerSteps : ℕ)
    (σ : Environment P J) (x y : ZMod P) : ℝ :=
  rate kt * conditionalWalk (X R.source (side P ks) (CopyPadding.identifier D ss))
    (Y R.terminal (side P kt) (CopyPadding.identifier D st))
    (graph R.source R.terminal R.source_terminal (side P ks) (side P kt)
      (side_le P ks) (side_le P kt) (CopyPadding.identifier D ss)
      (CopyPadding.identifier D st)) (fun _ _ => outerSteps)
    (initialPilotNormalized HP D R bin ks kt kb ss st cutoff h C
      rawSteps prepSteps detectorSteps) σ x y

/-- Range-based outer allocation, fixed before any lower calls. Width and source
rate are explicit. This finite bound does not count environment atoms. -/
@[expose] def initialPilotOuterSteps (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (P J ks : ℕ) (ε : ℝ) : ℕ :=
  max 1 (spectralWalkLength (1 - 1 / (155648 * (J+1) * (4:ℝ)^4))
    (32 * ((P : ℝ)^2 / (P * rate ks) *
      (2 * HP.Q HP.toHierarchyParams.atomCap)^4)) ε 0)

private theorem normalized_range
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (D : ZMod P) (R : RoleProfile J)
    (bin ks kt kb : ℕ) (ss st : List (ZMod P))
    (cutoff h : ℝ → ℝ) (C : Matrix (ZMod P) (ZMod P) ℝ)
    (rawSteps prepSteps detectorSteps : ℕ) (σ : Environment P J) (x y : ZMod P) :
    initialPilotNormalized HP D R bin ks kt kb ss st cutoff h C
      rawSteps prepSteps detectorSteps σ x y ∈
      Set.Icc 0 (2 * HP.Q HP.toHierarchyParams.atomCap) := by
  unfold initialPilotNormalized
  exact selectedRequest_mem_Icc HP D id _ _ _ _ _ σ x y

private theorem true_range
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (D : ZMod P) (R : RoleProfile J)
    (ks kt : ℕ) (ss st : List (ZMod P)) (C : Matrix (ZMod P) (ZMod P) ℝ)
    (σ : Environment P J) (x y : ZMod P) :
    initialTrueNormalized HP D R ks kt ss st C σ x y ∈
      Set.Icc 0 (2 * HP.Q HP.toHierarchyParams.atomCap) := by
  unfold initialTrueNormalized
  exact selectedRequest_mem_Icc HP D id _ _ _ _ _ σ x y

/-- The known normalized range pays the actual outer noise at a positive length,
regardless of the completed RAW, preparation and detector lengths. -/
theorem initialPilotOuter_allocated
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (D : ZMod P) (R : RoleProfile J)
    (bin ks kt kb : ℕ) (ss st : List (ZMod P))
    (cutoff h : ℝ → ℝ) (C : Matrix (ZMod P) (ZMod P) ℝ)
    (rawSteps prepSteps detectorSteps : ℕ) {ε : ℝ} (hε : 0 < ε) :
    let X := X R.source (side P ks) (CopyPadding.identifier D ss)
    let Y := Y R.terminal (side P kt) (CopyPadding.identifier D st)
    let A := initialPilotNormalized HP D R bin ks kt kb ss st cutoff h C
      rawSteps prepSteps detectorSteps
    let steps := initialPilotOuterSteps HP P J ks ε
    0 < steps ∧ rowNormPow 4 P (rate ks) X Y (fun σ x y =>
      conditionalWalk X Y (graph R.source R.terminal R.source_terminal
        (side P ks) (side P kt) (side_le P ks) (side_le P kt)
        (CopyPadding.identifier D ss) (CopyPadding.identifier D st))
        (fun _ _ => steps) A σ x y - rowSliceMean X Y A x y) ≤ ε^4 := by
  intro X Y A steps
  have hNu : 0 ≤ (P : ℝ) * rate ks := mul_nonneg (Nat.cast_nonneg _) (rate_pos ks).le
  have hrange := rowNormPow_fourth_le_expect_envelope hNu X Y A
    (fun _ => (2 * HP.Q HP.toHierarchyParams.atomCap)^4) (fun _ => by positivity)
    (fun σ x y _ _ => by
      rw [abs_of_nonneg (normalized_range HP D R bin ks kt kb ss st cutoff h C
        rawSteps prepSteps detectorSteps σ x y).1]
      exact pow_le_pow_left₀
        (normalized_range HP D R bin ks kt kb ss st cutoff h C
          rawSteps prepSteps detectorSteps σ x y).1
        (normalized_range HP D R bin ks kt kb ss st cutoff h C
          rawSteps prepSteps detectorSteps σ x y).2 4)
  simp only [ZMod.card, Fintype.expect_const] at hrange
  have hden : (1:ℝ) < 155648 * (J+1) * (4:ℝ)^4 := by
    have := Nat.cast_nonneg (α := ℝ) J; nlinarith
  have hr : 0 < 1 - 1 / (155648 * (J+1) * (4:ℝ)^4) :=
    sub_pos.mpr ((div_lt_one (by linarith)).mpr hden)
  have hp := spectralWalkLength_payment hr (sub_lt_self _ (by positivity))
    (show 0 ≤ 32 * ((P : ℝ)^2 / (P * rate ks) *
      (2 * HP.Q HP.toHierarchyParams.atomCap)^4) by positivity)
    hε 0 steps (Nat.le_max_right _ _)
  simp only [pow_zero, mul_one] at hp
  refine ⟨lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left _ _), ?_⟩
  have hn := noise R.source R.terminal R.source_terminal (side P ks) (side P kt)
    (side_le P ks) (side_le P kt) (CopyPadding.identifier D ss)
    (CopyPadding.identifier D st) hNu steps A
  exact hn.trans ((mul_le_mul_of_nonneg_left hrange (by positivity)).trans
    (by nlinarith only [hp]))

set_option backward.isDefEq.respectTransparency false in
/-- Centered noise and root-paid mean bias control the completed first correction.
The target identification is proved from primitive pilot sampling laws on the same
slice. The range, width and rates in both payments remain literal. -/
theorem initialPilotCompleted_error
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (D : ZMod P) (hD : D ≠ 0)
    (R : RoleProfile J) (H : Horizon P) (bin k kb : ℕ) (hk : k ≤ H.maxExponent)
    (ss st : List (ZMod P)) (cutoff h : ℝ → ℝ) (C : Matrix (ZMod P) (ZMod P) ℝ)
    (hC : ∀ x y, 0 ≤ C x y) (hC1 : C *ᵥ 1 ≤ 1)
    (hCf : ∀ x y, C x y ≤ rate k) (rawSteps prepSteps detectorSteps outerSteps : ℕ) :
    let X := X R.source (side P k) (CopyPadding.identifier D ss)
    let Y := Y R.terminal (side P k) (CopyPadding.identifier D st)
    let A := initialPilotNormalized HP D R bin k k kb ss st cutoff h C
      rawSteps prepSteps detectorSteps
    let A' := initialTrueNormalized HP D R k k ss st C
    let G := graph R.source R.terminal R.source_terminal (side P k) (side P k)
      (side_le P k) (side_le P k) (CopyPadding.identifier D ss) (CopyPadding.identifier D st)
    let target := pilotCorrection (HP.toHierarchyParams.cutoff (rate k)) HP.γ
      (columnDetector (canonicalChannel id (rate k)) (canonicalChannel id (rate k))
        HP.ϕ HP.ρ HP.J HP.K (rate k)) C 1
    rowNormPow 4 P (rate k) X Y (fun σ x y =>
      initialPilotCompleted HP D R bin k k kb ss st cutoff h C
        rawSteps prepSteps detectorSteps outerSteps σ x y - target x y) ≤
      8 * (rate k)^4 *
        (rowNormPow 4 P (rate k) X Y (fun σ x y =>
          conditionalWalk X Y G (fun _ _ => outerSteps) A σ x y - rowSliceMean X Y A x y) +
        (4 * (2 * HP.Q HP.toHierarchyParams.atomCap)^((3 : ℝ)/4))^4 *
          rootDistPow 4 P (rate k) X Y A A') := by
  intro X Y A A' G target
  have hNu : 0 ≤ (P : ℝ) * rate k := mul_nonneg (Nat.cast_nonneg _) (rate_pos k).le
  have hm : ∀ x y, rate k * rowSliceMean X Y A' x y = target x y :=
    initialTrueNormalized_mean HP D hD R H k hk ss st C hC hC1 hCf
  have hb := rowNormPow_sliceMean_sub_le_rootDistPow hNu X Y A A'
    (normalized_range HP D R bin k k kb ss st cutoff h C rawSteps prepSteps detectorSteps)
    (true_range HP D R k k ss st C)
  have he := rowNormPow_sub_le_centered (X := X) (Y := Y) hNu
    (initialPilotCompleted HP D R bin k k kb ss st cutoff h C
      rawSteps prepSteps detectorSteps outerSteps)
    (fun x y => rate k * rowSliceMean X Y A x y) target
  have hn : (fun σ x y => initialPilotCompleted HP D R bin k k kb ss st cutoff h C
      rawSteps prepSteps detectorSteps outerSteps σ x y - rate k * rowSliceMean X Y A x y) =
      (fun σ x y => rate k * (conditionalWalk X Y G (fun _ _ => outerSteps) A σ x y -
        rowSliceMean X Y A x y)) := by
    funext σ x y; dsimp only [initialPilotCompleted, A, X, Y, G]; ring
  have hm' : (fun (_ : Environment P J) x y => rate k * rowSliceMean X Y A x y -
      target x y) = (fun (_ : Environment P J) x y => rate k *
        (rowSliceMean X Y A x y - rowSliceMean X Y A' x y)) := by
    funext σ x y; rw [← hm x y]; ring
  rw [hn, hm', rowNormPow_mul (rate_pos k).le, rowNormPow_mul (rate_pos k).le] at he
  exact he.trans (by nlinarith [mul_le_mul_of_nonneg_left hb (pow_nonneg (rate_pos k).le 4)])

set_option backward.isDefEq.respectTransparency false in
/-- Positive-tolerance accuracy toward the genuine canonical FIRST pilot correction.
The outer range budget and length are fixed before invoking normalized-child allocation;
its RAW and detector tolerances are in turn fixed before completing their actual calls.
All regularity constants are selected for fixed HP before the prime and requests.
This proves an ordinary fourth-moment error in parent matrix units, for a common
source/rank/usage rate and one covering dense bin. It is not recursive closure. -/
theorem initialPilotCompleted_accuracy
    (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ∀ (P J : ℕ) [Fact P.Prime] (D : ZMod P), D ≠ 0 →
    ∀ (R : RoleProfile J) (H : Horizon P) (bin k : ℕ), k ≤ H.maxExponent →
    ∀ (ss st : List (ZMod P)) (cutoff h : ℝ → ℝ)
      (C : Matrix (ZMod P) (ZMod P) ℝ),
    (∀ v, cutoff v ≠ 0 → h v = 1) →
    ∀ η : ℝ, 0 < η → (∀ v, v ≤ η → HP.ρ v = 1) →
    2 * (1 + 32 / η) ≤ HP.K →
    (∀ x y, 0 ≤ C x y) → C *ᵥ 1 ≤ 1 →
    (∀ x y, C x y ≤ rate k) →
    (∀ x y, rate k * cutoff (C x y / rate k) = C x y) →
    ∀ π : ℝ, 0 < π →
    (∀ y, π ≤ (dens {t : FrameChannel P 4 1 | frameRetains P 4 (side P k) t
      (CopyPadding.identifier D st y)} : ℝ)) →
    ∀ ε : ℝ, 0 < ε →
    let conversion := (4 * (2 * HP.Q HP.toHierarchyParams.atomCap)^((3 : ℝ)/4))^4
    let payment := 8 * (rate k)^4 * (1 + conversion)
    let tolerance := ε / (1 + payment)
    let outerSteps := initialPilotOuterSteps HP P J k tolerance
    ∃ rawSteps detectorSteps : ℕ,
      0 < rawSteps ∧ 0 < detectorSteps ∧ 0 < outerSteps ∧
      rowNormPow 4 P (rate k)
        (X R.source (side P k) (CopyPadding.identifier D ss))
        (Y R.terminal (side P k) (CopyPadding.identifier D st))
        (fun σ x y => initialPilotCompleted HP D R bin k k k ss st cutoff h C
          rawSteps 1 detectorSteps outerSteps σ x y -
          pilotCorrection (HP.toHierarchyParams.cutoff (rate k)) HP.γ
            (columnDetector (canonicalChannel id (rate k)) (canonicalChannel id (rate k))
              HP.ϕ HP.ρ HP.J HP.K (rate k)) C 1 x y) ≤ ε^4 := by
  obtain ⟨L, Cr, Cp, Cm, Lp, hL, hCr, hCp, hCm, hLp, ha⟩ :=
    initialPilotNormalized_accuracy HP
  intro P J inst D hD R H bin k hk ss st cutoff h C hkh η hη hρη hK hC hC1 hCf
    hcover π hπ hY ε hε conversion payment tolerance outerSteps
  have hp : 0 ≤ payment := by dsimp only [payment, conversion]; positivity
  have ht : 0 < tolerance := div_pos hε (by linarith : 0 < 1 + payment)
  -- This length uses only the known range, before any lower call is completed.
  have hos : 0 < outerSteps := lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left _ _)
  let childPayment := 64 * (((Cr / rate k)^4 + Cp^4 * (Lp / rate k)^4) *
    (P : ℝ)^2 + Cm^4)
  let rawSteps := initialPilotRawSteps HP D R bin k k k ss st cutoff h C
    (tolerance / (1 + childPayment))
  let detectorSteps := initialPilotSteps HP L D R bin k k k ss st cutoff h C
    (tolerance / (1 + childPayment) / (1 + (P : ℝ) * rate k / (rate k * π)))
  obtain ⟨hrs, hds, he⟩ := ha P J D hD R H bin k k hk hk ss st cutoff h C hkh η hη hρη
    hK hC hC1 hcover π hπ hY tolerance ht
  refine ⟨rawSteps, detectorSteps, hrs, hds, hos, ?_⟩
  have hn := (initialPilotOuter_allocated HP D R bin k k k ss st cutoff h C
    rawSteps 1 detectorSteps ht).2
  have hb := initialPilotCompleted_error HP D hD R H bin k k hk ss st cutoff h C
    hC hC1 hCf rawSteps 1 detectorSteps outerSteps
  dsimp only at hb hn he
  have he' : rootDistPow 4 P (rate k)
      (X R.source (side P k) (CopyPadding.identifier D ss))
      (Y R.terminal (side P k) (CopyPadding.identifier D st))
      (initialPilotNormalized HP D R bin k k k ss st cutoff h C rawSteps 1 detectorSteps)
      (initialTrueNormalized HP D R k k ss st C) ≤ tolerance^4 := he
  apply hb.trans
  have hc : 0 ≤ conversion := by dsimp only [conversion]; positivity
  have hf : 0 ≤ 8 * (rate k)^4 := by positivity
  have hbound := mul_le_mul_of_nonneg_left
    (add_le_add hn (mul_le_mul_of_nonneg_left he' hc)) hf
  have hbound' : _ ≤ payment * tolerance^4 := hbound.trans_eq (by
    dsimp only [payment]; ring)
  exact hbound'.trans (calibrated_fourth_moment hp hε)

end Matrix.HierarchyParams.H4RankEnvironment
