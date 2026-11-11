/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate
public import CslibFrontier.Computability.LogSpaceDerandomization.NormalizedAtomRows.SecondEnvelope
public import CslibFrontier.Computability.LogSpaceDerandomization.RootMetric.FiniteEnvelope

/-!
# Common deterministic envelopes of the actual two-signal prefixes

The first envelope is the actual absolute input mean error divided by `rate k + G`.
The second is B1 of the completed full-terminal RAW walk. A finite zero-padded
maximum after division by the dyadic slope gives one deterministic matrix per channel.
Both prefixes use the same completed raw walk, and preparation follows that walk.
The fourth moment is paid by the sum of the scaled actual prefix envelope moments.
This finite construction does not assume a final common envelope or a target cap.
The finite output consumer is `ReserveOutput`; recursive reserve induction remains separate.
The row/normalization proof patterns are adapted from Samuel Schlesinger.

## Main definitions

* `firstMeanEnvelope`: absolute mean error in the relative first-signal units.
* `commonMeanEnvelope`: one deterministic matrix per channel for the finite horizon.

## Main results

* `actualTwoSignal_mean_le_common`: both actual clipped means satisfy the common envelope.
* `commonMeanEnvelope_moment_le_cost`: absolute child costs and RAW moments pay common B.
-/
public section
noncomputable section
namespace Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
open Finset Cslib Cslib.Probability Cslib.RowCompression
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {P J : ℕ} [Fact P.Prime]

/-- First absolute input-mean envelope, in the actual relative first-signal units. -/
@[expose] def firstMeanEnvelope (R : RoleProfile J) (D : ZMod P)
    (ss st : List (ZMod P)) (ks k : ℕ)
    (input : Environment P J → Matrix (ZMod P) (ZMod P) ℝ)
    (G : Matrix (ZMod P) (ZMod P) ℝ) (x y : ZMod P) : ℝ :=
  min 1 (|rowSliceMean (retainedMask R.source (side P ks) D ss)
    (retainedMask R.terminal (side P k) D st) input x y - G x y| / (rate k + G x y))

set_option backward.isDefEq.respectTransparency false in
/-- An absolute input mean-error payment bounds the first envelope. No clipped
relative estimate is inverted, and no upper bound on the genuine residual is used. -/
theorem firstMeanEnvelope_moment_le (R : RoleProfile J) (D : ZMod P)
    (ss st : List (ZMod P)) (ks k : ℕ)
    (input : Environment P J → Matrix (ZMod P) (ZMod P) ℝ)
    (G : Matrix (ZMod P) (ZMod P) ℝ) (hG : ∀ x y, 0 ≤ G x y)
    (cost : Matrix (ZMod P) (ZMod P) ℝ)
    (he : ∀ x y, |rowSliceMean (retainedMask R.source (side P ks) D ss)
      (retainedMask R.terminal (side P k) D st) input x y - G x y| ≤ cost x y)
    {N u : ℝ} (hNu : 0 ≤ N * u) :
    rowNormPow 4 N u (retainedMask R.source (side P ks) D ss)
      (retainedMask R.terminal (side P k) D st) (fun _ => firstMeanEnvelope R D ss st ks k
        input G) ≤
    (rate k)⁻¹ ^ 4 * rowNormPow 4 N u (retainedMask R.source (side P ks) D ss)
      (retainedMask R.terminal (side P k) D st) (fun _ => cost) := by
  have hc (x y : ZMod P) : 0 ≤ cost x y := (abs_nonneg _).trans (he x y)
  have hp := row_mono_abs (retainedMask R.source (side P ks) D ss)
    (retainedMask R.terminal (side P k) D st) hNu
    (fun _ => firstMeanEnvelope R D ss st ks k input G)
    (fun _ x y => (rate k)⁻¹ * cost x y) (fun σ x y _ _ => by
      have hd : 0 < rate k + G x y := add_pos_of_pos_of_nonneg (rate_pos k) (hG x y)
      rw [abs_of_nonneg (show 0 ≤ firstMeanEnvelope R D ss st ks k input G x y from
        le_min (by norm_num) (div_nonneg (abs_nonneg _) hd.le)),
        abs_of_nonneg (mul_nonneg (inv_nonneg.mpr (rate_pos k).le) (hc x y))]
      exact (min_le_right _ _).trans ((div_le_div_of_nonneg_right (he x y) hd.le).trans
        (by simpa only [div_eq_mul_inv, mul_comm] using
          div_le_div_of_nonneg_left (hc x y) (rate_pos k) (le_add_of_nonneg_right (hG x y)))))
  rw [row_const_mul, abs_of_pos (inv_pos.mpr (rate_pos k))] at hp
  exact hp

/-- The actual per-prefix envelopes, before the finite maximum. -/
@[expose] def twoSignalMeanEnvelope (R : RoleProfile J) (D : ZMod P)
    (ss st : List (ZMod P)) (ks k ku : ℕ) (Lh Lρ ζ : ℝ)
    (input A : ℕ → Environment P J → Matrix (ZMod P) (ZMod P) ℝ)
    (G : Matrix (ZMod P) (ZMod P) ℝ) (ν : Fin 2) (i : ℕ) :
    Matrix (ZMod P) (ZMod P) ℝ :=
  if ν = 0 then firstMeanEnvelope R D ss st ks k (input (i + 1)) G else
    secondMeanEnvelope R D ss st ks k ku Lh Lρ ζ (A (i + 1)) G

/-- One actual deterministic matrix per channel, zero at an empty prefix horizon. -/
@[expose] def commonMeanEnvelope (R : RoleProfile J) (D : ZMod P)
    (ss st : List (ZMod P)) (ks k ku m : ℕ) (Lh Lρ ζ : ℝ)
    (input A : ℕ → Environment P J → Matrix (ZMod P) (ZMod P) ℝ)
    (G : Matrix (ZMod P) (ZMod P) ℝ) (ν : Fin 2) :
    Matrix (ZMod P) (ZMod P) ℝ :=
  finiteEnvelope (range m) (fun i => (2 : ℝ) ^ dyadicSlack m i)
    (twoSignalMeanEnvelope R D ss st ks k ku Lh Lρ ζ input A G ν)

/-- All common matrices are nonnegative, including an empty prefix set. -/
lemma commonMeanEnvelope_nonneg (R : RoleProfile J) (D : ZMod P)
    (ss st : List (ZMod P)) (ks k ku m : ℕ) (Lh Lρ ζ : ℝ)
    (input A : ℕ → Environment P J → Matrix (ZMod P) (ZMod P) ℝ)
    (G : Matrix (ZMod P) (ZMod P) ℝ) (ν : Fin 2) (x y : ZMod P) :
    0 ≤ commonMeanEnvelope R D ss st ks k ku m Lh Lρ ζ input A G ν x y :=
  finiteEnvelope_nonneg _ _ _ _ _

/-- At horizon zero there is no residual prefix contribution in either channel. -/
@[simp] lemma commonMeanEnvelope_zero (R : RoleProfile J) (D : ZMod P)
    (ss st : List (ZMod P)) (ks k ku : ℕ) (Lh Lρ ζ : ℝ)
    (input A : ℕ → Environment P J → Matrix (ZMod P) (ZMod P) ℝ)
    (G : Matrix (ZMod P) (ZMod P) ℝ) (ν : Fin 2) :
    commonMeanEnvelope R D ss st ks k ku 0 Lh Lρ ζ input A G ν = 0 := by
  ext x y
  change finiteEnvelope (range 0) _ _ x y = 0
  rw [range_zero]
  exact finiteEnvelope_empty _ _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- Actual completed raw walking, followed by selected preparation and the narrower
preparation walk, satisfies the common envelope. Neither mean/noise nor B is a premise. -/
theorem actualTwoSignal_mean_le_common
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (hK : 0 < HP.K)
    (D : ZMod P) (R : RoleProfile J) (ks k ku m : ℕ) (husage : k ≤ ku)
    (ss st : List (ZMod P))
    (input : ℕ → Environment P J → Matrix (ZMod P) (ZMod P) ℝ)
    (rawSteps prepSteps : ℕ → ℕ)
    {Lh Lρ : ℝ} (hLρ : 0 ≤ Lρ)
    (hh : ∀ a b, |polynomialPrepCutoff4 HP.θ a - polynomialPrepCutoff4 HP.θ b| ≤ Lh * |a - b|)
    (hρ : ∀ a b, |HP.ρ a - HP.ρ b| ≤ Lρ * |a - b|)
    (ζ : ℝ) (G : Matrix (ZMod P) (ZMod P) ℝ)
    (ν : Fin 2) (i : ℕ) (hi : i < m) (x y : ZMod P) :
    let A := fun j => conditionalWalk (retainedMask R.source (side P ks) D ss)
      (retainedMask R.terminal (side P k) D st)
      (graph R.source R.terminal R.source_terminal (side P ks) (side P k)
        (side_le P ks) (side_le P k) (fun x => CopyPadding.identifier D ss x)
        (fun y => CopyPadding.identifier D st y)) (fun _ _ => rawSteps j) (input j)
    let T := fun j σ x y => selectedPreparation HP D R st k (A j) σ x y
    let W := fun j => conditionalWalk (retainedMask R.source (side P ks) D ss)
      (retainedMask R.terminal (side P ku) D st)
      (graph R.source R.terminal R.source_terminal (side P ks) (side P ku)
        (side_le P ks) (side_le P ku) (fun x => CopyPadding.identifier D ss x)
        (fun y => CopyPadding.identifier D st y)) (fun _ _ => prepSteps j) (T j)
    |actualClippedMean HP R.source R.terminal (side P ks) (side P k) (side P ku)
      D ss st k G ζ (firstSignalIncrement A k (secondSignalIncrement W ζ))
      (fun _ _ _ _ => 0) ν i x y| ≤
      commonMeanEnvelope R D ss st ks k ku m Lh Lρ ζ input A G ν x y * 2 ^ dyadicSlack m i := by
  extract_lets A T W
  have hb := le_finiteEnvelope_mul (range m) (fun i => (2 : ℝ) ^ dyadicSlack m i)
    (twoSignalMeanEnvelope R D ss st ks k ku Lh Lρ ζ input A G ν)
    (mem_range.mpr hi) (by positivity) x y
  apply le_trans _ hb
  fin_cases ν
  · change |actualClippedMean HP R.source R.terminal (side P ks) (side P k) (side P ku)
      D ss st k G ζ (firstSignalIncrement A k (secondSignalIncrement W ζ))
      (fun _ _ _ _ => 0) 0 i x y| ≤ |firstMeanEnvelope R D ss st ks k (input (i + 1)) G x y|
    rw [actualClippedMean_first_eq]
    exact le_rfl
  · have he := actualSelectedSecondSignal_mean_le_envelope HP hK D R ks k ku husage ss st A
      (fun _ => graph R.source R.terminal R.source_terminal (side P ks) (side P ku)
        (side_le P ks) (side_le P ku) (fun x => CopyPadding.identifier D ss x)
        (fun y => CopyPadding.identifier D st y))
      (fun j _ _ => prepSteps j) A hLρ hh hρ ζ G i x y
    have hn : 0 ≤ actualClippedMean HP R.source R.terminal (side P ks) (side P k) (side P ku)
        D ss st k G ζ (firstSignalIncrement A k (secondSignalIncrement W ζ))
        (fun _ _ _ _ => 0) 1 i x y := by
      simp only [actualClippedMean, Fin.isValue, one_ne_zero, ↓reduceIte]
      positivity
    change |actualClippedMean HP R.source R.terminal (side P ks) (side P k) (side P ku)
      D ss st k G ζ (firstSignalIncrement A k (secondSignalIncrement W ζ))
      (fun _ _ _ _ => 0) 1 i x y| ≤ |secondMeanEnvelope R D ss st ks k ku Lh Lρ ζ (A (i + 1)) G x y|
    rw [abs_of_nonneg hn]
    exact he.trans (le_abs_self _)

/-- Common B fourth moments are paid by scaled ACTUAL prefix envelope moments.
The second channel keeps the narrower usage mask throughout integration. -/
theorem commonMeanEnvelope_moment_le
    (R : RoleProfile J) (D : ZMod P) (ss st : List (ZMod P))
    (ks k ku m : ℕ) (Lh Lρ ζ : ℝ)
    (input A : ℕ → Environment P J → Matrix (ZMod P) (ZMod P) ℝ)
    (G : Matrix (ZMod P) (ZMod P) ℝ) (ν : Fin 2) {N u : ℝ} (hNu : 0 ≤ N * u) :
    rowNormPow 4 N u (retainedMask R.source (side P ks) D ss)
      (retainedMask R.terminal (side P (if ν = 0 then k else ku)) D st)
      (fun _ => commonMeanEnvelope R D ss st ks k ku m Lh Lρ ζ input A G ν) ≤
    ∑ i ∈ range m, rowNormPow 4 N u (retainedMask R.source (side P ks) D ss)
      (retainedMask R.terminal (side P (if ν = 0 then k else ku)) D st)
      (fun _ x y => twoSignalMeanEnvelope R D ss st ks k ku Lh Lρ ζ input A G ν i x y /
        2 ^ dyadicSlack m i) :=
  rowNormPow_finiteEnvelope_le _ _ _ _ _ hNu

set_option backward.isDefEq.respectTransparency false in
/-- Concrete finite allocation from absolute conditional child costs and centered RAW
moments. The width/rate/gate/zeta amplification of B1 remains visible. This payment
is deliberately finite-horizon: it charges at most m copies of the larger channel budget. -/
theorem commonMeanEnvelope_moment_le_cost
    (R : RoleProfile J) (D : ZMod P) (ss st : List (ZMod P))
    (ks k ku m : ℕ) (husage : k ≤ ku)
    {Lh Lρ : ℝ} (hLh : 0 ≤ Lh) (hLρ : 0 ≤ Lρ) (ζ : ℝ)
    (input A : ℕ → Environment P J → Matrix (ZMod P) (ZMod P) ℝ)
    (G : Matrix (ZMod P) (ZMod P) ℝ) (hG : ∀ x y, 0 ≤ G x y)
    (cost : ℕ → Matrix (ZMod P) (ZMod P) ℝ)
    (he : ∀ i < m, ∀ x y, |rowSliceMean (retainedMask R.source (side P ks) D ss)
      (retainedMask R.terminal (side P k) D st) (input (i + 1)) x y - G x y| ≤ cost i x y)
    {N u childBudget rawBudget : ℝ} (hNu : 0 ≤ N * u)
    (hc : ∀ i < m, rowNormPow 4 N u (retainedMask R.source (side P ks) D ss)
      (retainedMask R.terminal (side P k) D st) (fun _ => cost i) ≤ childBudget)
    (hz : ∀ i < m, rowNormPow 4 N u (retainedMask R.source (side P ks) D ss)
      (retainedMask R.terminal (side P k) D st) (fun σ x y => A (i + 1) σ x y -
        rowSliceMean (retainedMask R.source (side P ks) D ss)
          (retainedMask R.terminal (side P k) D st) (input (i + 1)) x y) ≤ rawBudget)
    (ν : Fin 2) :
    rowNormPow 4 N u (retainedMask R.source (side P ks) D ss)
      (retainedMask R.terminal (side P (if ν = 0 then k else ku)) D st)
      (fun _ => commonMeanEnvelope R D ss st ks k ku m Lh Lρ ζ input A G ν) ≤
    m * max ((rate k)⁻¹ ^ 4 * childBudget)
      (P * (|ζ| * (Lh + Lρ) / rate k) ^ 4 * (8 * (rawBudget + childBudget))) := by
  apply (rowNormPow_finiteEnvelope_le_card_mul (range m)
    (fun i => (2 : ℝ) ^ dyadicSlack m i)
    (twoSignalMeanEnvelope R D ss st ks k ku Lh Lρ ζ input A G ν)
    (retainedMask R.source (side P ks) D ss)
    (retainedMask R.terminal (side P (if ν = 0 then k else ku)) D st) hNu
    (fun i _ => one_le_pow₀ (by norm_num)) ?_).trans_eq (by rw [card_range])
  intro i hi
  have him := mem_range.mp hi
  fin_cases ν
  · exact ((firstMeanEnvelope_moment_le R D ss st ks k (input (i + 1)) G hG
      (cost i) (he i him) hNu).trans
        (mul_le_mul_of_nonneg_left (hc i him) (by positivity))).trans (le_max_left _ _)
  · apply le_trans _ (le_max_right _ _)
    apply secondMeanEnvelope_moment_le R D ss st ks k ku husage hLh hLρ ζ
      (A (i + 1)) (rowSliceMean (retainedMask R.source (side P ks) D ss)
        (retainedMask R.terminal (side P k) D st) (input (i + 1))) G hNu (hz i him)
    apply le_trans _ (hc i him)
    apply row_mono_abs _ _ hNu
    intro σ x y _ _
    exact (he i him x y).trans (le_abs_self _)

end Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
