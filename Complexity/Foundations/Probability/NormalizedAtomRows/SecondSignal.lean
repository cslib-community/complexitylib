/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Probability.NormalizedAtomRows.FirstSignal

/-!
# Preparatory second signals on the actual usage slice

The selected preparation is evaluated on the actual incoming-normalized residual from
lower-child raw, preparation and pilot functions on one full environment. Its rank gate
uses the terminal rate, while its walk and mean use source × usage. The initial second
coordinate is literally zero. No desired mean, independence of children or numerical
recursive payment is assumed. The target remains the existing genuine joint preparation
mean; convergence of the selected input means to that target is a separate obligation.

These are original finite bridges using the existing fourth-moment adaptation of
[OpenAI2026LogSpace, Lemma 7.8, printed p. 42], revision 7ef5c0cc. Telescoping and support
proofs reuse Samuel Schlesinger's compression API. Recursive envelopes, parameter payments,
recursive estimation and native RL remain open.

## Main definitions

* `selectedResidualPreparation`: actual selected preparation of the lower-child residual.
* `secondSignalIncrement`: scaled walk differences for the second slot.

## Main results

* `actualNoiseEntry_secondSignalIncrement`: exact stationary endpoint noise.
* `actualSecondSignal_noise_le_input`: ROW contraction on the actual H4 usage graph.
* `selectedResidualPreparation_moment`: explicit finite density payment.
-/

public section

namespace Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments

open Finset Cslib Cslib.Probability Cslib.RowCompression
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable
variable {P J : ℕ} [Fact P.Prime]

/-- Actual selected dense preparation of the residual, before walk averaging. All child
functions see the same environment; dense base and zero-correction cases are inherited. -/
@[expose] def selectedResidualPreparation {q : ℕ}
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (D : ZMod P) (R : RoleProfile J)
    (l bin ks km k kb : ℕ) (ss sm st : List (ZMod P)) (Kc : ℕ) (binCutoff : ℝ → ℝ)
    (raw prep : HierarchyTask.Request q (Fin J) (ZMod P) →
      Environment P J → Matrix (ZMod P) (ZMod P) ℝ)
    (maximum : HierarchyTask.Request q (Fin J) (ZMod P) → Environment P J → ZMod P → ℝ)
    (σ : Environment P J) : Matrix (ZMod P) (ZMod P) ℝ :=
  DenseRowRecipe.preparation (polynomialPrepCutoff4 HP.θ) HP.ρ HP.K (rate k)
    (retainedMask R.terminal (side P k) D st)
    (rawIncomingNormalized HP D id R l bin ks km k kb ss sm st
      (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff Kc binCutoff raw prep maximum σ) σ

/-- The selected cutoff and gate give [0,1] even for signed, correlated residuals. -/
lemma selectedResidualPreparation_range {q : ℕ}
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (D : ZMod P) (R : RoleProfile J)
    (l bin ks km k kb : ℕ) (ss sm st : List (ZMod P)) (Kc : ℕ) (binCutoff : ℝ → ℝ)
    (raw prep : HierarchyTask.Request q (Fin J) (ZMod P) →
      Environment P J → Matrix (ZMod P) (ZMod P) ℝ)
    (maximum : HierarchyTask.Request q (Fin J) (ZMod P) → Environment P J → ZMod P → ℝ)
    (σ : Environment P J) (x y : ZMod P) :
    selectedResidualPreparation HP D R l bin ks km k kb ss sm st Kc binCutoff
      raw prep maximum σ x y ∈ Set.Icc 0 1 := by
  exact ⟨mul_nonneg (polynomialPrepCutoff4_nonneg _ _) (HP.ρ_nonneg _),
    (mul_le_of_le_one_right (polynomialPrepCutoff4_nonneg _ _) (HP.ρ_le_one _)).trans
      (polynomialPrepCutoff4_le_one _ _)⟩

/-- This rank support bound concerns the preparation input, not the averaged walk.
Walk averaging can combine different retained supports. -/
lemma selectedResidualPreparation_support {q : ℕ}
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (hK : 0 < HP.K)
    (D : ZMod P) (R : RoleProfile J)
    (l bin ks km k kb : ℕ) (ss sm st : List (ZMod P)) (Kc : ℕ) (binCutoff : ℝ → ℝ)
    (raw prep : HierarchyTask.Request q (Fin J) (ZMod P) →
      Environment P J → Matrix (ZMod P) (ZMod P) ℝ)
    (maximum : HierarchyTask.Request q (Fin J) (ZMod P) → Environment P J → ZMod P → ℝ)
    (σ : Environment P J) (x : ZMod P) :
    #{y ∈ ({y | retainedMask R.terminal (side P k) D st σ y} : Finset (ZMod P)) |
      selectedResidualPreparation HP D R l bin ks km k kb ss sm st Kc binCutoff
        raw prep maximum σ x y ≠ 0} < HP.K := by
  unfold selectedResidualPreparation DenseRowRecipe.preparation atomPrep
  exact card_filter_mul_rowGate_ne_zero_lt _ x hK (by linarith [HP.θ_pos] : 0 ≤ HP.θ / 2)
    (fun _ hd => polynomialPrepCutoff4_eq_zero HP.θ_pos hd)
    (show HP.η₂ ≤ HP.θ / 2 by
      linarith [HP.η₂_lt, HP.δ₀_lt_δ₁, HP.δ₁_lt, HP.θ_pos]) HP.ρ_zero

/-- Finite input payment with the exact joint densities and both width sums retained.
This does not imply a uniform numerical recursive budget. Empty slices contribute zero. -/
theorem selectedResidualPreparation_moment {q : ℕ}
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (D : ZMod P) (R : RoleProfile J)
    (l bin ks km k kb kt : ℕ) (ss sm st : List (ZMod P)) (Kc : ℕ) (binCutoff : ℝ → ℝ)
    (raw prep : HierarchyTask.Request q (Fin J) (ZMod P) →
      Environment P J → Matrix (ZMod P) (ZMod P) ℝ)
    (maximum : HierarchyTask.Request q (Fin J) (ZMod P) → Environment P J → ZMod P → ℝ)
    {N u : ℝ} (hNu : 0 ≤ N * u) :
    rowNormPow 4 N u (retainedMask R.source (side P ks) D ss)
      (retainedMask R.terminal (side P kt) D st)
      (fun σ x y => selectedResidualPreparation HP D R l bin ks km k kb ss sm st Kc binCutoff
        raw prep maximum σ x y) ≤
      (N * u)⁻¹ * ∑ x : ZMod P, ∑ y : ZMod P,
        (({σ : Environment P J | retainedMask R.source (side P ks) D ss σ x ∧
          retainedMask R.terminal (side P kt) D st σ y} : Finset _).dens : ℝ) := by
  rw [rowNormPow_eq_sum_dens_mul_expect]
  apply mul_le_mul_of_nonneg_left (sum_le_sum fun x _ => sum_le_sum fun y _ => ?_)
    (inv_nonneg.mpr hNu)
  apply mul_le_of_le_one_right (by positivity)
  rcases ({σ : Environment P J | retainedMask R.source (side P ks) D ss σ x ∧
    retainedMask R.terminal (side P kt) D st σ y} : Finset _).eq_empty_or_nonempty with he | he
  · rw [he]; norm_num
  apply expect_le he
  intro σ _
  have hr := selectedResidualPreparation_range HP D R l bin ks km k kb ss sm st Kc
    binCutoff raw prep maximum σ x y
  rw [abs_of_nonneg hr.1]
  exact pow_le_one₀ hr.1 hr.2

/-- Scaled second differences with prior zero at index zero. -/
@[expose] def secondSignalIncrement
    (F : ℕ → Environment P J → ZMod P → ZMod P → ℝ) (ζ : ℝ) :=
  fun σ x i y => ζ * (F (i + 1) σ x y - (if i = 0 then 0 else F i σ x y))

omit [Fact P.Prime] in
/-- The existing first increment accepts the second slot without changing its prefix. -/
lemma actualPrefix_twoSignal_first
    (F H : ℕ → Environment P J → ZMod P → ZMod P → ℝ) (k : ℕ) (ζ : ℝ)
    (i : ℕ) (σ : Environment P J) (x y : ZMod P) :
    actualPrefix (firstSignalIncrement F k (secondSignalIncrement H ζ)) (fun _ _ _ _ => 0)
      i σ x y 0 = F (i + 1) σ x y / rate k :=
  actualPrefix_firstSignalIncrement F k _ _ (by intros; rfl) i σ x y

omit [Fact P.Prime] in
/-- Telescoping the second coordinate from literal zero gives ζ times the actual walk. -/
lemma actualPrefix_twoSignal_second
    (F H : ℕ → Environment P J → ZMod P → ZMod P → ℝ) (k : ℕ) (ζ : ℝ)
    (i : ℕ) (σ : Environment P J) (x y : ZMod P) :
    actualPrefix (firstSignalIncrement F k (secondSignalIncrement H ζ)) (fun _ _ _ _ => 0)
      i σ x y 1 = ζ * H (i + 1) σ x y := by
  unfold actualPrefix
  convert uncompressed_second_telescope (fun j y => ζ * H j σ x y)
    (fun j y => (F (j + 1) σ x y - (if j = 0 then 0 else F j σ x y)) / rate k)
    (fun _ _ => 0) (by intros; rfl) i y using 1
  congr 1
  funext j z ν
  simp only [firstSignalIncrement, secondSignalIncrement]
  split_ifs <;> ring

/-- Actual two-signal zero extension persists through the uncompressed prefix and
compression. There is no support restriction on the full-rank first signal. -/
lemma actualTwoSignal_zero_off {E : Type*} [Fintype E]
    (s t : Fin J) (Ls Lt : ℕ) (D : ZMod P) (ss st : List (ZMod P))
    (graphs : ℕ → ∀ x y, RotationMap
      (RetainedPairSlice (retainedMask s Ls D ss) (retainedMask t Lt D st) x y) E)
    (times : ℕ → ZMod P → ZMod P → ℕ)
    (input F : ℕ → Environment P J → ZMod P → ZMod P → ℝ) (k : ℕ) (ζ : ℝ)
    (σ : Environment P J) (x y : ZMod P) (hy : ¬retainedMask t Lt D st σ y) :
    let H := fun j => conditionalWalk (retainedMask s Ls D ss) (retainedMask t Lt D st)
      (graphs j) (times j) (input j)
    let Δ := firstSignalIncrement F k (secondSignalIncrement H ζ)
    (∀ i, actualPrefix Δ (fun _ _ _ _ => 0) i σ x y 1 = 0) ∧
    (∀ S n K ρ m, (iterate S n K ρ (Δ σ x) ⟨0, fun _ _ => 0⟩ m).row y 1 = 0) := by
  dsimp only
  have hz (j : ℕ) := conditionalWalk_zero_off (retainedMask s Ls D ss)
    (retainedMask t Lt D st) (graphs j) (times j) (input j) σ x y hy
  constructor
  · intro i
    rw [actualPrefix_twoSignal_second, hz, mul_zero]
  · intro S n K ρ m
    apply iterate_second_zero_off S n K ρ _ _ y rfl _ m
    intro i
    simp only [firstSignalIncrement, secondSignalIncrement, Fin.isValue, one_ne_zero,
      ↓reduceIte, hz, ite_self, sub_self, mul_zero]

/-- Stationarity identifies the actual second noise on source × usage, including
empty slices. The first slot and full-rank denominator data remain arbitrary. -/
lemma actualNoiseEntry_secondSignalIncrement {E : Type*} [Fintype E] [Nonempty E]
    (s t : Fin J) (Ls La Lt : ℕ) (D : ZMod P) (ss st : List (ZMod P))
    (graphs : ℕ → ∀ x y, RotationMap
      (RetainedPairSlice (retainedMask s Ls D ss) (retainedMask t Lt D st) x y) E)
    (times : ℕ → ZMod P → ZMod P → ℕ)
    (input F : ℕ → Environment P J → ZMod P → ZMod P → ℝ)
    (k : ℕ) (ζ : ℝ) (G : Matrix (ZMod P) (ZMod P) ℝ)
    (i : ℕ) (σ : Environment P J) (x y : ZMod P) :
    let H := fun j => conditionalWalk (retainedMask s Ls D ss) (retainedMask t Lt D st)
      (graphs j) (times j) (input j)
    actualNoiseEntry s t Ls La Lt D ss st k G
      (firstSignalIncrement F k (secondSignalIncrement H ζ)) (fun _ _ _ _ => 0) 1 i σ x y =
      |ζ| * |H (i + 1) σ x y - rowSliceMean (retainedMask s Ls D ss)
        (retainedMask t Lt D st) (input (i + 1)) x y| := by
  dsimp only
  unfold actualNoiseEntry twoMaskMean
  simp only [Fin.isValue, one_ne_zero, ↓reduceIte, div_one, actualPrefix_twoSignal_second]
  unfold rowSliceMean
  rw [← mul_expect]
  change |ζ * _ - ζ * rowSliceMean _ _ (conditionalWalk _ _ _ _ _) x y| = _
  rw [rowSliceMean_conditionalWalk, ← mul_sub, abs_mul]
  rfl

/-- Exact row scaling of the actual second noise. -/
lemma actualNoiseEntry_second_row {E : Type*} [Fintype E] [Nonempty E]
    (s t : Fin J) (Ls La Lt : ℕ) (D : ZMod P) (ss st : List (ZMod P))
    (graphs : ℕ → ∀ x y, RotationMap
      (RetainedPairSlice (retainedMask s Ls D ss) (retainedMask t Lt D st) x y) E)
    (times : ℕ → ZMod P → ZMod P → ℕ)
    (input F : ℕ → Environment P J → ZMod P → ZMod P → ℝ)
    (k : ℕ) (ζ : ℝ) (G : Matrix (ZMod P) (ZMod P) ℝ) (i : ℕ) (N u : ℝ) :
    let H := fun j => conditionalWalk (retainedMask s Ls D ss) (retainedMask t Lt D st)
      (graphs j) (times j) (input j)
    rowNormPow 4 N u (retainedMask s Ls D ss) (retainedMask t Lt D st)
      (actualNoiseEntry s t Ls La Lt D ss st k G
        (firstSignalIncrement F k (secondSignalIncrement H ζ)) (fun _ _ _ _ => 0) 1 i) =
      ζ ^ 4 * rowNormPow 4 N u (retainedMask s Ls D ss) (retainedMask t Lt D st)
        (fun σ x y => H (i + 1) σ x y - rowSliceMean (retainedMask s Ls D ss)
          (retainedMask t Lt D st) (input (i + 1)) x y) := by
  dsimp only
  unfold rowNormPow
  simp_rw [actualNoiseEntry_secondSignalIncrement]
  simp only [abs_mul, abs_abs, mul_pow, ← mul_sum, ← mul_expect,
    (by decide : Even (4 : ℕ)).pow_abs ζ]
  ring

/-- The actual usage-slice graph discharges the endpoint ROW noise contract. No desired
final noise is a premise, and the input is at budget i+1 on the full shared environment. -/
theorem actualSecondSignal_noise_le_input
    (R : RoleProfile J) (ks kt : ℕ) (La : ℕ) (D : ZMod P) (ss st : List (ZMod P))
    (input F : ℕ → Environment P J → ZMod P → ZMod P → ℝ)
    (steps : ℕ → ℕ) (k : ℕ) (ζ : ℝ) (G : Matrix (ZMod P) (ZMod P) ℝ)
    {N u : ℝ} (hNu : 0 ≤ N * u) (i : ℕ) :
    let H := fun j => conditionalWalk (retainedMask R.source (side P ks) D ss)
      (retainedMask R.terminal (side P kt) D st)
      (graph R.source R.terminal R.source_terminal (side P ks) (side P kt)
        (side_le P ks) (side_le P kt) (fun x => CopyPadding.identifier D ss x)
        (fun y => CopyPadding.identifier D st y)) (fun _ _ => steps j) (input j)
    rowNormPow 4 N u (retainedMask R.source (side P ks) D ss)
      (retainedMask R.terminal (side P kt) D st)
      (actualNoiseEntry R.source R.terminal (side P ks) La (side P kt) D ss st k G
        (firstSignalIncrement F k (secondSignalIncrement H ζ)) (fun _ _ _ _ => 0) 1 i) ≤
      ζ ^ 4 * (32 * (1 - 1 / (155648 * (J + 1) * (4 : ℝ) ^ 4)) ^ (2 * steps (i + 1)) *
        rowNormPow 4 N u (retainedMask R.source (side P ks) D ss)
          (retainedMask R.terminal (side P kt) D st) (input (i + 1))) := by
  dsimp only
  have hb := noise R.source R.terminal R.source_terminal (side P ks) (side P kt)
    (side_le P ks) (side_le P kt) (fun x => CopyPadding.identifier D ss x)
    (fun y => CopyPadding.identifier D st y) hNu (steps (i + 1)) (input (i + 1))
  have heq := actualNoiseEntry_second_row R.source R.terminal (side P ks) La (side P kt)
    D ss st (fun _ => graph R.source R.terminal R.source_terminal (side P ks) (side P kt)
      (side_le P ks) (side_le P kt) (fun x => CopyPadding.identifier D ss x)
      (fun y => CopyPadding.identifier D st y)) (fun j _ _ => steps j) input F k ζ G i N u
  exact heq.trans_le (mul_le_mul_of_nonneg_left hb (by positivity))

/-- Concrete lower-child preparation client of the endpoint ROW contraction. The walk
uses the narrower usage exponent kt, while preparation ranks use k. Every budget j uses
its own genuine earlier raw/preparation/pilot functions; no desired mean is supplied. -/
theorem actualSelectedSecondSignal_noise
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (D : ZMod P) (R : RoleProfile J)
    (l bin ks km k kb kt : ℕ) (_husage : k ≤ kt)
    (ss sm st : List (ZMod P)) (Kc : ℕ) (binCutoff : ℝ → ℝ)
    (raw prep : ∀ j : ℕ, HierarchyTask.Request j (Fin J) (ZMod P) →
      Environment P J → Matrix (ZMod P) (ZMod P) ℝ)
    (maximum : ∀ j : ℕ, HierarchyTask.Request j (Fin J) (ZMod P) →
      Environment P J → ZMod P → ℝ)
    (F : ℕ → Environment P J → ZMod P → ZMod P → ℝ)
    (steps : ℕ → ℕ) (ζ : ℝ) (G : Matrix (ZMod P) (ZMod P) ℝ)
    {N u : ℝ} (hNu : 0 ≤ N * u) (i : ℕ) :
    let T := fun j σ x y => selectedResidualPreparation HP D R l bin ks km k kb ss sm st
      Kc binCutoff (raw j) (prep j) (maximum j) σ x y
    let H := fun j => conditionalWalk (retainedMask R.source (side P ks) D ss)
      (retainedMask R.terminal (side P kt) D st)
      (graph R.source R.terminal R.source_terminal (side P ks) (side P kt)
        (side_le P ks) (side_le P kt) (fun x => CopyPadding.identifier D ss x)
        (fun y => CopyPadding.identifier D st y)) (fun _ _ => steps j) (T j)
    rowNormPow 4 N u (retainedMask R.source (side P ks) D ss)
      (retainedMask R.terminal (side P kt) D st)
      (actualNoiseEntry R.source R.terminal (side P ks) (side P k) (side P kt) D ss st k G
        (firstSignalIncrement F k (secondSignalIncrement H ζ)) (fun _ _ _ _ => 0) 1 i) ≤
      ζ ^ 4 * (32 * (1 - 1 / (155648 * (J + 1) * (4 : ℝ) ^ 4)) ^ (2 * steps (i + 1)) *
        rowNormPow 4 N u (retainedMask R.source (side P ks) D ss)
          (retainedMask R.terminal (side P kt) D st) (T (i + 1))) := by
  exact actualSecondSignal_noise_le_input R ks kt (side P k) D ss st _ F steps k ζ G hNu i

end
end Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
