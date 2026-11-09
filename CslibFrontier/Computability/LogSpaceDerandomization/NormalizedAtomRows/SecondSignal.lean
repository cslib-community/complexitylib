/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.LogSpaceDerandomization.NormalizedAtomRows.FirstSignal
public import CslibFrontier.Foundations.Probability.SpectralPayment
public import CslibFrontier.Computability.LogSpaceDerandomization.GridRowMoment

/-!
# Preparatory second signals on the actual usage slice

The selected preparation is evaluated on a supplied completed raw child, including the
actual first-signal H4 walk, on one full environment. Its rank gate
uses the terminal rate, while its walk and mean use source × usage. The initial second
coordinate is literally zero. The selected input's range and rank support pay 16K on an
admitted source horizon, giving an explicit finite walk length for positive noise tolerance.
No desired mean or independence of children is assumed. The target remains the existing
genuine joint preparation mean; convergence of the selected input means to that target
is a separate obligation.

These are original finite bridges using the existing fourth-moment adaptation of
[OpenAI2026LogSpace, Lemma 7.8, printed p. 42], revision 7ef5c0cc. Telescoping and support
proofs reuse Samuel Schlesinger's compression API. Recursive child budgets and envelopes,
recursive estimation and native RL remain open.

## Main definitions

* `selectedPreparation`: selected preparation of a completed raw child.
* `rawSamplePreparation`: optional unaveraged finite client, not recursive wiring.
* `secondSignalIncrement`: scaled walk differences for the second slot.

## Main results

* `actualNoiseEntry_secondSignalIncrement`: exact stationary endpoint noise.
* `actualSecondSignal_noise_le_input`: ROW contraction on the actual H4 usage graph.
* `selectedPreparation_moment`: explicit finite joint-density payment.
* `selectedPreparation_moment_le`: support-based pre-walk payment of 16K.
* `actualSelectedSecondSignal_noise_le_dyadic`: numerical actual second-prefix budget.
-/

public section

namespace Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments

open Finset Cslib Cslib.Probability Cslib.RowCompression
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable
variable {P J : ℕ} [Fact P.Prime]

/-- Selected preparation of a supplied completed raw child in matrix units. The atom
recipe performs the sole division by rate k; a normalized first prefix must be rescaled. -/
@[expose] def selectedPreparation
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (D : ZMod P) (R : RoleProfile J)
    (st : List (ZMod P)) (k : ℕ)
    (A : Environment P J → Matrix (ZMod P) (ZMod P) ℝ) (σ : Environment P J) :
    Matrix (ZMod P) (ZMod P) ℝ :=
  DenseRowRecipe.preparation (polynomialPrepCutoff4 HP.θ) HP.ρ HP.K (rate k)
    (retainedMask R.terminal (side P k) D st) (A σ) σ

/-- Optional finite preparation of an unaveraged raw sample, not a recursive evaluator. All child
functions see the same environment; dense base and zero-correction cases are inherited. -/
@[expose] def rawSamplePreparation {q : ℕ}
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (D : ZMod P) (R : RoleProfile J)
    (l bin ks km k kb : ℕ) (ss sm st : List (ZMod P)) (Kc : ℕ) (binCutoff : ℝ → ℝ)
    (raw prep : HierarchyTask.Request q (Fin J) (ZMod P) →
      Environment P J → Matrix (ZMod P) (ZMod P) ℝ)
    (maximum : HierarchyTask.Request q (Fin J) (ZMod P) → Environment P J → ZMod P → ℝ)
    (σ : Environment P J) : Matrix (ZMod P) (ZMod P) ℝ :=
  selectedPreparation HP D R st k
    (rawIncomingNormalized HP D id R l bin ks km k kb ss sm st
      (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff Kc binCutoff raw prep maximum) σ

/-- The selected cutoff and gate give [0,1] even for signed, correlated residuals. -/
lemma selectedPreparation_range
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (D : ZMod P) (R : RoleProfile J)
    (st : List (ZMod P)) (k : ℕ)
    (A : Environment P J → Matrix (ZMod P) (ZMod P) ℝ)
    (σ : Environment P J) (x y : ZMod P) :
    selectedPreparation HP D R st k A σ x y ∈ Set.Icc 0 1 := by
  exact ⟨mul_nonneg (polynomialPrepCutoff4_nonneg _ _) (HP.ρ_nonneg _),
    (mul_le_of_le_one_right (polynomialPrepCutoff4_nonneg _ _) (HP.ρ_le_one _)).trans
      (polynomialPrepCutoff4_le_one _ _)⟩

/-- A zero completed raw child has zero preparation, irrespective of the rank slice. -/
@[simp] lemma selectedPreparation_zero
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (D : ZMod P) (R : RoleProfile J)
    (st : List (ZMod P)) (k : ℕ) (σ : Environment P J) (x y : ZMod P) :
    selectedPreparation HP D R st k (fun _ _ _ => 0) σ x y = 0 := by
  have hz := polynomialPrepCutoff4_eq_zero HP.θ_pos
    (show (0 : ℝ) ≤ HP.θ / 2 by linarith [HP.θ_pos])
  simp only [selectedPreparation, DenseRowRecipe.preparation, atomPrep, zero_div, hz, zero_mul]

/-- This rank support bound concerns the preparation input, not the averaged walk.
Walk averaging can combine different retained supports. -/
lemma selectedPreparation_support
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (hK : 0 < HP.K)
    (D : ZMod P) (R : RoleProfile J)
    (st : List (ZMod P)) (k : ℕ)
    (A : Environment P J → Matrix (ZMod P) (ZMod P) ℝ)
    (σ : Environment P J) (x : ZMod P) :
    #{y ∈ ({y | retainedMask R.terminal (side P k) D st σ y} : Finset (ZMod P)) |
      selectedPreparation HP D R st k A σ x y ≠ 0} < HP.K := by
  unfold selectedPreparation DenseRowRecipe.preparation atomPrep
  exact card_filter_mul_rowGate_ne_zero_lt _ x hK (by linarith [HP.θ_pos] : 0 ≤ HP.θ / 2)
    (fun _ hd => polynomialPrepCutoff4_eq_zero HP.θ_pos hd)
    (show HP.η₂ ≤ HP.θ / 2 by
      linarith [HP.η₂_lt, HP.δ₀_lt_δ₁, HP.δ₁_lt, HP.θ_pos]) HP.ρ_zero

/-- Finite input payment with the exact joint densities and both width sums retained.
This does not imply a uniform numerical recursive budget. Empty slices contribute zero. -/
theorem selectedPreparation_moment
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (D : ZMod P) (R : RoleProfile J)
    (ks k kt : ℕ) (ss st : List (ZMod P))
    (A : Environment P J → Matrix (ZMod P) (ZMod P) ℝ)
    {N u : ℝ} (hNu : 0 ≤ N * u) :
    rowNormPow 4 N u (retainedMask R.source (side P ks) D ss)
      (retainedMask R.terminal (side P kt) D st)
      (fun σ x y => selectedPreparation HP D R st k A σ x y) ≤
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
  have hr := selectedPreparation_range HP D R st k A σ x y
  rw [abs_of_nonneg hr.1]
  exact pow_le_one₀ hr.1 hr.2

/-- Sparsity pays for the selected input before averaging, even when the residual,
source retention and rank support depend on the same full environment. Usage is narrower
than rank. Only the source density sum remains; there is no endpoint width factor. -/
theorem selectedPreparation_support_moment
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (hK : 0 < HP.K)
    (D : ZMod P) (R : RoleProfile J)
    (ks k kt : ℕ) (husage : k ≤ kt)
    (ss st : List (ZMod P))
    (A : Environment P J → Matrix (ZMod P) (ZMod P) ℝ)
    {N u : ℝ} (hNu : 0 ≤ N * u) :
    rowNormPow 4 N u (retainedMask R.source (side P ks) D ss)
      (retainedMask R.terminal (side P kt) D st)
      (fun σ x y => selectedPreparation HP D R st k A σ x y) ≤
      HP.K * ((N * u)⁻¹ * ∑ x : ZMod P,
        (({σ : Environment P J | retainedMask R.source (side P ks) D ss σ x} :
          Finset _).dens : ℝ)) := by
  have hside : side P kt ≤ side P k := by
    rw [side_eq_ceil, side_eq_ceil]
    exact Nat.ceil_mono (mul_le_mul_of_nonneg_left
      (inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) husage)) (by positivity))
  have hcard (σ : Environment P J) (x : ZMod P) :
      #{y ∈ ({y | retainedMask R.terminal (side P kt) D st σ y} : Finset (ZMod P)) |
        selectedPreparation HP D R st k A σ x y ≠ 0} ≤ HP.K := by
    apply (card_le_card ?_).trans
      (selectedPreparation_support HP hK D R st k A σ x).le
    intro y hy
    simp only [mem_filter, mem_univ, true_and] at hy ⊢
    exact ⟨mem_retentionBox.mpr (fun a => (mem_retentionBox.mp hy.1 a).trans_le hside), hy.2⟩
  have hb := rowNormPow_le_of_card_le
    (X := retainedMask R.source (side P ks) D ss)
    (Y := retainedMask R.terminal (side P kt) D st)
    (Z := fun σ x y => selectedPreparation HP D R st k A σ x y)
    (by decide : 4 ≠ 0) hNu (by norm_num : (0 : ℝ) ≤ 1)
    (fun σ x y => by
      rw [abs_of_nonneg (selectedPreparation_range HP D R st k A σ x y).1]
      exact (selectedPreparation_range HP D R st k A σ x y).2)
    (fun σ x _ => hcard σ x)
  simpa only [one_pow, mul_one, vertexNormPow_one_eq_sum_dens] using hb

/-- On an admitted source horizon the normalized pre-walk fourth moment is at most 16K.
Only source exponent ks needs the horizon; no input/support independence is used. -/
theorem selectedPreparation_moment_le
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (hK : 0 < HP.K)
    (D : ZMod P) (R : RoleProfile J) (H : Horizon P)
    (ks k kt : ℕ) (hks : ks ≤ H.maxExponent) (husage : k ≤ kt)
    (ss st : List (ZMod P))
    (A : Environment P J → Matrix (ZMod P) (ZMod P) ℝ) :
    rowNormPow 4 P (rate ks) (retainedMask R.source (side P ks) D ss)
      (retainedMask R.terminal (side P kt) D st)
      (fun σ x y => selectedPreparation HP D R st k A σ x y) ≤ 16 * HP.K := by
  have hP : (0 : ℝ) < P := by exact_mod_cast (Fact.out : P.Prime).pos
  have hr := rate_pos ks
  have hd := side_div_pow_four_le H hks
  have hb := selectedPreparation_support_moment HP hK D R ks k kt
    husage ss st A (mul_pos hP hr).le
  rw [source_density_sum] at hb
  calc
    _ ≤ HP.K * ((↑P * rate ks)⁻¹ * (↑P * ((side P ks : ℝ) / P) ^ 4)) := hb
    _ ≤ HP.K * ((↑P * rate ks)⁻¹ * (↑P * (16 * rate ks))) := by gcongr
    _ = 16 * HP.K := by field_simp [hP.ne', hr.ne']

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
  congr 1 with j z ν : 3
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

/-- Completed-child preparation client of the endpoint ROW contraction. The walk
uses the narrower usage exponent kt, while preparation ranks use k. Every budget j uses
its own completed raw child; no desired mean is supplied. -/
theorem actualSelectedSecondSignal_noise
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (D : ZMod P) (R : RoleProfile J)
    (ks k kt : ℕ) (_husage : k ≤ kt)
    (ss st : List (ZMod P))
    (A : ℕ → Environment P J → Matrix (ZMod P) (ZMod P) ℝ)
    (F : ℕ → Environment P J → ZMod P → ZMod P → ℝ)
    (steps : ℕ → ℕ) (ζ : ℝ) (G : Matrix (ZMod P) (ZMod P) ℝ)
    {N u : ℝ} (hNu : 0 ≤ N * u) (i : ℕ) :
    let T := fun j σ x y => selectedPreparation HP D R st k (A j) σ x y
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

/-- Numerical second-noise payment for the selected completed-child preparation. The
support argument applies to T before the walk, never to its possibly dense average. -/
theorem actualSelectedSecondSignal_noise_le
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (hK : 0 < HP.K)
    (D : ZMod P) (R : RoleProfile J) (Horizon : Horizon P)
    (ks k kt : ℕ) (husage : k ≤ kt) (hks : ks ≤ Horizon.maxExponent)
    (ss st : List (ZMod P))
    (A : ℕ → Environment P J → Matrix (ZMod P) (ZMod P) ℝ)
    (F : ℕ → Environment P J → ZMod P → ZMod P → ℝ)
    (steps : ℕ → ℕ) (ζ : ℝ) (G : Matrix (ZMod P) (ZMod P) ℝ)
    (i : ℕ) :
    let T := fun j σ x y => selectedPreparation HP D R st k (A j) σ x y
    let H := fun j => conditionalWalk (retainedMask R.source (side P ks) D ss)
      (retainedMask R.terminal (side P kt) D st)
      (graph R.source R.terminal R.source_terminal (side P ks) (side P kt)
        (side_le P ks) (side_le P kt) (fun x => CopyPadding.identifier D ss x)
        (fun y => CopyPadding.identifier D st y)) (fun _ _ => steps j) (T j)
    rowNormPow 4 P (rate ks) (retainedMask R.source (side P ks) D ss)
      (retainedMask R.terminal (side P kt) D st)
      (actualNoiseEntry R.source R.terminal (side P ks) (side P k) (side P kt) D ss st k G
        (firstSignalIncrement F k (secondSignalIncrement H ζ)) (fun _ _ _ _ => 0) 1 i) ≤
      ζ ^ 4 * (32 * (1 - 1 / (155648 * (J + 1) * (4 : ℝ) ^ 4)) ^ (2 * steps (i + 1)) *
        (16 * HP.K)) := by
  have hP : (0 : ℝ) < P := by exact_mod_cast (Fact.out : P.Prime).pos
  have hb := actualSelectedSecondSignal_noise HP D R ks k kt husage
    ss st A F steps ζ G (mul_pos hP (rate_pos ks)).le i
  exact hb.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left
      (selectedPreparation_moment_le HP hK D R Horizon ks k kt hks
        husage ss st (A (i + 1)))
      (mul_nonneg (by norm_num) (by rw [pow_mul]; positivity))) (by positivity))

/-- The logarithmic step choice discharges the actual second-prefix noise budget at i+1.
First-signal payments and deterministic mean envelopes remain separate obligations. -/
theorem actualSelectedSecondSignal_noise_le_dyadic
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (hK : 0 < HP.K)
    (D : ZMod P) (R : RoleProfile J) (Horizon : Horizon P)
    (ks k kt : ℕ) (husage : k ≤ kt) (hks : ks ≤ Horizon.maxExponent)
    (ss st : List (ZMod P))
    (A : ℕ → Environment P J → Matrix (ZMod P) (ZMod P) ℝ)
    (F : ℕ → Environment P J → ZMod P → ZMod P → ℝ)
    (steps : ℕ → ℕ) (ζ : ℝ) (G : Matrix (ZMod P) (ZMod P) ℝ)
    (i m : ℕ) {ε : ℝ} (hε : 0 < ε)
    (hsteps : spectralWalkLength (1 - 1 / (155648 * (J + 1) * (4 : ℝ) ^ 4))
      (ζ ^ 4 * 512 * HP.K) ε (dyadicSlack m i) ≤ steps (i + 1)) :
    let T := fun j σ x y => selectedPreparation HP D R st k (A j) σ x y
    let H := fun j => conditionalWalk (retainedMask R.source (side P ks) D ss)
      (retainedMask R.terminal (side P kt) D st)
      (graph R.source R.terminal R.source_terminal (side P ks) (side P kt)
        (side_le P ks) (side_le P kt) (fun x => CopyPadding.identifier D ss x)
        (fun y => CopyPadding.identifier D st y)) (fun _ _ => steps j) (T j)
    rowNormPow 4 P (rate ks) (retainedMask R.source (side P ks) D ss)
      (retainedMask R.terminal (side P kt) D st)
      (actualNoiseEntry R.source R.terminal (side P ks) (side P k) (side P kt) D ss st k G
        (firstSignalIncrement F k (secondSignalIncrement H ζ)) (fun _ _ _ _ => 0) 1 i) ≤
      (ε * (64 : ℝ)⁻¹ ^ dyadicSlack m i) ^ 4 := by
  have hden : (1 : ℝ) < 155648 * (J + 1) * (4 : ℝ) ^ 4 := by
    have : (0 : ℝ) ≤ J := Nat.cast_nonneg J
    nlinarith
  have hr : 0 < 1 - 1 / (155648 * (J + 1) * (4 : ℝ) ^ 4) :=
    sub_pos.mpr ((div_lt_one (by linarith)).mpr hden)
  have hp := spectralWalkLength_payment hr (sub_lt_self _ (by positivity))
    (by positivity : 0 ≤ ζ ^ 4 * 512 * HP.K) hε (dyadicSlack m i) (steps (i + 1)) hsteps
  have hp' : ζ ^ 4 * (32 * (1 - 1 / (155648 * (J + 1) * (4 : ℝ) ^ 4)) ^
      (2 * steps (i + 1)) * (16 * HP.K)) ≤
      (ε * (64 : ℝ)⁻¹ ^ dyadicSlack m i) ^ 4 := by nlinarith only [hp]
  exact (actualSelectedSecondSignal_noise_le HP hK D R Horizon ks k kt husage
    hks ss st A F steps ζ G i).trans
      hp'

end
end Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
