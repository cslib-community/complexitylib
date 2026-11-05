/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate
public import Complexity.Foundations.Probability.HierarchyInitialPerturbation
public import Complexity.Foundations.Probability.HierarchyInitialSparseSecondNoise
public import Complexity.Foundations.Probability.HierarchyInitialIntegrated
public import Complexity.Foundations.Probability.HierarchyInitialSemanticNoise
public import Complexity.Foundations.Probability.HierarchySupportedPreparation
public import Complexity.Foundations.Probability.NormalizedAtomRows.ScheduledMeanTail
public import Complexity.Foundations.Probability.NormalizedAtomRows.ScheduleAllocation
import Complexity.Foundations.Probability.HierarchyInitialFeasibility
import Complexity.Foundations.Data.List.Blocks

/-!
# Preparation payments for computed approximate initial histories

Literal completed-group executions identify the first prefixes and preparation walks on
one environment. Their transport consumes strict lower-budget own-request rooted precision,
including separate reset-right execution. The semantic omitted/inactive deficit and
centered first noise are retained explicitly.

`initialComputedPrecisionMoment` supplies four nonnegative costs to the actual four-max,
raw clipped-error and sharp-reserve consumers. The first mean uses clipped group and
endpoint transport. The first noise combines joint-slice centered transport with the
canonical semantic payment. Both retain their previous fallbacks and structural-charge
allocations. The second mean uses saturated relative errors on the union of the two
preparation supports, with full-terminal-rank first-mean/noise inputs. The second noise
uses a sparse spectral minimum under the actual polynomial-preparation, source-horizon
and source/terminal/usage guards; the original range bound remains available.

The reserve separates deterministic heavy-event tails from unconditional centered-noise
tails and retains the literal raw false-event weights. The bounded first-coordinate
allocations live here. Uniform mean and second-mean allocations and the covered joint
four-statistic payment are supplied by the specialized allocation and reserve-assembly
modules. Their execution bridge uses the same completed groups and preparation list.
Simultaneous changing-request accuracy/availability and native logarithmic-space
realization remain separate obligations.

## Main results

* `initial_compressed_mean_moment`: transported mean discrepancy plus semantic deficit.
* `initial_compressed_prefix_absolute`: actual absolute error before preparation.
* `initial_compressed_first_noise`: centered transport with the actual conditional mean.
* `initial_compressed_preparation`: full-rank sensitivity and actual usage-walk noise.
* `exists_initial_compressed_fourMax`: the shared sharp reserve on computed histories.
* `initial_compressed_precision_reserve`: numerical reserve from own-request rooted IH.
* `initialComputedRelativeMoment_polynomial_firstNoise_le`: actual semantic minimum consumer.
* `initialComputedRelativeMoment`: denominator-retaining semantic first-noise costs.
* `initialComputedPrecisionMoment`: clipped mean and centered noise in the literal reserve.
* `initialComputedPrecisionMoment_secondMean_le`: supported relative preparation payment.
* `initialComputedPrecisionMoment_secondNoise_le`: guarded sparse preparation-noise payment.
* `initial_compressed_centered_first_noise`: correlated centered actual prefix payment.
* `initialComputedPrecisionMoment_firstNoise_exists_charge`: fixed-charge bounded noise family.
* `initialComputedNormalizedNoise_polynomial_uniform_le`: complete initial noise envelope.
* `initialComputedPrecisionMoment_firstNoise_polynomial_paid`: uniform complete noise payment.
* `initialComputedPrecisionMoment_firstNoise_weighted_le`: actual minima with semantic residuals.
* `initialComputedPrecisionMoment_firstNoise_schedule_le`: all four transported-noise allocations.
* `initialComputedFirstCoordinate_reserve_le`: first mean plus transported-noise reserve comparison.
* `initialComputedPrecisionMoment_firstNoise_polynomial_schedule`: complete noise allocations.
* `initialComputedFirstCoordinateReserve_exists_charge`: conditional first-coordinate certificate.
* `initialComputedPrecisionMoment_first_weighted_le`: weighted moments with separate deficit.
* `initialComputedPrecisionMoment_first_tail_le`: paid actual deterministic first-mean tail.
* `initialComputedPrecisionMoment_first_pre_le`: stationary floor-weighted endpoint payment.
* `initialComputedPrecisionMoment_first_final_le`: final slack-one endpoint payment.
* `initialPolynomialLoss_row_bounded_family`: positive-prefix semantic row payment.
* `initialPolynomialLoss_first_weighted_family`: full inactive first row with exponential weight.
* `initialPolynomialLoss_first_schedule_family`: literal stationary/raw/tail first-row payments.
* `initialPolynomialLoss_root_bounded_family`: common rooted semantic schedule envelope.
* `initialComputedFirstBudgets_bounded_family`: all four semantic and transport payments.
* `initialComputedFirstBudgets_exists_charge`: fixed charge for the complete first mean.
* `initialComputedFirstFinalPayment`: final semantic payment in the actual reserve.
* `initialComputedPrecisionMoment_first_final_payment_le`: computed final payment consumer.
* `initialComputedFirstFinalBudget_bounded_family`: actual final semantic budget absorption.
* `initialComputedPrecisionMoment_first_raw_le`: aggregate weighted raw endpoint payment.
* `initial_compressed_precision_clipped_first`: actual clipped first-coordinate payment.
* `initialPerturbationFactor`: target-dependent worst-pair transport payment.
* `initialComputedMoment_final_firstNoise_zero`: exact old absolute-envelope noise cost.
* `initialComputedMoment_firstNoise_not_uniform`: a uniform envelope obstruction.
-/
public section
noncomputable section
namespace Matrix.HierarchyParams.H4RankEnvironment.BudgetData
open Finset Cslib Cslib.RowCompression Cslib.Probability
open NormalizedMoments
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix retainedMask
set_option backward.isDefEq.respectTransparency false
variable {P : ℕ} [Fact P.Prime] {HP : FourthRootHierarchyParams 16 1 16 32 8}

/-- Finite matrix-unit payment: transported prefix cost plus the semantic history's
centered noise and omitted/inactive deficit. No claim that this charge is small is built in. -/
@[expose] def initialTransportMoment (B : BudgetData HP P) (M n : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (R : RoleProfile 3)
    (ks ka : ℕ) (ss st : List (ZMod P)) (ε : ℕ → ℝ) (j : ℕ) : ℝ :=
  8 * (((j + 1 : ℕ) : ℝ) ^ 3 * ∑ i ∈ range (j + 1), ε i + 8 *
          (((2 : ℝ) ^ (-B.requestPrecision M { r with usage := r.terminal }) *
            (64 / 63) * (1 / 64 : ℝ) ^ dyadicSlack (Nat.log2 M + 1) j) ^ 4 +
            rowNormPow 4 P (rate ks) (retainedMask R.source (side P ks) B.padding ss)
              (retainedMask R.terminal (side P ka) B.padding st)
              (fun _ => B.initialPolynomialLoss M n j r)))

/-- Sup norm payment for a fixed-pair inverse denominator. Unlike inverse rate alone,
this retains the target. It is a worst-pair bound, not a pair-weighted recursive IH. -/
@[expose] def initialPerturbationFactor (ka : ℕ) (G : Matrix (ZMod P) (ZMod P) ℝ) : ℝ :=
  ‖fun xy : ZMod P × ZMod P => (rate ka + G xy.1 xy.2)⁻¹‖ ^ 4

/-- The target-dependent factor never exceeds the inverse-rate payment for a
nonnegative target. A zero target somewhere can still force equality. -/
lemma initialPerturbationFactor_le (ka : ℕ) (G : Matrix (ZMod P) (ZMod P) ℝ)
    (hG : ∀ x y, 0 ≤ G x y) :
    initialPerturbationFactor ka G ≤ (rate ka)⁻¹ ^ 4 := by
  apply pow_le_pow_left₀ (norm_nonneg _)
  apply (pi_norm_le_iff_of_nonneg (inv_nonneg.mpr (rate_pos ka).le : 0 ≤ (rate ka)⁻¹)).mpr
  intro xy
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr
    (add_pos_of_pos_of_nonneg (rate_pos ka) (hG xy.1 xy.2)))]
  exact inv_anti₀ (rate_pos ka) (le_add_of_nonneg_right (hG xy.1 xy.2))

/-- A single zero target entry makes the worst-pair payment exactly inverse rate.
This explains why this refinement alone cannot give uniform absorption on sparse targets. -/
lemma initialPerturbationFactor_eq_of_zero (ka : ℕ) (G : Matrix (ZMod P) (ZMod P) ℝ)
    (hG : ∀ x y, 0 ≤ G x y) (x y : ZMod P) (hxy : G x y = 0) :
    initialPerturbationFactor ka G = (rate ka)⁻¹ ^ 4 := by
  apply le_antisymm (initialPerturbationFactor_le ka G hG)
  have hw := norm_le_pi_norm (fun xy : ZMod P × ZMod P =>
    (rate ka + G xy.1 xy.2)⁻¹) (x, y)
  simp only [hxy, add_zero, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (rate_pos ka))] at hw
  exact pow_le_pow_left₀ (inv_nonneg.mpr (rate_pos ka).le) hw 4

/-- Constant positive targets expose a strict gain, without asserting that such a lower
bound holds for every admissible matrix. -/
lemma initialPerturbationFactor_const (ka : ℕ) (g : ℝ) :
    initialPerturbationFactor (P := P) ka (fun _ _ => g) = |(rate ka + g)⁻¹| ^ 4 := by
  simp [initialPerturbationFactor, Real.norm_eq_abs]

/-- Centered first noise of the literal computed prefixes. The transported perturbation
is centered at its own conditional mean before adding the semantic completion noise.
Both payments are unconditional; no heavy-event rarity factor is applied to noise.
Returns the absolute payment and a denominator-retaining semantic group payment. -/
theorem initial_compressed_first_noise
    (B : BudgetData HP P) (M : ℕ) (hM : 0 < M) (hbins : B.bins.Nonempty)
    (exponent : HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℕ) (ζ floor : ℝ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (R : RoleProfile 3)
    (ks ka : ℕ) (ss st : List (ZMod P))
    (hs : r.source = gridChannel R.source ks ss)
    (ht : r.terminal = gridChannel R.terminal ka st)
    (A C : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ) (ε : ℕ → ℝ)
    (hA : ∀ j < Nat.log2 M + 1,
      B.completedGroup (fun m q => if m < M then B.compressedHistory exponent ζ floor m q
        else none) M (dyadicSlack (Nat.log2 M + 1) j) (.pilotInput ⟨0, HP.k_pos⟩)
        { r with usage := r.terminal } = some (A j))
    (hCrun : ∀ j < Nat.log2 M + 1,
      B.completedGroup (fun m q => if m < M then B.evaluate m q else none)
        M (dyadicSlack (Nat.log2 M + 1) j) (.pilotInput ⟨0, HP.k_pos⟩)
        { r with usage := r.terminal } = some (C j))
    (herr : ∀ j < Nat.log2 M + 1, rowNormPow 4 P r.source.rate
      (fun σ x => r.source.retains (channels B.padding) σ x)
      (fun σ y => r.terminal.retains (channels B.padding) σ y) (A j - C j) ≤ ε j) :
    ∃ groups,
      (List.range (Nat.log2 M + 1)).mapM (fun j =>
        B.completedGroup (fun m q => if m < M then B.compressedHistory exponent ζ floor m q
          else none) M (dyadicSlack (Nat.log2 M + 1) j) (.pilotInput ⟨0, HP.k_pos⟩)
          { r with usage := r.terminal }) = some groups ∧
      let F := fun p σ x y => ((groups.take p).map (fun T => T σ x y)).sum
      ∀ j < Nat.log2 M + 1, ∀ (G : Matrix (ZMod P) (ZMod P) ℝ),
        (∀ x y, 0 ≤ G x y) → ∀ (Lt : ℕ)
          (second : Environment P 3 → ZMod P → ℕ → ZMod P → ℝ),
        rowNormPow 4 P r.source.rate
          (retainedMask R.source (side P ks) B.padding ss)
          (retainedMask R.terminal (side P ka) B.padding st)
          (actualNoiseEntry R.source R.terminal (side P ks) (side P ka) Lt B.padding ss st
            ka G (firstSignalIncrement F ka second) 0 0 j) ≤
          (rate ka)⁻¹ ^ 4 * (8 * (16 *
            (((j + 1 : ℕ) : ℝ) ^ 3 * ∑ i ∈ range (j + 1), ε i) +
            (((2 : ℝ) ^ (-B.requestPrecision M { r with usage := r.terminal }) * (64 / 63)) *
              (1 / 64 : ℝ) ^ dyadicSlack (Nat.log2 M + 1) j) ^ 4)) ∧
        rowNormPow 4 P r.source.rate
          (retainedMask R.source (side P ks) B.padding ss)
          (retainedMask R.terminal (side P ka) B.padding st)
          (actualNoiseEntry R.source R.terminal (side P ks) (side P ka) Lt B.padding ss st
            ka G (firstSignalIncrement F ka second) 0 0 j) ≤
          8 * (16 * initialPerturbationFactor ka G *
            (((j + 1 : ℕ) : ℝ) ^ 3 * ∑ i ∈ range (j + 1), ε i) +
              B.initialRelativeNoiseBudget M r R.source R.terminal R.source_terminal
                ks ka ss st G (j + 1)) := by
  have hsr : 0 ≤ r.source.rate := by rw [hs]; exact (rate_pos ks).le
  obtain ⟨groups, reference, hgroups, href, hpref, _⟩ :=
    B.initial_compressed_prefix_error exponent ζ floor M { r with usage := r.terminal }
      hsr A C ε hA hCrun herr
  let F : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ :=
    fun p σ x y => ((groups.take p).map (fun T => T σ x y)).sum
  let G : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ :=
    fun p σ x y => ((reference.take p).map (fun T => T σ x y)).sum
  have hG : B.initialPrefixes M r = some G := by
    unfold initialPrefixes
    rw [href]
    rfl
  refine ⟨groups, hgroups, ?_⟩
  change ∀ j < Nat.log2 M + 1, _
  intro j hj target htarget Lt second
  have hNu : 0 ≤ (P : ℝ) * r.source.rate := mul_nonneg (Nat.cast_nonneg _) hsr
  have hdiff := hpref (j + 1) (by omega)
  simp only [ht, hs, gridChannel, CorrectionRowTask.Channel.retains, channels,
    semanticSide_grid] at hdiff
  have hnoise := B.initialPrefix_noise_dyadic M hM hbins r R.source R.terminal
    R.source_terminal ks ka ss st hs ht G hG (j + 1) (by omega)
  dsimp only at hnoise
  simp only [Nat.add_sub_cancel] at hnoise
  have hb := rowNormPow_centered_fourth_le hNu
    (retainedMask R.source (side P ks) B.padding ss)
    (retainedMask R.terminal (side P ka) B.padding st) (F (j + 1)) (G (j + 1))
  have hn := actualNoiseEntry_first_prefix_row_le R.source R.terminal
    (side P ks) (side P ka) Lt B.padding ss st F ka target htarget second 0
    (by intros; rfl) j hNu
  constructor
  · apply hn.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply hb.trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 8)
    apply add_le_add
    · apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 16)
      convert hdiff using 1
      congr 8
      exact congrArg (fun c => c.rate) hs
    · convert hnoise using 1; congr 8
  · rw [actualNoiseEntry_first_prefix_row_eq R.source R.terminal
      (side P ks) (side P ka) Lt B.padding ss st F ka target htarget second 0
      (by intros; rfl) j P r.source.rate]
    let normed := fun (T : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ) σ x y =>
      T σ x y / (rate ka + target x y)
    have hc := rowNormPow_centered_fourth_le hNu
      (retainedMask R.source (side P ks) B.padding ss)
      (retainedMask R.terminal (side P ka) B.padding st)
      (normed (F (j + 1))) (normed (G (j + 1)))
    apply hc.trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 8)
    apply add_le_add
    · rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 16)
      have hdifference : rowNormPow 4 P r.source.rate
          (retainedMask R.source (side P ks) B.padding ss)
          (retainedMask R.terminal (side P ka) B.padding st)
          (F (j + 1) - G (j + 1)) ≤
          ((j + 1 : ℕ) : ℝ) ^ 3 * ∑ i ∈ range (j + 1), ε i := by
        convert hdiff using 1
        congr 8
        exact congrArg (fun c => c.rate) hs
      have hw := rowNormPow_mul_le_pi_norm hNu
        (retainedMask R.source (side P ks) B.padding ss)
        (retainedMask R.terminal (side P ka) B.padding st)
        (F (j + 1) - G (j + 1))
        (fun xy : ZMod P × ZMod P => (rate ka + target xy.1 xy.2)⁻¹)
      have he : normed (F (j + 1)) - normed (G (j + 1)) =
          (fun σ x y => (F (j + 1) - G (j + 1)) σ x y *
            (rate ka + target x y)⁻¹) := by
        funext σ x y
        dsimp only [normed, Pi.sub_apply, Matrix.sub_apply]
        ring
      rw [he]
      exact hw.trans (mul_le_mul_of_nonneg_left hdifference (by positivity))
    · have href := B.initialPrefix_relative_noise M hM hbins r R.source R.terminal
        R.source_terminal ks ka ss st hs ht G hG target (j + 1)
      simpa only [normed, rowSliceMean, ← expect_div, ← sub_div] using href

/-- Four explicit row-moment costs for computed initial history: deterministic first
mean/deficit, preparation mean, centered first noise, and usage noise. Bin importance
and prefix cubes enter through the executed group charges ε, without parent accuracy. -/
@[expose] def initialComputedMoment (B : BudgetData HP P) (M n : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (R : RoleProfile 3)
    (ks ka : ℕ) (ss st : List (ZMod P)) (ε : ℕ → ℝ) (ζ Lh Lρ : ℝ)
    (j : ℕ) (noise : Bool) (ν : Fin 2) : ℝ :=
  let T := ((j + 1 : ℕ) : ℝ) ^ 3 * ∑ i ∈ range (j + 1), ε i
  let Z := (((2 : ℝ) ^ (-B.requestPrecision M { r with usage := r.terminal }) * (64 / 63)) *
    (1 / 64 : ℝ) ^ dyadicSlack (Nat.log2 M + 1) j) ^ 4
  if noise then
    if ν = 0 then (rate ka)⁻¹ ^ 4 * (8 * (16 * T + Z)) else
      (|ζ| * (2 : ℝ) ^ (-B.requestPrecision M r) *
        (1 / 64 : ℝ) ^ dyadicSlack (Nat.log2 M + 1) j) ^ 4
  else if ν = 0 then (rate ka)⁻¹ ^ 4 * (8 * (T +
    rowNormPow 4 P (rate ks) (retainedMask R.source (side P ks) B.padding ss)
      (retainedMask R.terminal (side P ka) B.padding st)
      (fun _ => B.initialPolynomialLoss M n j r))) else
    P * (|ζ| * (Lh + Lρ) / rate ka) ^ 4 *
      B.initialTransportMoment M n r R ks ka ss st ε j

/-- Nonnegative group payments produce nonnegative costs for each of the four moments. -/
lemma initialComputedMoment_nonneg (B : BudgetData HP P) (M n : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (R : RoleProfile 3)
    (ks ka : ℕ) (ss st : List (ZMod P)) (ε : ℕ → ℝ) (hε : ∀ i, 0 ≤ ε i)
    (ζ Lh Lρ : ℝ) (j : ℕ) (noise : Bool) (ν : Fin 2) :
    0 ≤ B.initialComputedMoment M n r R ks ka ss st ε ζ Lh Lρ j noise ν := by
  have hs := sum_nonneg (fun i (_ : i ∈ range (j + 1)) => hε i)
  have hr := rate_pos ks
  have hnorm := rowNormPow_nonneg (s := 4)
    (X := retainedMask R.source (side P ks) B.padding ss)
    (Y := retainedMask R.terminal (side P ka) B.padding st)
    (mul_nonneg (Nat.cast_nonneg P) hr.le) (fun _ => B.initialPolynomialLoss M n j r)
  unfold initialComputedMoment initialTransportMoment
  split_ifs <;> positivity

/-- Computed four-statistic payment retaining pairwise semantic normalization. Only the
first noise is sharpened; taking the minimum preserves the previous absolute payment.
The transported error pays the target-dependent worst-pair inverse denominator.
No pair-weighted IH or global absorption is claimed. -/
@[expose] def initialComputedRelativeMoment (B : BudgetData HP P) (M n : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (R : RoleProfile 3)
    (ks ka : ℕ) (ss st : List (ZMod P)) (ε : ℕ → ℝ) (ζ Lh Lρ : ℝ)
    (j : ℕ) (noise : Bool) (ν : Fin 2) : ℝ :=
  let old := B.initialComputedMoment M n r R ks ka ss st ε ζ Lh Lρ j noise ν
  if noise ∧ ν = 0 then min old
    (8 * (16 * initialPerturbationFactor ka B.base *
      (((j + 1 : ℕ) : ℝ) ^ 3 * ∑ i ∈ range (j + 1), ε i) +
      B.initialRelativeNoiseBudget M r R.source R.terminal R.source_terminal
        ks ka ss st B.base (j + 1))) else old

/-- The literal computed first-noise minimum consumes the polynomial semantic payment.
The transported child charge is retained unchanged and is not paid by this theorem. -/
theorem initialComputedRelativeMoment_polynomial_firstNoise_le (B : BudgetData HP P)
    (hrate : B.binRate = rate)
    (hcutoff : B.cutoff = fun i => boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1)
      rate 1 i (fun _ => 1))
    (H : Horizon P) (hb : ∀ i ∈ B.bins, i ≤ H.maxExponent)
    (M n : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (R : RoleProfile 3)
    (ks ka : ℕ) (ss st : List (ZMod P))
    (hs : r.source = gridChannel R.source ks ss)
    (ht : r.terminal = gridChannel R.terminal ka st) (ha : ka ≤ H.maxExponent)
    (hC : ∀ x y, 0 ≤ B.base x y) (hC1 : B.base *ᵥ 1 ≤ 1)
    (ε : ℕ → ℝ) (ζ Lh Lρ : ℝ) (j : ℕ) :
    let m := Nat.log2 M + 1
    let q := { r with usage := r.terminal }
    B.initialComputedRelativeMoment M n r R ks ka ss st ε ζ Lh Lρ j true 0 ≤
      min (B.initialComputedMoment M n r R ks ka ss st ε ζ Lh Lρ j true 0)
        (8 * (16 * initialPerturbationFactor ka B.base *
          (((j + 1 : ℕ) : ℝ) ^ 3 * ∑ i ∈ range (j + 1), ε i) +
          (256 * B.binCap) ^ 4 * ((min (j + 1) m : ℕ) ^ (3 : ℕ) *
            ∑ i ∈ range (min (j + 1) m),
              ((2 : ℝ) ^ (-B.requestPrecision M q) *
                (64 : ℝ)⁻¹ ^ dyadicSlack m i) ^ 4))) := by
  dsimp only
  simp only [initialComputedRelativeMoment, Fin.isValue]
  apply min_le_min_left
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply add_le_add le_rfl
  exact B.initialRelativeNoiseBudget_polynomial_le hrate hcutoff H hb M r
    R.source R.terminal R.source_terminal ks ka ss st hs ht ha hC hC1 (j + 1)

/-- Nonnegative input payments give nonnegative sharpened costs. -/
lemma initialComputedRelativeMoment_nonneg (B : BudgetData HP P) (M n : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (hr : 0 ≤ r.source.rate)
    (R : RoleProfile 3) (ks ka : ℕ) (ss st : List (ZMod P)) (ε : ℕ → ℝ)
    (hε : ∀ i, 0 ≤ ε i) (ζ Lh Lρ : ℝ) (j : ℕ) (noise : Bool) (ν : Fin 2) :
    0 ≤ B.initialComputedRelativeMoment M n r R ks ka ss st ε ζ Lh Lρ j noise ν := by
  have hold := B.initialComputedMoment_nonneg M n r R ks ka ss st ε hε ζ Lh Lρ j noise ν
  have hrel := B.initialRelativeNoiseBudget_nonneg M r hr R.source R.terminal
    R.source_terminal ks ka ss st B.base (j + 1)
  have hsum := sum_nonneg (fun i (_ : i ∈ range (j + 1)) => hε i)
  unfold initialComputedRelativeMoment initialPerturbationFactor
  split_ifs <;> positivity

/-- Even with no transported child error, the final semantic first-noise payment has
this exact coefficient relative to its own parent precision. Increasing `M` alone does
not shrink the ratio: `rate ka = 2^(-4*ka)` leaves a factor `2^(16*ka)`.
This is an identity for the numerical envelope, not a lower bound on actual noise. -/
theorem initialComputedMoment_final_firstNoise_zero (B : BudgetData HP P) (M n : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (R : RoleProfile 3)
    (ks ka : ℕ) (ss st : List (ZMod P)) (ζ Lh Lρ : ℝ) :
    B.initialComputedMoment M n r R ks ka ss st (fun _ => 0) ζ Lh Lρ
      (Nat.log2 M) true 0 =
      (8 / 63 ^ 4 : ℝ) * ((2 : ℝ) ^ ka) ^ 16 *
        ((2 : ℝ) ^ (-B.requestPrecision M { r with usage := r.terminal })) ^ 4 := by
  simp only [initialComputedMoment, sum_const_zero, mul_zero, ↓reduceIte,
    dyadicSlack_last, pow_one, zero_add, rate, inv_pow, inv_inv]
  ring

/-- No statistical-budget threshold absorbs this envelope by one coefficient uniform
in the terminal exponent. The exponent is chosen before the budget and request; no
changing-request IH is assumed or refuted. Here `ka` is independent of `r.terminal`:
there is no admissibility, horizon/prime bound or successful-execution guard. This does
not give a counterexample on valid recursive calls. Sharper actual conditional-noise
analysis is needed to use this route for the simultaneous invariant. -/
theorem initialComputedMoment_firstNoise_not_uniform (B : BudgetData HP P) (A : ℝ) :
    ∃ ka : ℕ, ∀ (M n : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
      (R : RoleProfile 3) (ks : ℕ) (ss st : List (ZMod P)) (ζ Lh Lρ : ℝ),
      A * ((2 : ℝ) ^ (-B.requestPrecision M { r with usage := r.terminal })) ^ 4 <
        B.initialComputedMoment M n r R ks ka ss st (fun _ => 0) ζ Lh Lρ
          (Nat.log2 M) true 0 := by
  obtain ⟨ka, hk⟩ := pow_unbounded_of_one_lt (A / (8 / 63 ^ 4))
    (by norm_num : (1 : ℝ) < 2 ^ 16)
  rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 8 / 63 ^ 4)] at hk
  rw [← pow_mul, Nat.mul_comm 16 ka, pow_mul] at hk
  refine ⟨ka, ?_⟩
  intro M n r R ks ss st ζ Lh Lρ
  rw [B.initialComputedMoment_final_firstNoise_zero]
  exact mul_lt_mul_of_pos_right (by simpa only [mul_comm] using hk) (by positivity)

/-- Nonnegative transported costs can only increase the final semantic noise charge.
Its parent-normalized coefficient is independent of the statistical budget. -/
theorem initialComputedMoment_final_firstNoise_ge (B : BudgetData HP P) (M n : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (R : RoleProfile 3)
    (ks ka : ℕ) (ss st : List (ZMod P)) (ε : ℕ → ℝ) (hε : ∀ i, 0 ≤ ε i)
    (ζ Lh Lρ : ℝ) :
    (8 / 63 ^ 4 : ℝ) * ((2 : ℝ) ^ ka) ^ 16 *
        ((2 : ℝ) ^ (-B.requestPrecision M { r with usage := r.terminal })) ^ 4 ≤
      B.initialComputedMoment M n r R ks ka ss st ε ζ Lh Lρ (Nat.log2 M) true 0 := by
  rw [← B.initialComputedMoment_final_firstNoise_zero M n r R ks ka ss st ζ Lh Lρ]
  have hsum := sum_nonneg (fun i (_ : i ∈ range (Nat.log2 M + 1)) => hε i)
  simp only [initialComputedMoment, sum_const_zero, mul_zero, ↓reduceIte, zero_add]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 8)
  exact le_add_of_nonneg_left (by positivity)

/-- This scalar envelope retains a nondecaying final-noise coefficient even after all
three sharp repairs. In particular a depth-only fixed-request limit cannot establish a
single recursive constant for unbounded terminal exponents. This is an envelope lower
bound; actual error might be much smaller. The raw/width/tail terms are still present. -/
theorem initialComputedNumericalReserve_ge_noise (B : BudgetData HP P) (M n : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (R : RoleProfile 3)
    (ks ka : ℕ) (ss st : List (ZMod P)) (ε : ℕ → ℝ) (hε : ∀ i, 0 ≤ ε i)
    (ζ Lh Lρ floor cap C Cpre : ℝ) :
    let a := fun j noise ν =>
      B.initialComputedMoment M n r R ks ka ss st ε ζ Lh Lρ j noise ν ^ (4⁻¹ : ℝ)
    128 * (HP.K : ℝ) * C ^ 4 *
        ((8 / 63 ^ 4 : ℝ) * ((2 : ℝ) ^ ka) ^ 16 *
          ((2 : ℝ) ^ (-B.requestPrecision M { r with usage := r.terminal })) ^ 4) ≤
      initialNumericalReserve HP M floor cap C Cpre
        (fun j => (a j false 0 + a j false 1) + (a j true 0 + a j true 1)) := by
  dsimp only
  let cost := B.initialComputedMoment M n r R ks ka ss st ε ζ Lh Lρ (Nat.log2 M)
  have hc (noise : Bool) (ν : Fin 2) : 0 ≤ cost noise ν :=
    B.initialComputedMoment_nonneg M n r R ks ka ss st ε hε ζ Lh Lρ _ noise ν
  have ha (noise : Bool) (ν : Fin 2) : 0 ≤ cost noise ν ^ (4⁻¹ : ℝ) :=
    Real.rpow_nonneg (hc noise ν) _
  have hpow : cost true 0 ≤
      ((cost false 0 ^ (4⁻¹ : ℝ) + cost false 1 ^ (4⁻¹ : ℝ)) +
        (cost true 0 ^ (4⁻¹ : ℝ) + cost true 1 ^ (4⁻¹ : ℝ))) ^ 4 := by
    calc
      _ = (cost true 0 ^ (4⁻¹ : ℝ)) ^ 4 :=
        (Real.rpow_inv_natCast_pow (hc true 0) (by decide : 4 ≠ 0)).symm
      _ ≤ _ := pow_le_pow_left₀ (ha true 0)
        (by linarith [ha false 0, ha false 1, ha true 1]) 4
  exact (mul_le_mul_of_nonneg_left
    ((B.initialComputedMoment_final_firstNoise_ge M n r R ks ka ss st ε hε ζ Lh Lρ).trans
      hpow) (by positivity)).trans
    (initialNumericalReserve_ge_final HP M floor cap C Cpre
      (fun j =>
        (B.initialComputedMoment M n r R ks ka ss st ε ζ Lh Lρ j false 0 ^ (4⁻¹ : ℝ) +
          B.initialComputedMoment M n r R ks ka ss st ε ζ Lh Lρ j false 1 ^ (4⁻¹ : ℝ)) +
        (B.initialComputedMoment M n r R ks ka ss st ε ζ Lh Lρ j true 0 ^ (4⁻¹ : ℝ) +
          B.initialComputedMoment M n r R ks ka ss st ε ζ Lh Lρ j true 1 ^ (4⁻¹ : ℝ))))

/-- Exact spectral payment for an actual centered completed-group discrepancy.
The input retains its literal endpoint charge; in particular equal pairs cost zero. -/
@[expose] def initialCenteredGroupCharge (B : BudgetData HP P) (M d : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (coefficient : ℝ) : ℝ :=
  32 * (1 - 1 / (155648 * (3 + 1) * (4 : ℝ)^4)) ^ (2 * B.steps M r d) *
    B.initialRootGroupCharge M d r coefficient

/-- Centered input payments are nonnegative without a recursive availability premise. -/
lemma initialCenteredGroupCharge_nonneg (B : BudgetData HP P) (M d : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (coefficient : ℝ) :
    0 ≤ B.initialCenteredGroupCharge M d r coefficient := by
  unfold initialCenteredGroupCharge
  exact mul_nonneg (by positivity) (B.initialRootGroupCharge_nonneg M d r coefficient)

/-- The unchanged six-unit walk margin pays a five-unit active envelope. This
bounded bin family has no field-width factor. Positive parent precision is explicit. -/
theorem initialCenteredGroupCharge_bounded (B : BudgetData HP P)
    (hcharge : 0 ≤ B.rankCharge) (hrate : B.binRate = rate) (H : Horizon P)
    (M d ks ka L : ℕ) (ha : ka ≤ H.maxExponent)
    (hi : ∀ bin ∈ B.bins, bin ≤ H.maxExponent) (hc : #B.bins ≤ L + 1)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka)
    (htask : r.task = .row 0 (.pilotInput ⟨0, HP.k_pos⟩))
    (hp : 0 ≤ B.requestPrecision M r) (coefficient : ℝ) :
    B.initialCenteredGroupCharge M d r coefficient ≤
      (16 * ((L + 1 : ℕ) : ℝ) ^ 4 *
        (16 ^ 4 * (4 * (2 * B.binCap) ^ ((3 : ℝ) / 4)) ^ 4)) *
      (|coefficient| * (2 : ℝ) ^ (-B.requestPrecision M r) *
        (2 : ℝ) ^ (-B.rankCharge) * (1 / 2 : ℝ) ^ d) ^ 4 := by
  let e := (2 : ℝ) ^ (-B.requestPrecision M r)
  let a := (2 : ℝ) ^ (-B.rankCharge)
  let K := 16 * ((L + 1 : ℕ) : ℝ) ^ 4 *
    (16 ^ 4 * (4 * (2 * B.binCap) ^ ((3 : ℝ) / 4)) ^ 4)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have he : e ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have hactive := B.initialRootGroupCharge_le_active hcharge hrate M d ks ka r hs ht
    htask coefficient
  have hbound := B.initialActiveRootGroupCharge_bounded hrate H M d ka L ha hi hc r ht coefficient
  have hgap := B.initial_completion_gap_payment M d ks r hs
  have hb := (mul_le_mul_of_nonneg_left (hactive.trans hbound)
    (show 0 ≤ 32 * (1 - 1 / (155648 * (3 + 1) * (4 : ℝ)^4)) ^
      (2 * B.steps M r d) by positivity)).trans
    (mul_le_mul_of_nonneg_right hgap
      (show 0 ≤ K * (coefficient ^ 4 * (e * a * (32 : ℝ) ^ d) ^ 4) by
        dsimp only [K, e, a]; positivity))
  have hprod : (64 : ℝ)⁻¹ ^ d * (32 : ℝ) ^ d = (1 / 2 : ℝ) ^ d := by
    rw [← mul_pow]
    norm_num
  have heq : (e * (64 : ℝ)⁻¹ ^ d) ^ 4 *
      (K * (coefficient ^ 4 * (e * a * (32 : ℝ) ^ d) ^ 4)) =
      K * (|coefficient| * e * a * (1 / 2 : ℝ) ^ d * e) ^ 4 := by
    rw [show (1 / 2 : ℝ) ^ d = (64 : ℝ)⁻¹ ^ d * (32 : ℝ) ^ d from hprod.symm,
      mul_pow, mul_pow, mul_pow, mul_pow, mul_pow, mul_pow, mul_pow]
    rw [show |coefficient| ^ 4 = coefficient ^ 4 from (by decide : Even (4 : ℕ)).pow_abs _]
    ring
  change B.initialCenteredGroupCharge M d r coefficient ≤
    K * (|coefficient| * e * a * (1 / 2 : ℝ) ^ d) ^ 4
  apply hb.trans
  rw [heq]
  apply mul_le_mul_of_nonneg_left _ hK
  apply pow_le_pow_left₀ (by dsimp only [e, a]; positivity)
  exact mul_le_of_le_one_right (by dsimp only [e, a]; positivity) he

/-- Correlated first-noise transport is summed after centering on the original joint
slice. Semantic noise retains its existing separate payment. -/
@[expose] def initialComputedBoundedCenteredNoise (B : BudgetData HP P) (M : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (R : RoleProfile 3)
    (ks ka : ℕ) (ss st : List (ZMod P)) (coefficient : ℝ) (j : ℕ) : ℝ :=
  8 * (initialPerturbationFactor ka B.base *
    (∑ i ∈ range (j + 1),
      B.initialCenteredGroupCharge M (dyadicSlack (Nat.log2 M + 1) i)
        { r with usage := r.terminal } coefficient ^ (4⁻¹ : ℝ)) ^ 4 +
    B.initialRelativeNoiseBudget M r R.source R.terminal R.source_terminal
      ks ka ss st B.base (j + 1))

/-- Both summands retain nonnegative exact finite payments. -/
lemma initialComputedBoundedCenteredNoise_nonneg (B : BudgetData HP P) (M : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (hr : 0 ≤ r.source.rate)
    (R : RoleProfile 3) (ks ka : ℕ) (ss st : List (ZMod P)) (coefficient : ℝ) (j : ℕ) :
    0 ≤ B.initialComputedBoundedCenteredNoise M r R ks ka ss st coefficient j := by
  have hn := B.initialRelativeNoiseBudget_nonneg M r hr R.source R.terminal
    R.source_terminal ks ka ss st B.base (j + 1)
  unfold initialComputedBoundedCenteredNoise initialPerturbationFactor
  positivity

/-- A priori constant for a bounded full-bin/terminal family. It depends on the
primitive range, child coefficient and family bound, before field width or requests. -/
@[expose] def initialCenteredNoiseConstant (binCap coefficient : ℝ) (L : ℕ) : ℝ :=
  (rate L)⁻¹ * 2 *
    (16 * ((L + 1 : ℕ) : ℝ) ^ 4 *
      ((16 : ℝ) ^ 4 * (4 * (2 * binCap) ^ ((3 : ℝ) / 4)) ^ 4)) ^ (4⁻¹ : ℝ) *
    |coefficient|

/-- The actual first-noise payment has geometric decay under the unchanged steps.
Only transported noise uses this constant; semantic relative noise is kept separate.
The explicit bounded family is uniform in positive precision and field width. -/
theorem initialComputedBoundedCenteredNoise_bounded (B : BudgetData HP P)
    (hcharge : 0 ≤ B.rankCharge) (hrate : B.binRate = rate) (H : Horizon P)
    (M j ks ka L : ℕ) (hj : j < Nat.log2 M + 1) (hka : ka ≤ L)
    (ha : ka ≤ H.maxExponent) (hi : ∀ bin ∈ B.bins, bin ≤ H.maxExponent)
    (hc : #B.bins ≤ L + 1)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka)
    (htask : r.task = .row 0 (.pilotInput ⟨0, HP.k_pos⟩))
    (hp : 0 ≤ B.requestPrecision M { r with usage := r.terminal })
    (hbase : ∀ x y, 0 ≤ B.base x y)
    (R : RoleProfile 3) (ss st : List (ZMod P)) (coefficient : ℝ) :
    B.initialComputedBoundedCenteredNoise M r R ks ka ss st coefficient j ≤
      8 * ((initialCenteredNoiseConstant B.binCap coefficient L *
        (2 : ℝ) ^ (-B.rankCharge) *
        (2 : ℝ) ^ (-B.requestPrecision M { r with usage := r.terminal }) *
        (1 / 2 : ℝ) ^ dyadicSlack (Nat.log2 M + 1) j) ^ 4 +
        B.initialRelativeNoiseBudget M r R.source R.terminal R.source_terminal
          ks ka ss st B.base (j + 1)) := by
  have hrateL := rate_pos L
  have hratea := rate_pos ka
  let q := { r with usage := r.terminal }
  let K := 16 * ((L + 1 : ℕ) : ℝ) ^ 4 *
    ((16 : ℝ) ^ 4 * (4 * (2 * B.binCap) ^ ((3 : ℝ) / 4)) ^ 4)
  let e := (2 : ℝ) ^ (-B.requestPrecision M q)
  let a := (2 : ℝ) ^ (-B.rankCharge)
  let T := K ^ (4⁻¹ : ℝ) * |coefficient| * e * a
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hT : 0 ≤ T := by dsimp only [T, e, a]; positivity
  have hr (i : ℕ) : B.initialCenteredGroupCharge M
      (dyadicSlack (Nat.log2 M + 1) i) q coefficient ^ (4⁻¹ : ℝ) ≤
      T * (1 / 2 : ℝ) ^ dyadicSlack (Nat.log2 M + 1) i := by
    have hb := B.initialCenteredGroupCharge_bounded hcharge hrate H M
      (dyadicSlack (Nat.log2 M + 1) i) ks ka L ha hi hc q hs ht htask hp coefficient
    have h := Real.rpow_le_rpow (B.initialCenteredGroupCharge_nonneg _ _ _ _) hb
      (by norm_num : (0 : ℝ) ≤ 4⁻¹)
    rw [Real.mul_rpow hK (by positivity)] at h
    have he : ((|coefficient| * e * a *
        (1 / 2 : ℝ) ^ dyadicSlack (Nat.log2 M + 1) i) ^ 4) ^ (4⁻¹ : ℝ) =
        |coefficient| * e * a * (1 / 2 : ℝ) ^ dyadicSlack (Nat.log2 M + 1) i := by
      convert Real.pow_rpow_inv_natCast (by dsimp only [e, a]; positivity :
        0 ≤ |coefficient| * e * a * (1 / 2 : ℝ) ^ dyadicSlack (Nat.log2 M + 1) i)
        (by decide : (4 : ℕ) ≠ 0) using 1
    rw [he] at h
    exact h.trans_eq (by dsimp only [T]; ring)
  have hsum := sum_le_sum (fun i (_ : i ∈ range (j + 1)) => hr i)
  rw [← mul_sum] at hsum
  have hd := sum_prefix_dyadic_decay_le (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
    (show j + 1 ≤ Nat.log2 M + 1 by omega)
  have hpref : (∑ i ∈ range (j + 1), B.initialCenteredGroupCharge M
      (dyadicSlack (Nat.log2 M + 1) i) q coefficient ^ (4⁻¹ : ℝ)) ≤
      T * (2 * (1 / 2 : ℝ) ^ dyadicSlack (Nat.log2 M + 1) j) := by
    apply hsum.trans
    convert mul_le_mul_of_nonneg_left hd hT using 1
    simp only [Nat.add_sub_cancel]
    ring
  have hinv : initialPerturbationFactor ka B.base ≤ ((rate L)⁻¹) ^ 4 := by
    apply (initialPerturbationFactor_le ka B.base hbase).trans
    apply pow_le_pow_left₀ (by positivity)
    exact inv_anti₀ (rate_pos L) (rate_antitone hka)
  unfold initialComputedBoundedCenteredNoise
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 8)
  apply add_le_add _ le_rfl
  apply (mul_le_mul hinv (pow_le_pow_left₀
    (sum_nonneg fun i _ => Real.rpow_nonneg (B.initialCenteredGroupCharge_nonneg _ _ _ _) _)
    hpref 4)
    (by positivity) (by positivity)).trans_eq
  dsimp only [initialCenteredNoiseConstant, T, K, e, a, q]
  ring

private theorem centered_sum (S : Finset ℕ)
    (X Y : Environment P 3 → ZMod P → Prop)
    (A : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ) :
    (fun σ x y => (∑ i ∈ S, A i σ x y) -
      rowSliceMean X Y (fun τ x y => ∑ i ∈ S, A i τ x y) x y) =
      (fun σ x y => ∑ i ∈ S, (A i σ x y - rowSliceMean X Y (A i) x y)) := by
  funext σ x y
  simp only [rowSliceMean, expect_sum_comm, sum_sub_distrib]

/-- Literal successful group executions and their centered bounds pay the actual first
noise. Minkowski sums centered discrepancies, so the payment has no prefix-cardinality
cube and uses no independence. Original joint conditional means are preserved. -/
theorem initial_compressed_centered_first_noise (B : BudgetData HP P)
    (exponent : HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℕ)
    (ζ floor : ℝ) (M : ℕ) (hM : 0 < M) (hbins : B.bins.Nonempty)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (R : RoleProfile 3)
    (ks ka : ℕ) (ss st : List (ZMod P))
    (hs : r.source = gridChannel R.source ks ss)
    (ht : r.terminal = gridChannel R.terminal ka st)
    (A C : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ) (coefficient : ℝ)
    (hA : ∀ i < Nat.log2 M + 1,
      B.completedGroup (fun m q => if m < M then B.compressedHistory exponent ζ floor m q
        else none) M (dyadicSlack (Nat.log2 M + 1) i) (.pilotInput ⟨0, HP.k_pos⟩)
        { r with usage := r.terminal } = some (A i))
    (hCrun : ∀ i < Nat.log2 M + 1,
      B.completedGroup (fun m q => if m < M then B.evaluate m q else none)
        M (dyadicSlack (Nat.log2 M + 1) i) (.pilotInput ⟨0, HP.k_pos⟩)
        { r with usage := r.terminal } = some (C i))
    (herr : ∀ i < Nat.log2 M + 1,
      rowNormPow 4 P r.source.rate
        (retainedMask R.source (side P ks) B.padding ss)
        (retainedMask R.terminal (side P ka) B.padding st)
        (fun σ x y => (A i - C i) σ x y - rowSliceMean
          (retainedMask R.source (side P ks) B.padding ss)
          (retainedMask R.terminal (side P ka) B.padding st) (A i - C i) x y) ≤
        B.initialCenteredGroupCharge M (dyadicSlack (Nat.log2 M + 1) i)
          { r with usage := r.terminal } coefficient)
    (groups : List (Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ))
    (hgroups : (List.range (Nat.log2 M + 1)).mapM (fun i =>
      B.completedGroup (fun m q => if m < M then B.compressedHistory exponent ζ floor m q
        else none) M (dyadicSlack (Nat.log2 M + 1) i) (.pilotInput ⟨0, HP.k_pos⟩)
        { r with usage := r.terminal }) = some groups)
    (hbase : ∀ x y, 0 ≤ B.base x y)
    (Lt : ℕ) (second : Environment P 3 → ZMod P → ℕ → ZMod P → ℝ)
    (j : ℕ) (hj : j < Nat.log2 M + 1) :
    let F := fun p σ x y => ((groups.take p).map (fun T => T σ x y)).sum
    rowNormPow 4 P r.source.rate
      (retainedMask R.source (side P ks) B.padding ss)
      (retainedMask R.terminal (side P ka) B.padding st)
      (actualNoiseEntry R.source R.terminal (side P ks) (side P ka) Lt B.padding ss st
        ka B.base (firstSignalIncrement F ka second) 0 0 j) ≤
      B.initialComputedBoundedCenteredNoise M r R ks ka ss st coefficient j := by
  let Xs := retainedMask R.source (side P ks) B.padding ss
  let Ya := retainedMask R.terminal (side P ka) B.padding st
  have hNu : 0 ≤ (P : ℝ) * r.source.rate := by
    rw [hs]; exact mul_nonneg (Nat.cast_nonneg _) (rate_pos ks).le
  have hlist : groups = (List.range (Nat.log2 M + 1)).map A := by
    apply Option.some.inj
    apply hgroups.symm.trans
    apply List.mapM_eq_some_iff_forall₂.mpr
    rw [List.forall₂_map_right_iff, List.forall₂_same]
    exact fun i hi => hA i (List.mem_range.mp hi)
  let G := fun p σ x y =>
    ((((List.range (Nat.log2 M + 1)).map C).take p).map (fun T => T σ x y)).sum
  have hG : B.initialPrefixes M r = some G := by
    unfold initialPrefixes
    have hr : (List.range (Nat.log2 M + 1)).mapM (fun i =>
        B.completedGroup (fun m q => if m < M then B.evaluate m q else none)
          M (dyadicSlack (Nat.log2 M + 1) i) (.pilotInput ⟨0, HP.k_pos⟩)
          { r with usage := r.terminal }) = some ((List.range (Nat.log2 M + 1)).map C) := by
      apply List.mapM_eq_some_iff_forall₂.mpr
      rw [List.forall₂_map_right_iff, List.forall₂_same]
      exact fun i hi => hCrun i (List.mem_range.mp hi)
    rw [hr]
    rfl
  let F := fun p σ x y => ((groups.take p).map (fun T => T σ x y)).sum
  let E := fun i σ x y => (A i - C i) σ x y - rowSliceMean Xs Ya (A i - C i) x y
  let e := fun i => B.initialCenteredGroupCharge M (dyadicSlack (Nat.log2 M + 1) i)
    { r with usage := r.terminal } coefficient ^ (4⁻¹ : ℝ)
  have hp : rowNormPow 4 P r.source.rate Xs Ya
      (fun σ x y => (F (j + 1) - G (j + 1)) σ x y -
        rowSliceMean Xs Ya (F (j + 1) - G (j + 1)) x y) ≤
      (∑ i ∈ range (j + 1), e i) ^ 4 := by
    have heq : F (j + 1) - G (j + 1) =
        fun σ x y => ∑ i ∈ range (j + 1), (A i - C i) σ x y := by
      funext σ x y
      simp only [F, G, hlist, Pi.sub_apply, Matrix.sub_apply, ← List.map_take,
        List.take_range, min_eq_left (show j + 1 ≤ Nat.log2 M + 1 by omega),
        List.map_map, Function.comp_def, List.sum_map_range_eq_sum_range, sum_sub_distrib]
    rw [heq, centered_sum]
    have hb := rowNormPow_sum_le_pow_sum (X := Xs) (by decide : 4 ≠ 0) hNu Ya
      (range (j + 1)) E (fun _ => 1) e (by intros; norm_num)
      (fun i _ => Real.rpow_nonneg (B.initialCenteredGroupCharge_nonneg _ _ _ _) _)
      (fun i hi => by
        dsimp only [e]
        have he : (B.initialCenteredGroupCharge M (dyadicSlack (Nat.log2 M + 1) i)
            { r with usage := r.terminal } coefficient ^ (4⁻¹ : ℝ)) ^ 4 =
            B.initialCenteredGroupCharge M (dyadicSlack (Nat.log2 M + 1) i)
              { r with usage := r.terminal } coefficient := by
          convert Real.rpow_inv_natCast_pow (B.initialCenteredGroupCharge_nonneg M
            (dyadicSlack (Nat.log2 M + 1) i) { r with usage := r.terminal } coefficient)
            (by decide : (4 : ℕ) ≠ 0) using 1
        rw [he]
        exact herr i (by have := mem_range.mp hi; omega))
    simpa only [one_mul] using hb
  dsimp only
  rw [actualNoiseEntry_first_prefix_row_eq R.source R.terminal
    (side P ks) (side P ka) Lt B.padding ss st F ka B.base hbase second 0
    (by intros; rfl) j P r.source.rate]
  have heq : (fun σ x y => F (j + 1) σ x y / (rate ka + B.base x y) -
      rowSliceMean Xs Ya (fun τ x y => F (j + 1) τ x y / (rate ka + B.base x y)) x y) =
      (fun σ x y =>
        ((F (j + 1) - G (j + 1)) σ x y -
          rowSliceMean Xs Ya (F (j + 1) - G (j + 1)) x y) *
            (rate ka + B.base x y)⁻¹ +
        (G (j + 1) σ x y / (rate ka + B.base x y) -
          rowSliceMean Xs Ya (fun τ x y => G (j + 1) τ x y /
            (rate ka + B.base x y)) x y)) := by
    funext σ x y
    simp only [rowSliceMean, ← expect_div, Pi.sub_apply, expect_sub_distrib]
    ring
  change rowNormPow 4 P r.source.rate Xs Ya _ ≤ _
  rw [heq]
  apply (rowNormPow_add_le hNu _ _).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 8)
  apply add_le_add
  · exact (rowNormPow_mul_le_pi_norm hNu Xs Ya _
      (fun xy : ZMod P × ZMod P => (rate ka + B.base xy.1 xy.2)⁻¹)).trans
      (mul_le_mul_of_nonneg_left hp (by positivity))
  · have hn := B.initialPrefix_relative_noise M hM hbins r R.source R.terminal
      R.source_terminal ks ka ss st hs ht G hG B.base (j + 1)
    simpa only [Xs, Ya, rowSliceMean, ← expect_div, ← sub_div] using hn

/-- First-noise transport with normalization inside the centered joint row moment.
Finite Minkowski preserves arbitrary correlations. The pairwise target denominator only
contracts this normalized discrepancy; supported semantic noise remains separate. -/
theorem initial_compressed_normalized_first_noise (B : BudgetData HP P)
    (exponent : HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℕ)
    (ζ floor : ℝ) (M : ℕ) (hM : 0 < M) (hbins : B.bins.Nonempty)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (R : RoleProfile 3)
    (ks ka : ℕ) (ss st : List (ZMod P))
    (hs : r.source = gridChannel R.source ks ss)
    (ht : r.terminal = gridChannel R.terminal ka st)
    (A C : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (ε : ℕ → ℝ) (hε : ∀ i, 0 ≤ ε i)
    (hA : ∀ i < Nat.log2 M + 1,
      B.completedGroup (fun m q => if m < M then B.compressedHistory exponent ζ floor m q
        else none) M (dyadicSlack (Nat.log2 M + 1) i) (.pilotInput ⟨0, HP.k_pos⟩)
        { r with usage := r.terminal } = some (A i))
    (hCrun : ∀ i < Nat.log2 M + 1,
      B.completedGroup (fun m q => if m < M then B.evaluate m q else none)
        M (dyadicSlack (Nat.log2 M + 1) i) (.pilotInput ⟨0, HP.k_pos⟩)
        { r with usage := r.terminal } = some (C i))
    (herr : ∀ i < Nat.log2 M + 1,
      rowNormPow 4 P r.source.rate
        (retainedMask R.source (side P ks) B.padding ss)
        (retainedMask R.terminal (side P ka) B.padding st)
        (fun σ x y => ((A i - C i) σ x y - rowSliceMean
          (retainedMask R.source (side P ks) B.padding ss)
          (retainedMask R.terminal (side P ka) B.padding st) (A i - C i) x y) / rate ka) ≤ ε i ^ 4)
    (groups : List (Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ))
    (hgroups : (List.range (Nat.log2 M + 1)).mapM (fun i =>
      B.completedGroup (fun m q => if m < M then B.compressedHistory exponent ζ floor m q
        else none) M (dyadicSlack (Nat.log2 M + 1) i) (.pilotInput ⟨0, HP.k_pos⟩)
        { r with usage := r.terminal }) = some groups)
    (hbase : ∀ x y, 0 ≤ B.base x y)
    (Lt : ℕ) (second : Environment P 3 → ZMod P → ℕ → ZMod P → ℝ)
    (j : ℕ) (hj : j < Nat.log2 M + 1) :
    let F := fun p σ x y => ((groups.take p).map (fun T => T σ x y)).sum
    rowNormPow 4 P r.source.rate
      (retainedMask R.source (side P ks) B.padding ss)
      (retainedMask R.terminal (side P ka) B.padding st)
      (actualNoiseEntry R.source R.terminal (side P ks) (side P ka) Lt B.padding ss st
        ka B.base (firstSignalIncrement F ka second) 0 0 j) ≤
      8 * ((∑ i ∈ range (j + 1), ε i) ^ 4 +
        B.initialRelativeNoiseBudget M r R.source R.terminal R.source_terminal
          ks ka ss st B.base (j + 1)) := by
  let Xs := retainedMask R.source (side P ks) B.padding ss
  let Ya := retainedMask R.terminal (side P ka) B.padding st
  have hNu : 0 ≤ (P : ℝ) * r.source.rate := by
    rw [hs]; exact mul_nonneg (Nat.cast_nonneg _) (rate_pos ks).le
  have hlist : groups = (List.range (Nat.log2 M + 1)).map A := by
    apply Option.some.inj
    apply hgroups.symm.trans
    apply List.mapM_eq_some_iff_forall₂.mpr
    rw [List.forall₂_map_right_iff, List.forall₂_same]
    exact fun i hi => hA i (List.mem_range.mp hi)
  let G := fun p σ x y =>
    ((((List.range (Nat.log2 M + 1)).map C).take p).map (fun T => T σ x y)).sum
  have hG : B.initialPrefixes M r = some G := by
    unfold initialPrefixes
    have hr : (List.range (Nat.log2 M + 1)).mapM (fun i =>
        B.completedGroup (fun m q => if m < M then B.evaluate m q else none)
          M (dyadicSlack (Nat.log2 M + 1) i) (.pilotInput ⟨0, HP.k_pos⟩)
          { r with usage := r.terminal }) = some ((List.range (Nat.log2 M + 1)).map C) := by
      apply List.mapM_eq_some_iff_forall₂.mpr
      rw [List.forall₂_map_right_iff, List.forall₂_same]
      exact fun i hi => hCrun i (List.mem_range.mp hi)
    rw [hr]
    rfl
  let F := fun p σ x y => ((groups.take p).map (fun T => T σ x y)).sum
  let E := fun i σ x y => ((A i - C i) σ x y - rowSliceMean Xs Ya (A i - C i) x y) /
    rate ka
  have hp : rowNormPow 4 P r.source.rate Xs Ya
      (fun σ x y => ((F (j + 1) - G (j + 1)) σ x y -
        rowSliceMean Xs Ya (F (j + 1) - G (j + 1)) x y) / rate ka) ≤
      (∑ i ∈ range (j + 1), ε i) ^ 4 := by
    have heq : F (j + 1) - G (j + 1) =
        fun σ x y => ∑ i ∈ range (j + 1), (A i - C i) σ x y := by
      funext σ x y
      simp only [F, G, hlist, Pi.sub_apply, Matrix.sub_apply, ← List.map_take,
        List.take_range, min_eq_left (show j + 1 ≤ Nat.log2 M + 1 by omega),
        List.map_map, Function.comp_def, List.sum_map_range_eq_sum_range, sum_sub_distrib]
    rw [heq]
    simp only [rowSliceMean, expect_sum_comm, ← sum_sub_distrib, sum_div]
    have hb := rowNormPow_sum_le_pow_sum (X := Xs) (by decide : 4 ≠ 0) hNu Ya
      (range (j + 1)) E (fun _ => 1) ε (by intros; norm_num)
      (fun i _ => hε i) (fun i hi => herr i (by have := mem_range.mp hi; omega))
    simpa only [one_mul, E, rowSliceMean] using hb
  dsimp only
  rw [actualNoiseEntry_first_prefix_row_eq R.source R.terminal
    (side P ks) (side P ka) Lt B.padding ss st F ka B.base hbase second 0
    (by intros; rfl) j P r.source.rate]
  have heq : (fun σ x y => F (j + 1) σ x y / (rate ka + B.base x y) -
      rowSliceMean Xs Ya (fun τ x y => F (j + 1) τ x y / (rate ka + B.base x y)) x y) =
      (fun σ x y =>
        ((F (j + 1) - G (j + 1)) σ x y -
          rowSliceMean Xs Ya (F (j + 1) - G (j + 1)) x y) *
            (rate ka + B.base x y)⁻¹ +
        (G (j + 1) σ x y / (rate ka + B.base x y) -
          rowSliceMean Xs Ya (fun τ x y => G (j + 1) τ x y /
            (rate ka + B.base x y)) x y)) := by
    funext σ x y
    simp only [rowSliceMean, ← expect_div, Pi.sub_apply, expect_sub_distrib]
    ring
  change rowNormPow 4 P r.source.rate Xs Ya _ ≤ _
  rw [heq]
  apply (rowNormPow_add_le hNu _ _).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 8)
  apply add_le_add
  · apply (rowNormPow_le_mul hNu (c := 1) ?_).trans (by simpa only [one_mul] using hp)
    intro σ x y _ _
    rw [one_mul]
    have hden : rate ka ≤ rate ka + B.base x y := le_add_of_nonneg_right (hbase x y)
    have hr := rate_pos ka
    have hratio : 0 ≤ rate ka / (rate ka + B.base x y) := div_nonneg hr.le (hr.trans_le hden).le
    have hratio1 : rate ka / (rate ka + B.base x y) ≤ 1 :=
      (div_le_one (hr.trans_le hden)).mpr hden
    have heq : (((F (j + 1) - G (j + 1)) σ x y -
        rowSliceMean Xs Ya (F (j + 1) - G (j + 1)) x y) *
          (rate ka + B.base x y)⁻¹) =
        (((F (j + 1) - G (j + 1)) σ x y -
          rowSliceMean Xs Ya (F (j + 1) - G (j + 1)) x y) / rate ka) *
            (rate ka / (rate ka + B.base x y)) := by field_simp
    rw [heq, abs_mul, abs_of_nonneg hratio]
    apply pow_le_pow_left₀ (by positivity)
    exact mul_le_of_le_one_right (abs_nonneg _) hratio1
  · have hn := B.initialPrefix_relative_noise M hM hbins r R.source R.terminal
      R.source_terminal ks ka ss st hs ht G hG B.base (j + 1)
    simpa only [Xs, Ya, rowSliceMean, ← expect_div, ← sub_div] using hn

/-- Primitive constant for normalized ordinary noise, chosen before fields, requests,
budgets, horizons and precision. The summable scale majorant accounts for both bin tails. -/
@[expose] def initialNormalizedNoiseConstant (binCap coefficient : ℝ) : ℝ :=
  64 * (4 * (2 * binCap) ^ ((3 : ℝ) / 4)) * |coefficient| *
    ∑' h, LogSpaceEstimation.scaleMajorant h

/-- Unbounded normalized first-noise payment. Semantic supported noise is unchanged. -/
@[expose] def initialComputedNormalizedNoise (B : BudgetData HP P) (M : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (R : RoleProfile 3)
    (ks ka : ℕ) (ss st : List (ZMod P)) (coefficient : ℝ) (j : ℕ) : ℝ :=
  8 * ((initialNormalizedNoiseConstant B.binCap coefficient *
    (2 : ℝ) ^ (-B.requestPrecision M { r with usage := r.terminal }) *
    (2 : ℝ) ^ (-B.rankCharge) * (1 / 16 : ℝ) ^ dyadicSlack (Nat.log2 M + 1) j) ^ 4 +
    B.initialRelativeNoiseBudget M r R.source R.terminal R.source_terminal
      ks ka ss st B.base (j + 1))

/-- Normalized first-noise costs are nonnegative on every nonnegative source. -/
lemma initialComputedNormalizedNoise_nonneg (B : BudgetData HP P) (M : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (hr : 0 ≤ r.source.rate)
    (R : RoleProfile 3) (ks ka : ℕ) (ss st : List (ZMod P)) (coefficient : ℝ) (j : ℕ) :
    0 ≤ B.initialComputedNormalizedNoise M r R ks ka ss st coefficient j := by
  have hn := B.initialRelativeNoiseBudget_nonneg M r hr R.source R.terminal
    R.source_terminal ks ka ss st B.base (j + 1)
  unfold initialComputedNormalizedNoise
  positivity

/-- Conditional execution at actual child precision pays actual first noise for arbitrary
admissible horizons. This constructs the literal group list, keeps correlated prefixes,
and requires reset-right availability separately. It asserts no joint recursive IH. -/
theorem initial_compressed_normalized_noise_consumer (B : BudgetData HP P)
    (hcharge : 0 ≤ B.rankCharge) (hrate : B.binRate = rate) (H : Horizon P)
    (exponent : HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℕ)
    (ζ floor : ℝ) (M : ℕ) (hM : 0 < M) (hbins : B.bins.Nonempty)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (R : RoleProfile 3)
    (ks ka : ℕ) (ss st : List (ZMod P))
    (hs : r.source = gridChannel R.source ks ss)
    (ht : r.terminal = gridChannel R.terminal ka st)
    (htask : r.task = .row 0 (.pilotInput ⟨0, HP.k_pos⟩))
    (ha : ka ≤ H.maxExponent) (hi : ∀ bin ∈ B.bins, bin ≤ H.maxExponent)
    (hp : 0 ≤ B.requestPrecision M { r with usage := r.terminal })
    (D : ℕ → ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hzero : ∀ bin, D bin 0 = 0) (coefficient : ℝ)
    (ih : ∀ i bin, bin ∈ B.bins →
      let d := dyadicSlack (Nat.log2 M + 1) i
      let q := { r with usage := r.terminal }
      let fine := LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale q (some bin))
      let coarse := LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale q (some bin))
      fine ≠ coarse → ∀ m ∈ ({fine, coarse} : Finset ℕ), m < M → 0 < m →
      let q := { r with usage := r.terminal }
      let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
        q.source (midpoint q) q.terminal (B.binRate bin)
      B.compressedBin m bin (exponent Q.direct) ζ floor Q.direct = some (D bin m) ∧
      rootDistPow 4 P Q.direct.source.rate
        (fun σ x => Q.direct.source.retains (channels B.padding) σ x)
        (fun σ y => Q.direct.usage.retains (channels B.padding) σ y) (D bin m)
        (denseChild B.padding id Q.direct (B.cutoff bin) (B.auxiliary bin)
          HP.ρ HP.K B.base) ≤
        coefficient ^ 4 * ((2 : ℝ) ^ (-B.requestPrecision m Q.direct)) ^ 4 ∧
      ∃ R, B.compressedBin m bin (exponent Q.right) ζ floor Q.right = some R)
    (hbase : ∀ x y, 0 ≤ B.base x y) :
    ∃ groups,
      (List.range (Nat.log2 M + 1)).mapM (fun i =>
        B.completedGroup (fun m q => if m < M then B.compressedHistory exponent ζ floor m q
          else none) M (dyadicSlack (Nat.log2 M + 1) i) (.pilotInput ⟨0, HP.k_pos⟩)
          { r with usage := r.terminal }) = some groups ∧
      ∀ (Lt : ℕ) (second : Environment P 3 → ZMod P → ℕ → ZMod P → ℝ)
        (j : ℕ), j < Nat.log2 M + 1 →
      let F := fun p σ x y => ((groups.take p).map (fun T => T σ x y)).sum
      rowNormPow 4 P r.source.rate
        (retainedMask R.source (side P ks) B.padding ss)
        (retainedMask R.terminal (side P ka) B.padding st)
        (actualNoiseEntry R.source R.terminal (side P ks) (side P ka) Lt B.padding ss st
          ka B.base (firstSignalIncrement F ka second) 0 0 j) ≤
        B.initialComputedNormalizedNoise M r R ks ka ss st coefficient j := by
  let q := { r with usage := r.terminal }
  let K := initialNormalizedNoiseConstant B.binCap coefficient / 2
  let e := (2 : ℝ) ^ (-B.requestPrecision M q)
  let a := (2 : ℝ) ^ (-B.rankCharge)
  let ε := fun i => K * (e * a * (1 / 16 : ℝ) ^ dyadicSlack (Nat.log2 M + 1) i)
  have hcap := B.binCap_nonneg
  have hK : 0 ≤ K := by
    dsimp only [K, initialNormalizedNoiseConstant]
    exact div_nonneg (mul_nonneg (by positivity)
      (tsum_nonneg LogSpaceEstimation.scaleMajorant_nonneg)) (by norm_num)
  have hε (i : ℕ) : 0 ≤ ε i := by dsimp only [ε, e, a]; positivity
  have hg (i : ℕ) := B.completedGroup_initial_compressed_normalized_paid hcharge hrate H
    exponent ζ floor M (dyadicSlack (Nat.log2 M + 1) i) hM hbins q
    R.source R.terminal R.source_terminal ks ka ka ss st hs ht
    (by rw [ht]; rfl) htask ha hi D hp hzero coefficient
    (fun bin hb => ih i bin hb)
  choose A C hA hC herr using hg
  have hnorm (i : ℕ) : rowNormPow 4 P r.source.rate
      (retainedMask R.source (side P ks) B.padding ss)
      (retainedMask R.terminal (side P ka) B.padding st)
      (fun σ x y => ((A i - C i) σ x y - rowSliceMean
        (retainedMask R.source (side P ks) B.padding ss)
        (retainedMask R.terminal (side P ka) B.padding st) (A i - C i) x y) / rate ka) ≤
      ε i ^ 4 := by
    have hb := herr i
    have hKeq : K = 32 * (4 * (2 * B.binCap) ^ ((3 : ℝ) / 4)) * |coefficient| *
        ∑' h, LogSpaceEstimation.scaleMajorant h := by
      dsimp only [K, initialNormalizedNoiseConstant]
      ring
    dsimp only [ε]
    rw [hKeq]
    simpa only [e, a, q, hs, ht, gridChannel, CorrectionRowTask.Channel.retains,
      channels, semanticSide_grid, X, Y, retainedMask, rowNormPow, rowSliceMean] using hb
  let groups := (List.range (Nat.log2 M + 1)).map A
  have hgroups : (List.range (Nat.log2 M + 1)).mapM (fun i =>
      B.completedGroup (fun m q => if m < M then B.compressedHistory exponent ζ floor m q
        else none) M (dyadicSlack (Nat.log2 M + 1) i) (.pilotInput ⟨0, HP.k_pos⟩) q) =
      some groups := by
    apply List.mapM_eq_some_iff_forall₂.mpr
    rw [List.forall₂_map_right_iff, List.forall₂_same]
    exact fun i _ => hA i
  refine ⟨groups, hgroups, ?_⟩
  intro Lt second j hj
  have hb := B.initial_compressed_normalized_first_noise exponent ζ floor M hM hbins r R
    ks ka ss st hs ht A C ε hε (fun i _ => hA i) (fun i _ => hC i)
    (fun i _ => hnorm i) groups hgroups hbase Lt second j hj
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 8)
  apply add_le_add _ le_rfl
  have hd := sum_prefix_dyadic_decay_le (by norm_num : (0 : ℝ) ≤ 1 / 16)
    (by norm_num : (1 / 16 : ℝ) < 1) (show j + 1 ≤ Nat.log2 M + 1 by omega)
  simp only [Nat.add_sub_cancel] at hd
  have hsε : (∑ i ∈ range (j + 1), ε i) ≤
      K * (e * a) * ((16 / 15) * (1 / 16 : ℝ) ^ dyadicSlack (Nat.log2 M + 1) j) := by
    simp only [ε, ← mul_sum, ← mul_assoc]
    convert mul_le_mul_of_nonneg_left hd (by dsimp only [e, a]; positivity : 0 ≤ K * (e * a))
      using 1 <;> ring
  apply pow_le_pow_left₀ (sum_nonneg fun i _ => hε i)
  apply hsε.trans
  dsimp only [K]
  have hnonneg : 0 ≤ initialNormalizedNoiseConstant B.binCap coefficient *
      e * a * (1 / 16 : ℝ) ^ dyadicSlack (Nat.log2 M + 1) j := by
    have hc : 0 ≤ initialNormalizedNoiseConstant B.binCap coefficient := by
      dsimp only [K] at hK
      linarith
    exact mul_nonneg (mul_nonneg (mul_nonneg hc (by dsimp only [e]; positivity))
      (by dsimp only [a]; positivity)) (by positivity)
  change _ ≤ initialNormalizedNoiseConstant B.binCap coefficient *
    e * a * (1 / 16 : ℝ) ^ dyadicSlack (Nat.log2 M + 1) j
  nlinarith only [hnonneg]

/-- Numerical guards for the unbounded normalized-noise lane. The common admissible
horizon is shared by the terminal and every bin; it supplies rounded-mass comparison. -/
@[expose] def initialNormalizedNoiseAdmissible (B : BudgetData HP P) (M : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (ka : ℕ) : Prop :=
  0 ≤ B.rankCharge ∧ B.binRate = rate ∧
    r.task = .row 0 (.pilotInput ⟨0, HP.k_pos⟩) ∧
    0 ≤ B.requestPrecision M { r with usage := r.terminal } ∧
    ∃ H : Horizon P, ka ≤ H.maxExponent ∧ ∀ bin ∈ B.bins, bin ≤ H.maxExponent

/-- Actual centered first-noise cost, retaining the bounded fallback and selecting the
uniform normalized payment on its numerical admissibility guards. -/
@[expose] def initialComputedCenteredNoise (B : BudgetData HP P) (M : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (R : RoleProfile 3)
    (ks ka : ℕ) (ss st : List (ZMod P)) (coefficient : ℝ) (j : ℕ) : ℝ :=
  min (B.initialComputedBoundedCenteredNoise M r R ks ka ss st coefficient j)
    (if B.initialNormalizedNoiseAdmissible M r ka then
      B.initialComputedNormalizedNoise M r R ks ka ss st coefficient j else
      B.initialComputedBoundedCenteredNoise M r R ks ka ss st coefficient j)

/-- Both fallback and normalized costs are nonnegative. -/
lemma initialComputedCenteredNoise_nonneg (B : BudgetData HP P) (M : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (hr : 0 ≤ r.source.rate)
    (R : RoleProfile 3) (ks ka : ℕ) (ss st : List (ZMod P)) (coefficient : ℝ) (j : ℕ) :
    0 ≤ B.initialComputedCenteredNoise M r R ks ka ss st coefficient j := by
  have hb := B.initialComputedBoundedCenteredNoise_nonneg M r hr R ks ka ss st coefficient j
  have hn := B.initialComputedNormalizedNoise_nonneg M r hr R ks ka ss st coefficient j
  unfold initialComputedCenteredNoise
  split_ifs <;> positivity

/-- The sparse second-noise branch requires the actual polynomial preparation and
source horizon. Its usage channel is narrower than full terminal rank, on the same suffix. -/
@[expose] def initialSecondNoiseAdmissible (B : BudgetData HP P)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (R : RoleProfile 3)
    (ks ka : ℕ) (ss st : List (ZMod P)) : Prop :=
  B.auxiliary = (fun _ => polynomialPrepCutoff4 HP.θ) ∧
    r.source = gridChannel R.source ks ss ∧ r.terminal = gridChannel R.terminal ka st ∧
    (∃ H : Horizon P, ks ≤ H.maxExponent) ∧
    ∃ ku, ka ≤ ku ∧ r.usage = gridChannel R.terminal ku st

/-- Four computed costs from own-request precision, using clipped mean transport for
the first coordinate and centered spectral transport for first noise. Both keep their
previous fallbacks. Saturated preparation also uses the two actual supports and the
first-coordinate mean/noise payments, without repeating a maximum across the field.
These minima are consumed by the literal four-max and raw clipped-error gates. -/
@[expose] def initialComputedPrecisionMoment (B : BudgetData HP P) (M n : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (R : RoleProfile 3)
    (ks ka : ℕ) (ss st : List (ZMod P)) (coefficient ζ Lh Lρ : ℝ)
    (j : ℕ) (noise : Bool) (ν : Fin 2) : ℝ :=
  let ε := fun i => B.initialRootGroupCharge M (dyadicSlack (Nat.log2 M + 1) i)
    { r with usage := r.terminal } coefficient
  let cost := fun (isNoise : Bool) (coordinate : Fin 2) =>
    let old := B.initialComputedRelativeMoment M n r R ks ka ss st ε ζ Lh Lρ j isNoise coordinate
    if !isNoise ∧ coordinate = 0 then min old
      (min (8 * (((∑ i ∈ range (j + 1),
        (B.initialClippedRootGroupCharge M (dyadicSlack (Nat.log2 M + 1) i)
          { r with usage := r.terminal } ka coefficient) ^ (4⁻¹ : ℝ)) ^ 4) +
        rowNormPow 4 P r.source.rate
          (retainedMask R.source (side P ks) B.padding ss)
          (retainedMask R.terminal (side P ka) B.padding st)
          (fun _ x y => min 1 (|B.initialPolynomialLoss M n j r x y| /
            (rate ka + B.base x y)))))
        (8 * (B.initialClippedEndpointPrefixCharge M j { r with usage := r.terminal } ka
          coefficient + rowNormPow 4 P r.source.rate
            (retainedMask R.source (side P ks) B.padding ss)
            (retainedMask R.terminal (side P ka) B.padding st)
            (fun _ x y => min 1 (|B.initialPolynomialLoss M n j r x y| /
              (rate ka + B.base x y)))))) else
      if isNoise ∧ coordinate = 0 then
        min old (B.initialComputedCenteredNoise M r R ks ka ss st coefficient j) else old
  if !noise ∧ ν = 1 then min (cost noise ν)
    (8 * (2 * HP.K) * (|ζ| * preparationRelativeConstant HP Lh Lρ) ^ 4 *
      (cost false 0 + cost true 0)) else
    if noise ∧ ν = 1 then min (cost noise ν)
      (if B.initialSecondNoiseAdmissible r R ks ka ss st then
        B.initialSecondNoiseMoment M r ζ j else cost noise ν) else cost noise ν

/-- The actual supported second-mean minimum consumes the same first-mean and first-noise
costs. Its full-rank input moments are supplied by the executed-history theorem. -/
theorem initialComputedPrecisionMoment_secondMean_le (B : BudgetData HP P) (M n : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (R : RoleProfile 3)
    (ks ka : ℕ) (ss st : List (ZMod P)) (coefficient ζ Lh Lρ : ℝ) (j : ℕ) :
    B.initialComputedPrecisionMoment M n r R ks ka ss st coefficient ζ Lh Lρ j false 1 ≤
      8 * (2 * HP.K) * (|ζ| * preparationRelativeConstant HP Lh Lρ) ^ 4 *
        (B.initialComputedPrecisionMoment M n r R ks ka ss st coefficient ζ Lh Lρ j false 0 +
          B.initialComputedPrecisionMoment M n r R ks ka ss st coefficient ζ Lh Lρ j true 0) := by
  simp only [initialComputedPrecisionMoment, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, false_and, (show (0 : Fin 2) ≠ 1 by decide),
    (show (1 : Fin 2) ≠ 0 by decide), and_false, and_self, ↓reduceIte]
  exact min_le_right _ _

/-- The actual second-noise minimum consumes the literal sparse preparation payment
when its polynomial-preparation and source/usage guards hold. Field coverage belongs to
numerical allocation, not to this execution selector. -/
theorem initialComputedPrecisionMoment_secondNoise_le (B : BudgetData HP P) (M n : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (R : RoleProfile 3)
    (ks ka : ℕ) (ss st : List (ZMod P)) (coefficient ζ Lh Lρ : ℝ) (j : ℕ)
    (hadm : B.initialSecondNoiseAdmissible r R ks ka ss st) :
    B.initialComputedPrecisionMoment M n r R ks ka ss st coefficient ζ Lh Lρ j true 1 ≤
      B.initialSecondNoiseMoment M r ζ j := by
  simp only [initialComputedPrecisionMoment, Bool.not_true, Bool.false_eq_true, false_and,
    (show (1 : Fin 2) ≠ 0 by decide), and_false, and_self, ↓reduceIte, hadm]
  exact min_le_right _ _

/-- A single structural charge allocates actual conditional first noise on a bounded
full-bin family, before field width, request coordinates and budgets are chosen. This
pays transported noise only; the supported semantic noise keeps its polynomial payment.
The existing four-max and raw separated reserve consume this same computed minimum. -/
theorem initialComputedPrecisionMoment_firstNoise_exists_charge
    (binCap coefficient : ℝ) (L : ℕ) :
    ∃ A : ℕ, ∀ {P : ℕ} [Fact P.Prime] (B : BudgetData HP P),
      B.binCap = binCap → B.rankCharge = A → B.binRate = rate →
      ∀ (H : Horizon P) (M j ks ka : ℕ), j < Nat.log2 M + 1 → ka ≤ L →
      ka ≤ H.maxExponent → (∀ bin ∈ B.bins, bin ≤ H.maxExponent) → #B.bins ≤ L + 1 →
      ∀ (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)),
      r.source.rate = rate ks → r.terminal.rate = rate ka →
      r.task = .row 0 (.pilotInput ⟨0, HP.k_pos⟩) →
      0 ≤ B.requestPrecision M { r with usage := r.terminal } →
      (∀ x y, 0 ≤ B.base x y) → ∀ (R : RoleProfile 3) (ss st : List (ZMod P))
        (n : ℕ) (ζ Lh Lρ : ℝ),
      B.initialComputedPrecisionMoment M n r R ks ka ss st coefficient ζ Lh Lρ j true 0 ≤
        8 * (((2 : ℝ) ^ (-B.requestPrecision M { r with usage := r.terminal }) *
          (1 / 2 : ℝ) ^ dyadicSlack (Nat.log2 M + 1) j) ^ 4 +
          B.initialRelativeNoiseBudget M r R.source R.terminal R.source_terminal
            ks ka ss st B.base (j + 1)) := by
  have hrateL := rate_pos L
  let K := initialCenteredNoiseConstant binCap coefficient L
  obtain ⟨A, hA⟩ := exists_nat_gt K
  have hpow : (A : ℝ) ≤ (2 : ℝ) ^ A := by
    exact_mod_cast (Nat.lt_two_pow_self (n := A)).le
  have hpaid : K * (2 : ℝ) ^ (-(A : ℝ)) ≤ 1 := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
    exact (mul_le_mul_of_nonneg_right (hA.le.trans hpow) (by positivity)).trans_eq
      (mul_inv_cancel₀ (by positivity))
  refine ⟨A, ?_⟩
  intro P _ B hcap hcharge hrate H M j ks ka hj hka ha hi hc r hs ht htask hp hbase
    R ss st n ζ Lh Lρ
  have hb := B.initialComputedBoundedCenteredNoise_bounded (by rw [hcharge]; positivity)
    hrate H M j ks ka L hj hka ha hi hc r hs ht htask hp hbase R ss st coefficient
  have hmin : B.initialComputedPrecisionMoment M n r R ks ka ss st coefficient ζ Lh Lρ
      j true 0 ≤ B.initialComputedBoundedCenteredNoise M r R ks ka ss st coefficient j := by
    simp only [initialComputedPrecisionMoment, initialComputedCenteredNoise,
      Bool.not_true, Bool.false_eq_true,
      false_and, ↓reduceIte, and_self]
    exact (min_le_right _ _).trans (min_le_left _ _)
  apply (hmin.trans hb).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 8)
  apply add_le_add _ le_rfl
  apply pow_le_pow_left₀ (by unfold initialCenteredNoiseConstant; positivity)
  have he := mul_le_mul_of_nonneg_right hpaid (show 0 ≤
    (2 : ℝ) ^ (-B.requestPrecision M { r with usage := r.terminal }) *
      (1 / 2 : ℝ) ^ dyadicSlack (Nat.log2 M + 1) j by positivity)
  simpa only [K, hcap, hcharge, one_mul, mul_assoc] using he

/-- One charge pays the actual computed first-noise minimum on unbounded admissible
bin/source/terminal families. The charge precedes field, horizon, budget and precision.
The four-max and literal separated-reserve consumers use this same minimum; semantic
supported noise retains its separate payment. -/
theorem initialComputedPrecisionMoment_firstNoise_uniform_charge
    (binCap coefficient : ℝ) :
    ∃ A : ℕ, ∀ {P : ℕ} [Fact P.Prime] (B : BudgetData HP P),
      B.binCap = binCap → B.rankCharge = A → B.binRate = rate →
      ∀ (H : Horizon P) (M j ks ka : ℕ), ka ≤ H.maxExponent →
      (∀ bin ∈ B.bins, bin ≤ H.maxExponent) →
      ∀ (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)),
      r.task = .row 0 (.pilotInput ⟨0, HP.k_pos⟩) →
      0 ≤ B.requestPrecision M { r with usage := r.terminal } →
      ∀ (R : RoleProfile 3) (ss st : List (ZMod P)) (n : ℕ) (ζ Lh Lρ : ℝ),
      B.initialComputedPrecisionMoment M n r R ks ka ss st coefficient ζ Lh Lρ j true 0 ≤
        8 * (((2 : ℝ) ^ (-B.requestPrecision M { r with usage := r.terminal }) *
          (1 / 16 : ℝ) ^ dyadicSlack (Nat.log2 M + 1) j) ^ 4 +
          B.initialRelativeNoiseBudget M r R.source R.terminal R.source_terminal
            ks ka ss st B.base (j + 1)) := by
  let K := initialNormalizedNoiseConstant binCap coefficient
  obtain ⟨A, hA⟩ := exists_nat_gt K
  have hpow : (A : ℝ) ≤ (2 : ℝ) ^ A := by
    exact_mod_cast (Nat.lt_two_pow_self (n := A)).le
  have hpaid : K * (2 : ℝ) ^ (-(A : ℝ)) ≤ 1 := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
    exact (mul_le_mul_of_nonneg_right (hA.le.trans hpow) (by positivity)).trans_eq
      (mul_inv_cancel₀ (by positivity))
  refine ⟨A, ?_⟩
  intro P _ B hcap hcharge hrate H M j ks ka ha hi r htask hp R ss st n ζ Lh Lρ
  have hadm : B.initialNormalizedNoiseAdmissible M r ka :=
    ⟨by rw [hcharge]; positivity, hrate, htask, hp, H, ha, hi⟩
  have hmin : B.initialComputedPrecisionMoment M n r R ks ka ss st coefficient ζ Lh Lρ
      j true 0 ≤ B.initialComputedNormalizedNoise M r R ks ka ss st coefficient j := by
    simp only [initialComputedPrecisionMoment, initialComputedCenteredNoise,
      Bool.not_true, Bool.false_eq_true,
      false_and, ↓reduceIte, and_self, hadm]
    exact (min_le_right _ _).trans (min_le_right _ _)
  apply hmin.trans
  unfold initialComputedNormalizedNoise
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 8)
  apply add_le_add _ le_rfl
  have hcap0 := B.binCap_nonneg
  apply pow_le_pow_left₀ (by
    unfold initialNormalizedNoiseConstant
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by positivity)
      (tsum_nonneg LogSpaceEstimation.scaleMajorant_nonneg)) (by positivity))
      (by positivity)) (by positivity))
  have hh := mul_le_mul_of_nonneg_right hpaid (show 0 ≤
    (2 : ℝ) ^ (-B.requestPrecision M { r with usage := r.terminal }) *
      (1 / 16 : ℝ) ^ dyadicSlack (Nat.log2 M + 1) j by positivity)
  simpa only [K, hcap, hcharge, one_mul, mul_assoc, mul_comm, mul_left_comm] using hh

/-- Both normalized transported noise and the original semantic noise have a
uniform structural payment. Canonical budget-boundary support pays the semantic
prefix cube; the walk schedule and production evaluator are unchanged. -/
theorem initialComputedNormalizedNoise_polynomial_uniform_le (B : BudgetData HP P)
    (hcharge : 0 ≤ B.rankCharge) (hrate : B.binRate = rate)
    (hcutoff : B.cutoff = fun i => boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1)
      rate 1 i (fun _ => 1))
    (H : Horizon P) (hi : ∀ bin ∈ B.bins, bin ≤ H.maxExponent)
    (M j ks ka : ℕ) (hM : 0 < M) (hj : j < Nat.log2 M + 1)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (R : RoleProfile 3)
    (ss st : List (ZMod P))
    (hs : r.source = gridChannel R.source ks ss)
    (ht : r.terminal = gridChannel R.terminal ka st)
    (htask : r.task = .row 0 (.pilotInput ⟨0, HP.k_pos⟩))
    (ha : ka ≤ H.maxExponent) (hp : 0 ≤ B.requestPrecision M r)
    (hbase : ∀ x y, 0 ≤ B.base x y) (hrow : B.base *ᵥ 1 ≤ 1)
    (coefficient : ℝ) :
    B.initialComputedNormalizedNoise M r R ks ka ss st coefficient j ≤
      ((2 * (initialNormalizedNoiseConstant B.binCap coefficient + 256 * B.binCap)) *
        (2 : ℝ) ^ (-B.requestPrecision M { r with usage := r.terminal }) *
        (2 : ℝ) ^ (-B.rankCharge) *
        (1 / 4 : ℝ) ^ dyadicSlack (Nat.log2 M + 1) j) ^ 4 := by
  have hsemantic := B.initialRelativeNoiseBudget_polynomial_uniform_le hcharge hrate
    hcutoff H hi M hM r R.source R.terminal R.source_terminal ks ka ss st hs ht htask
    ha hp hbase hrow (j + 1) (by omega)
  simp only [Nat.add_sub_cancel] at hsemantic
  let T := (2 : ℝ) ^ (-B.requestPrecision M { r with usage := r.terminal }) *
    (2 : ℝ) ^ (-B.rankCharge) * (1 / 4 : ℝ) ^ dyadicSlack (Nat.log2 M + 1) j
  let x := initialNormalizedNoiseConstant B.binCap coefficient * T
  let y := 256 * B.binCap * T
  have hcap := B.binCap_nonneg
  have hS : 0 ≤ ∑' h, LogSpaceEstimation.scaleMajorant h :=
    tsum_nonneg LogSpaceEstimation.scaleMajorant_nonneg
  have hx : 0 ≤ x := by dsimp only [x, T, initialNormalizedNoiseConstant]; positivity
  have hy : 0 ≤ y := by dsimp only [y, T]; positivity
  have hb : B.initialComputedNormalizedNoise M r R ks ka ss st coefficient j ≤
      8 * (x ^ 4 + y ^ 4) := by
    unfold initialComputedNormalizedNoise
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 8)
    apply add_le_add
    · dsimp only [x, T]
      apply pow_le_pow_left₀ (by unfold initialNormalizedNoiseConstant; positivity)
      have hd := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 16)
        (by norm_num : (1 / 16 : ℝ) ≤ 1 / 4) (dyadicSlack (Nat.log2 M + 1) j)
      have hh := mul_le_mul_of_nonneg_left hd (show 0 ≤
        initialNormalizedNoiseConstant B.binCap coefficient *
          (2 : ℝ) ^ (-B.requestPrecision M {r with usage := r.terminal}) *
          (2 : ℝ) ^ (-B.rankCharge) by unfold initialNormalizedNoiseConstant; positivity)
      simpa only [mul_assoc] using hh
    · simpa only [y, T, mul_assoc] using hsemantic
  have hx4 : x ^ 4 ≤ (x + y) ^ 4 := pow_le_pow_left₀ hx (le_add_of_nonneg_right hy) 4
  have hy4 : y ^ 4 ≤ (x + y) ^ 4 := pow_le_pow_left₀ hy (le_add_of_nonneg_left hx) 4
  apply hb.trans
  calc
    _ ≤ 16 * (x + y) ^ 4 := by linarith
    _ = _ := by dsimp only [x, y, T]; ring

/-- One charge, fixed before every field, horizon, bin family and request, pays the
complete actual first-noise statistic. This combines semantic and transported noise;
it does not pay the other three reserve statistics or construct recursive children. -/
theorem initialComputedPrecisionMoment_firstNoise_polynomial_paid
    (binCap coefficient : ℝ) :
    ∃ A : ℕ, ∀ {P : ℕ} [Fact P.Prime] (B : BudgetData HP P),
      B.binCap = binCap → B.rankCharge = A → B.binRate = rate →
      B.cutoff = (fun i => boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1)
        rate 1 i (fun _ => 1)) →
      ∀ (H : Horizon P) (M j ks ka : ℕ), 0 < M → j < Nat.log2 M + 1 →
      ka ≤ H.maxExponent → (∀ bin ∈ B.bins, bin ≤ H.maxExponent) →
      ∀ (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (R : RoleProfile 3)
        (ss st : List (ZMod P)),
      r.source = gridChannel R.source ks ss →
      r.terminal = gridChannel R.terminal ka st →
      r.task = .row 0 (.pilotInput ⟨0, HP.k_pos⟩) →
      0 ≤ B.requestPrecision M r → (∀ x y, 0 ≤ B.base x y) → B.base *ᵥ 1 ≤ 1 →
      ∀ (n : ℕ) (ζ Lh Lρ : ℝ),
      B.initialComputedPrecisionMoment M n r R ks ka ss st coefficient ζ Lh Lρ j true 0 ≤
        ((2 : ℝ) ^ (-B.requestPrecision M r) *
          (1 / 4 : ℝ) ^ dyadicSlack (Nat.log2 M + 1) j) ^ 4 := by
  let K := 2 * (initialNormalizedNoiseConstant binCap coefficient + 256 * binCap)
  obtain ⟨A, hA⟩ := exists_nat_gt K
  have hpow : (A : ℝ) ≤ (2 : ℝ) ^ A := by
    exact_mod_cast (Nat.lt_two_pow_self (n := A)).le
  have hpaid : K * (2 : ℝ) ^ (-(A : ℝ)) ≤ 1 := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
    exact (mul_le_mul_of_nonneg_right (hA.le.trans hpow) (by positivity)).trans_eq
      (mul_inv_cancel₀ (by positivity))
  refine ⟨A, ?_⟩
  intro P _ B hcap hcharge hrate hcutoff H M j ks ka hM hj ha hi r R ss st hs ht
    htask hp hbase hrow n ζ Lh Lρ
  have hadm : B.initialNormalizedNoiseAdmissible M r ka :=
    ⟨by rw [hcharge]; positivity, hrate, htask, hp, H, ha, hi⟩
  have hmin : B.initialComputedPrecisionMoment M n r R ks ka ss st coefficient ζ Lh Lρ
      j true 0 ≤ B.initialComputedNormalizedNoise M r R ks ka ss st coefficient j := by
    simp only [initialComputedPrecisionMoment, initialComputedCenteredNoise,
      Bool.not_true, Bool.false_eq_true, false_and, ↓reduceIte, and_self, hadm]
    exact (min_le_right _ _).trans (min_le_right _ _)
  apply (hmin.trans (B.initialComputedNormalizedNoise_polynomial_uniform_le
    (by rw [hcharge]; positivity) hrate hcutoff H hi M j ks ka hM hj r R ss st
    hs ht htask ha hp hbase hrow coefficient)).trans
  have hcap0 := B.binCap_nonneg
  have hS : 0 ≤ ∑' h, LogSpaceEstimation.scaleMajorant h :=
    tsum_nonneg LogSpaceEstimation.scaleMajorant_nonneg
  apply pow_le_pow_left₀ (by unfold initialNormalizedNoiseConstant; positivity)
  have hh := mul_le_mul_of_nonneg_right hpaid (show 0 ≤
    (2 : ℝ) ^ (-B.requestPrecision M r) *
      (1 / 4 : ℝ) ^ dyadicSlack (Nat.log2 M + 1) j by positivity)
  have hprecision : B.requestPrecision M { r with usage := r.terminal } =
      B.requestPrecision M r := rfl
  simpa only [hprecision, K, hcap, hcharge, one_mul, mul_assoc, mul_comm, mul_left_comm] using hh

/-- The existing first-mean minimum consumes the finite joint allocation condition.
Only the clipped transport part is paid here; the semantic deficit and other three
statistics remain separate. Uniform use requires the window condition uniformly. -/
theorem initialComputedPrecisionMoment_first_paid (B : BudgetData HP P)
    (hcharge : 0 ≤ B.rankCharge) (hrate : B.binRate = rate) (H : Horizon P)
    (M n j ks ka : ℕ) (ha : ka ≤ H.maxExponent)
    (hi : ∀ bin ∈ B.bins, bin ≤ H.maxExponent)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka)
    (htask : r.task = .row 0 (.pilotInput ⟨0, HP.k_pos⟩))
    (R : RoleProfile 3) (ss st : List (ZMod P)) (coefficient ζ Lh Lρ : ℝ)
    (hwindow : 2 *
      (max (512 * (6 * B.binCap + 3) ^ 3) (32768 * B.binCap ^ 3)) ^ (4⁻¹ : ℝ) *
      (∑ i ∈ range (j + 1), B.initialClippedRootWindow M
        (dyadicSlack (Nat.log2 M + 1) i) ka { r with usage := r.terminal }) ≤
      (2 : ℝ) ^ B.rankCharge) :
    B.initialComputedPrecisionMoment M n r R ks ka ss st coefficient ζ Lh Lρ j false 0 ≤
      8 * (coefficient ^ 4 * ((2 : ℝ) ^ (-B.requestPrecision M r)) ^ 4 +
        rowNormPow 4 P r.source.rate
          (retainedMask R.source (side P ks) B.padding ss)
          (retainedMask R.terminal (side P ka) B.padding st)
          (fun _ x y => min 1 (|B.initialPolynomialLoss M n j r x y| /
            (rate ka + B.base x y)))) := by
  unfold initialComputedPrecisionMoment
  simp only [Bool.not_false, Fin.isValue, and_self, ↓reduceIte]
  apply ((min_le_right _ _).trans (min_le_left _ _)).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 8)
  apply add_le_add _ le_rfl
  exact B.initialClippedRootPrefix_paid hcharge hrate H M (j + 1) ks ka ha hi
    { r with usage := r.terminal } hs ht htask hwindow coefficient

/-- The existing first-mean minimum consumes the finite joint allocation condition.
Only the surviving clipped endpoints are paid here; the semantic deficit and other
three statistics remain separate. Uniform use requires the one-window condition uniformly. -/
theorem initialComputedPrecisionMoment_first_endpoint_paid (B : BudgetData HP P)
    (hcharge : 0 ≤ B.rankCharge) (hrate : B.binRate = rate) (H : Horizon P)
    (M n j ks ka : ℕ) (ha : ka ≤ H.maxExponent)
    (hi : ∀ bin ∈ B.bins, bin ≤ H.maxExponent)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka)
    (htask : r.task = .row 0 (.pilotInput ⟨0, HP.k_pos⟩))
    (R : RoleProfile 3) (ss st : List (ZMod P)) (coefficient ζ Lh Lρ : ℝ)
    (hwindow :
      (max (512 * (6 * B.binCap + 3) ^ 3) (32768 * B.binCap ^ 3)) ^ (4⁻¹ : ℝ) *
        B.initialClippedEndpointWindow M j ka { r with usage := r.terminal } ≤
      (2 : ℝ) ^ B.rankCharge) :
    B.initialComputedPrecisionMoment M n r R ks ka ss st coefficient ζ Lh Lρ j false 0 ≤
      8 * (coefficient ^ 4 * ((2 : ℝ) ^ (-B.requestPrecision M r)) ^ 4 +
        rowNormPow 4 P r.source.rate
          (retainedMask R.source (side P ks) B.padding ss)
          (retainedMask R.terminal (side P ka) B.padding st)
          (fun _ x y => min 1 (|B.initialPolynomialLoss M n j r x y| /
            (rate ka + B.base x y)))) := by
  unfold initialComputedPrecisionMoment
  simp only [Bool.not_false, Fin.isValue, and_self, ↓reduceIte]
  apply ((min_le_right _ _).trans (min_le_right _ _)).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 8)
  apply add_le_add _ le_rfl
  exact B.initialClippedEndpointPrefixCharge_paid hcharge hrate H M j ks ka ha hi
    { r with usage := r.terminal } hs ht htask hwindow coefficient

/-- Weighted first-mean moments in the literal computed reserve. Use the actual
false-event coefficient at index `j` for the raw prefix `j + 1`. The semantic deficit
is paid separately. No successful parent accuracy or uniform prefix bound is assumed. -/
theorem initialComputedPrecisionMoment_first_weighted_le (B : BudgetData HP P)
    (hcharge : 0 ≤ B.rankCharge) (hrate : B.binRate = rate) (H : Horizon P)
    (M n ks ka : ℕ) (ha : ka ≤ H.maxExponent)
    (hi : ∀ bin ∈ B.bins, bin ≤ H.maxExponent)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka)
    (htask : r.task = .row 0 (.pilotInput ⟨0, HP.k_pos⟩))
    (R : RoleProfile 3) (ss st : List (ZMod P)) (coefficient ζ Lh Lρ : ℝ)
    (s : Finset ℕ) (w : ℕ → ℝ) (hw : ∀ j ∈ s, 0 ≤ w j) :
    (∑ j ∈ s, w j *
      B.initialComputedPrecisionMoment M n r R ks ka ss st coefficient ζ Lh Lρ j false 0) ≤
    8 * (((max (512 * (6 * B.binCap + 3) ^ 3) (32768 * B.binCap ^ 3)) ^
      (4⁻¹ : ℝ) * |coefficient| * (2 : ℝ) ^ (-B.requestPrecision M r) *
        (2 : ℝ) ^ (-B.rankCharge)) ^ 4 *
          ∑ j ∈ s, w j * B.initialClippedEndpointWindow M j ka
            { r with usage := r.terminal } ^ 4 +
      ∑ j ∈ s, w j * rowNormPow 4 P r.source.rate
        (retainedMask R.source (side P ks) B.padding ss)
        (retainedMask R.terminal (side P ka) B.padding st)
        (fun _ x y => min 1 (|B.initialPolynomialLoss M n j r x y| /
          (rate ka + B.base x y)))) := by
  have hpoint (j : ℕ) :
      B.initialComputedPrecisionMoment M n r R ks ka ss st coefficient ζ Lh Lρ j false 0 ≤
        8 * (B.initialClippedEndpointPrefixCharge M j { r with usage := r.terminal } ka
          coefficient + rowNormPow 4 P r.source.rate
            (retainedMask R.source (side P ks) B.padding ss)
            (retainedMask R.terminal (side P ka) B.padding st)
            (fun _ x y => min 1 (|B.initialPolynomialLoss M n j r x y| /
              (rate ka + B.base x y)))) := by
    unfold initialComputedPrecisionMoment
    simp only [Bool.not_false, Fin.isValue, and_self, ↓reduceIte]
    exact (min_le_right _ _).trans (min_le_right _ _)
  calc
    _ ≤ ∑ j ∈ s, w j * (8 *
        (B.initialClippedEndpointPrefixCharge M j { r with usage := r.terminal } ka
          coefficient + _)) := sum_le_sum fun j hj =>
      mul_le_mul_of_nonneg_left (hpoint j) (hw j hj)
    _ = 8 * ((∑ j ∈ s, w j * B.initialClippedEndpointPrefixCharge M j
        { r with usage := r.terminal } ka coefficient) + _) := by
      simp only [mul_add, sum_add_distrib, mul_sum]
      congr 1 <;> apply sum_congr rfl <;> intros <;> ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add
      (B.initialClippedEndpointPrefixCharge_weighted_le hcharge hrate H M ks ka ha hi
        { r with usage := r.terminal } hs ht htask s w hw coefficient) le_rfl) (by norm_num)

/-- The new first-mean minimum and all retained costs are nonnegative. -/
lemma initialComputedPrecisionMoment_nonneg (B : BudgetData HP P) (M n : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (hr : 0 ≤ r.source.rate)
    (R : RoleProfile 3) (ks ka : ℕ) (ss st : List (ZMod P))
    (coefficient ζ Lh Lρ : ℝ) (j : ℕ) (noise : Bool) (ν : Fin 2) :
    0 ≤ B.initialComputedPrecisionMoment M n r R ks ka ss st coefficient ζ Lh Lρ j noise ν := by
  have hold (isNoise : Bool) (coordinate : Fin 2) :=
    B.initialComputedRelativeMoment_nonneg M n r hr R ks ka ss st
    (fun i => B.initialRootGroupCharge M (dyadicSlack (Nat.log2 M + 1) i)
      { r with usage := r.terminal } coefficient)
    (fun i => B.initialRootGroupCharge_nonneg M (dyadicSlack (Nat.log2 M + 1) i)
      { r with usage := r.terminal } coefficient) ζ Lh Lρ j isNoise coordinate
  have holdCurrent := hold noise ν
  have holdMean := hold false 0
  have holdNoise := hold true 0
  have hsum := sum_nonneg (fun i (_ : i ∈ range (j + 1)) =>
    B.initialClippedRootGroupCharge_nonneg M (dyadicSlack (Nat.log2 M + 1) i)
      { r with usage := r.terminal } ka coefficient)
  have hrow := rowNormPow_nonneg (s := 4) (mul_nonneg (Nat.cast_nonneg P) hr)
    (X := retainedMask R.source (side P ks) B.padding ss)
    (Y := retainedMask R.terminal (side P ka) B.padding st)
    (fun _ x y => min 1 (|B.initialPolynomialLoss M n j r x y| / (rate ka + B.base x y)))
  have hep := B.initialClippedEndpointPrefixCharge_nonneg M j
    { r with usage := r.terminal } ka coefficient
  have hcenter := B.initialComputedCenteredNoise_nonneg M r hr R ks ka ss st coefficient j
  have hnormalized := B.initialComputedNormalizedNoise_nonneg M r hr R ks ka ss st coefficient j
  have hsparse := B.initialSecondNoiseMoment_nonneg M r ζ j
  unfold initialComputedPrecisionMoment
  split_ifs <;> positivity

/-- Weighted actual first-noise minima retain the supported semantic residual.
The transported payment keeps sixteenth-power decay before roots are summed. No
semantic bound, parent accuracy or event-rarity discount is supplied by this theorem. -/
theorem initialComputedPrecisionMoment_firstNoise_weighted_le (B : BudgetData HP P)
    (M n ks ka : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hr : 0 ≤ r.source.rate) (hadm : B.initialNormalizedNoiseAdmissible M r ka)
    (R : RoleProfile 3) (ss st : List (ZMod P)) (coefficient ζ Lh Lρ : ℝ)
    (s : Finset ℕ) (w : ℕ → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) :
    let K := initialNormalizedNoiseConstant B.binCap coefficient *
      (2 : ℝ) ^ (-B.requestPrecision M { r with usage := r.terminal }) *
      (2 : ℝ) ^ (-B.rankCharge)
    let S := fun j => B.initialRelativeNoiseBudget M r R.source R.terminal
      R.source_terminal ks ka ss st B.base (j + 1)
    let a := fun j => B.initialComputedPrecisionMoment M n r R ks ka ss st coefficient
      ζ Lh Lρ j true 0
    (∑ j ∈ s, w j * a j ^ (4⁻¹ : ℝ)) ≤
      (8 : ℝ) ^ (4⁻¹ : ℝ) *
        (K * (∑ j ∈ s, w j * (1 / 16 : ℝ) ^ dyadicSlack (Nat.log2 M + 1) j) +
          ∑ j ∈ s, w j * S j ^ (4⁻¹ : ℝ)) ∧
    (∑ j ∈ s, w j * a j) ≤
      8 * (K ^ 4 * (∑ j ∈ s, w j *
        ((1 / 16 : ℝ) ^ dyadicSlack (Nat.log2 M + 1) j) ^ 4) +
          ∑ j ∈ s, w j * S j) := by
  extract_lets K S a
  have hcap := B.binCap_nonneg
  have hsum : 0 ≤ ∑' h, LogSpaceEstimation.scaleMajorant h :=
    tsum_nonneg LogSpaceEstimation.scaleMajorant_nonneg
  have hK : 0 ≤ K := by dsimp only [K, initialNormalizedNoiseConstant]; positivity
  have hS (j : ℕ) : 0 ≤ S j := B.initialRelativeNoiseBudget_nonneg M r hr
    R.source R.terminal R.source_terminal ks ka ss st B.base (j + 1)
  have hpoint (j : ℕ) : a j ≤
      8 * ((K * (1 / 16 : ℝ) ^ dyadicSlack (Nat.log2 M + 1) j) ^ 4 + S j) := by
    change B.initialComputedPrecisionMoment M n r R ks ka ss st coefficient ζ Lh Lρ
      j true 0 ≤ B.initialComputedNormalizedNoise M r R ks ka ss st coefficient j
    simp only [initialComputedPrecisionMoment, initialComputedCenteredNoise,
      Bool.not_true, Bool.false_eq_true, false_and, ↓reduceIte, and_self, hadm]
    exact (min_le_right _ _).trans (min_le_right _ _)
  have hroot (j : ℕ) : a j ^ (4⁻¹ : ℝ) ≤
      (8 : ℝ) ^ (4⁻¹ : ℝ) *
        (K * (1 / 16 : ℝ) ^ dyadicSlack (Nat.log2 M + 1) j + S j ^ (4⁻¹ : ℝ)) := by
    have hn := B.initialComputedPrecisionMoment_nonneg M n r hr R ks ka ss st
      coefficient ζ Lh Lρ j true 0
    have h := Real.rpow_le_rpow hn (hpoint j) (by norm_num : (0 : ℝ) ≤ 4⁻¹)
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 8)
      (add_nonneg (by positivity) (hS j))] at h
    apply h.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply (Real.rpow_add_le_add_rpow (by positivity) (hS j) (by norm_num) (by norm_num)).trans
    have he : ((K * (1 / 16 : ℝ) ^ dyadicSlack (Nat.log2 M + 1) j) ^ 4) ^
        (4⁻¹ : ℝ) = K * (1 / 16 : ℝ) ^ dyadicSlack (Nat.log2 M + 1) j := by
      convert Real.pow_rpow_inv_natCast (by positivity :
        0 ≤ K * (1 / 16 : ℝ) ^ dyadicSlack (Nat.log2 M + 1) j)
        (by decide : (4 : ℕ) ≠ 0) using 1
    rw [he]
  constructor
  · apply (sum_le_sum fun j hj => mul_le_mul_of_nonneg_left (hroot j) (hw j hj)).trans_eq
    simp only [mul_add, sum_add_distrib, mul_sum]
    congr 1 <;> apply sum_congr rfl <;> intros <;> ring
  · apply (sum_le_sum fun j hj => mul_le_mul_of_nonneg_left (hpoint j) (hw j hj)).trans_eq
    simp only [mul_add, sum_add_distrib, mul_sum, mul_pow]
    congr 1 <;> apply sum_congr rfl <;> intros <;> ring

/-- All four literal first-noise allocations from the actual computed minimum.
Only transported noise is absorbed here. The supported semantic budget remains explicit
at every prefix, including the unconditional factor-28 tail; there is no rarity discount.
The already assembled first mean and both second-coordinate costs are unchanged. -/
theorem initialComputedPrecisionMoment_firstNoise_schedule_le (B : BudgetData HP P)
    (M n ks ka : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hr : 0 ≤ r.source.rate) (hadm : B.initialNormalizedNoiseAdmissible M r ka)
    (R : RoleProfile 3) (ss st : List (ZMod P)) (coefficient ζ Lh Lρ floor Rraw : ℝ)
    (hf : 0 < floor) :
    let m := Nat.log2 M + 1
    let K := initialNormalizedNoiseConstant B.binCap coefficient *
      (2 : ℝ) ^ (-B.requestPrecision M { r with usage := r.terminal }) *
      (2 : ℝ) ^ (-B.rankCharge)
    let S := fun j => B.initialRelativeNoiseBudget M r R.source R.terminal
      R.source_terminal ks ka ss st B.base (j + 1)
    let a := fun j => B.initialComputedPrecisionMoment M n r R ks ka ss st coefficient
      ζ Lh Lρ j true 0
    let w := fun j => 64 * (HP.K : ℝ) * Rraw ^ 4 /
      ((compatibleCapacity HP.K m j : ℝ) * dyadicFloor floor m j ^ 4)
    (∑ j ∈ range m, dyadicFloor floor m j * a j ^ (4⁻¹ : ℝ)) ≤
      (8 : ℝ) ^ (4⁻¹ : ℝ) * (K * floor / 511 +
        ∑ j ∈ range m, dyadicFloor floor m j * S j ^ (4⁻¹ : ℝ)) ∧
    a (Nat.log2 M) ^ (4⁻¹ : ℝ) ≤
      (8 : ℝ) ^ (4⁻¹ : ℝ) * (K / 16 + S (Nat.log2 M) ^ (4⁻¹ : ℝ)) ∧
    (∑ j ∈ range m, (28 : ℝ) ^ (m - j) * a j ^ (4⁻¹ : ℝ)) ≤
      (8 : ℝ) ^ (4⁻¹ : ℝ) * (K * (1792 / 57) +
        ∑ j ∈ range m, (28 : ℝ) ^ (m - j) * S j ^ (4⁻¹ : ℝ)) ∧
    (∑ j ∈ range m, w j * a j) ≤
      8 * ((64 * (HP.K : ℝ) * Rraw ^ 4 / ((HP.K + 1) * floor ^ 4)) *
        K ^ 4 / 63 + ∑ j ∈ range m, w j * S j) := by
  extract_lets m K S a w
  have hcap := B.binCap_nonneg
  have hsum : 0 ≤ ∑' h, LogSpaceEstimation.scaleMajorant h :=
    tsum_nonneg LogSpaceEstimation.scaleMajorant_nonneg
  have hK : 0 ≤ K := by dsimp only [K, initialNormalizedNoiseConstant]; positivity
  have halloc := compatible_sixteenth_noise_schedule hf (by norm_num : (0 : ℝ) ≤ 1)
    HP.K m Rraw (fun j => (1 / 16 : ℝ) ^ dyadicSlack m j)
    (by intro j _; exact ⟨by positivity, by rw [one_mul]⟩)
  simp only [mul_one, one_mul, one_pow] at halloc
  have hpre := (B.initialComputedPrecisionMoment_firstNoise_weighted_le M n ks ka r
    hr hadm R ss st coefficient ζ Lh Lρ (range m) (dyadicFloor floor m)
    (fun j _ => dyadicFloor_nonneg hf.le m j)).1
  have hfinal := (B.initialComputedPrecisionMoment_firstNoise_weighted_le M n ks ka r
    hr hadm R ss st coefficient ζ Lh Lρ {Nat.log2 M} (fun _ => 1)
    (by intros; norm_num)).1
  have htail := (B.initialComputedPrecisionMoment_firstNoise_weighted_le M n ks ka r
    hr hadm R ss st coefficient ζ Lh Lρ (range m) (fun j => (28 : ℝ) ^ (m - j))
    (by intros; positivity)).1
  have hraw := (B.initialComputedPrecisionMoment_firstNoise_weighted_le M n ks ka r
    hr hadm R ss st coefficient ζ Lh Lρ (range m) w (by
      intro j _
      have hh := (dyadicFloor_pos hf m j).le
      dsimp only [w]
      positivity)).2
  refine ⟨hpre.trans ?_, ?_, htail.trans ?_, hraw.trans ?_⟩
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply add_le_add _ le_rfl
    convert mul_le_mul_of_nonneg_left halloc.1 hK using 1; ring
  · simpa only [sum_singleton, one_mul, dyadicSlack, Nat.add_sub_cancel,
      Nat.sub_self, pow_zero, pow_one, mul_one_div] using hfinal
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact add_le_add (mul_le_mul_of_nonneg_left halloc.2.2.1 hK) le_rfl
  · apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 8)
    apply add_le_add _ le_rfl
    convert mul_le_mul_of_nonneg_left halloc.2.2.2 (pow_nonneg hK 4) using 1; ring

/-- Complete first-noise allocation, combining canonical semantic support with
transported own-request error in the actual minimum. Tail propagation is unconditional
at the literal root-level factor 28. The structural coefficient has no request dependence. -/
theorem initialComputedPrecisionMoment_firstNoise_polynomial_schedule (B : BudgetData HP P)
    (hcharge : 0 ≤ B.rankCharge) (hrate : B.binRate = rate)
    (hcutoff : B.cutoff = fun i => boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1)
      rate 1 i (fun _ => 1))
    (H : Horizon P) (hi : ∀ bin ∈ B.bins, bin ≤ H.maxExponent)
    (M n ks ka : ℕ) (hM : 0 < M)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (R : RoleProfile 3)
    (ss st : List (ZMod P))
    (hs : r.source = gridChannel R.source ks ss)
    (ht : r.terminal = gridChannel R.terminal ka st)
    (htask : r.task = .row 0 (.pilotInput ⟨0, HP.k_pos⟩))
    (ha : ka ≤ H.maxExponent) (hp : 0 ≤ B.requestPrecision M r)
    (hbase : ∀ x y, 0 ≤ B.base x y) (hrow : B.base *ᵥ 1 ≤ 1)
    (coefficient ζ Lh Lρ floor Rraw : ℝ) (hf : 0 < floor) :
    let m := Nat.log2 M + 1
    let K := 2 * (initialNormalizedNoiseConstant B.binCap coefficient + 256 * B.binCap) *
      (2 : ℝ) ^ (-B.requestPrecision M r) * (2 : ℝ) ^ (-B.rankCharge)
    let a := fun j => B.initialComputedPrecisionMoment M n r R ks ka ss st coefficient
      ζ Lh Lρ j true 0
    (∑ j ∈ range m, dyadicFloor floor m j * a j ^ (4⁻¹ : ℝ)) ≤ floor * K / 511 ∧
    a (Nat.log2 M) ^ (4⁻¹ : ℝ) ≤ K / 4 ∧
    (∑ j ∈ range m, (28 : ℝ) ^ (m - j) * a j ^ (4⁻¹ : ℝ)) ≤ K * (458752 / 57) ∧
    (∑ j ∈ range m, (64 * (HP.K : ℝ) * Rraw ^ 4 /
      ((compatibleCapacity HP.K m j : ℝ) * dyadicFloor floor m j ^ 4)) * a j) ≤
      (64 * (HP.K : ℝ) * Rraw ^ 4 / ((HP.K + 1) * floor ^ 4)) * K ^ 4 / 63 := by
  extract_lets m K a
  have hcap := B.binCap_nonneg
  have hsum : 0 ≤ ∑' h, LogSpaceEstimation.scaleMajorant h :=
    tsum_nonneg LogSpaceEstimation.scaleMajorant_nonneg
  have hK : 0 ≤ K := by dsimp only [K, initialNormalizedNoiseConstant]; positivity
  have hr : 0 ≤ r.source.rate := by rw [hs]; exact (rate_pos ks).le
  have hadm : B.initialNormalizedNoiseAdmissible M r ka :=
    ⟨hcharge, hrate, htask, hp, H, ha, hi⟩
  have hpoint (j : ℕ) (hj : j < m) : a j ≤
      (K * (1 / 4 : ℝ) ^ dyadicSlack m j) ^ 4 := by
    have hn : a j ≤ B.initialComputedNormalizedNoise M r R ks ka ss st coefficient j := by
      simp only [a, initialComputedPrecisionMoment, initialComputedCenteredNoise,
        Bool.not_true, Bool.false_eq_true, false_and, ↓reduceIte, and_self, hadm]
      exact (min_le_right _ _).trans (min_le_right _ _)
    exact hn.trans (B.initialComputedNormalizedNoise_polynomial_uniform_le hcharge hrate
      hcutoff H hi M j ks ka hM hj r R ss st hs ht htask ha hp hbase hrow coefficient)
  have han (j : ℕ) : 0 ≤ a j := B.initialComputedPrecisionMoment_nonneg M n r hr R ks ka
    ss st coefficient ζ Lh Lρ j true 0
  have he (j : ℕ) (hj : j < m) :
      0 ≤ a j ^ (4⁻¹ : ℝ) ∧ a j ^ (4⁻¹ : ℝ) ≤ K * (1 / 4 : ℝ) ^ dyadicSlack m j := by
    refine ⟨Real.rpow_nonneg (han j) _, ?_⟩
    have h := Real.rpow_le_rpow (han j) (hpoint j hj) (by norm_num : (0 : ℝ) ≤ 4⁻¹)
    have heq : ((K * (1 / 4 : ℝ) ^ dyadicSlack m j) ^ 4) ^ (4⁻¹ : ℝ) =
        K * (1 / 4 : ℝ) ^ dyadicSlack m j := by
      convert Real.pow_rpow_inv_natCast (by positivity : 0 ≤ K * (1 / 4 : ℝ) ^ dyadicSlack m j)
        (by decide : (4 : ℕ) ≠ 0) using 1
    exact h.trans_eq heq
  obtain ⟨hpre, hfinal, htail, hraw⟩ := compatible_quarter_noise_schedule hf hK HP.K m
    Rraw (fun j => a j ^ (4⁻¹ : ℝ)) he
  refine ⟨hpre, hfinal _ (by dsimp only [m]; omega), htail, ?_⟩
  have hpow (j : ℕ) : (a j ^ (4⁻¹ : ℝ)) ^ 4 = a j := by
    convert Real.rpow_inv_natCast_pow (han j) (by decide : (4 : ℕ) ≠ 0) using 1
  simpa only [hpow] using hraw

/-- The telescoped endpoint and semantic deficit remain separate after taking roots.
This is a bound on the actual first-mean cost consumed by the computed reserve. -/
theorem initialComputedPrecisionMoment_first_root_le (B : BudgetData HP P)
    (hcharge : 0 ≤ B.rankCharge) (hrate : B.binRate = rate) (H : Horizon P)
    (M n j ks ka : ℕ) (ha : ka ≤ H.maxExponent)
    (hi : ∀ bin ∈ B.bins, bin ≤ H.maxExponent)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (hr : 0 ≤ r.source.rate)
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka)
    (htask : r.task = .row 0 (.pilotInput ⟨0, HP.k_pos⟩))
    (R : RoleProfile 3) (ss st : List (ZMod P)) (coefficient ζ Lh Lρ : ℝ) :
    B.initialComputedPrecisionMoment M n r R ks ka ss st coefficient ζ Lh Lρ j false 0 ^
        (4⁻¹ : ℝ) ≤
      (8 : ℝ) ^ (4⁻¹ : ℝ) *
        (((max (512 * (6 * B.binCap + 3) ^ 3) (32768 * B.binCap ^ 3)) ^ (4⁻¹ : ℝ) *
          |coefficient| * (2 : ℝ) ^ (-B.requestPrecision M r) * (2 : ℝ) ^ (-B.rankCharge)) *
          B.initialClippedEndpointWindow M j ka { r with usage := r.terminal } +
        (rowNormPow 4 P r.source.rate (retainedMask R.source (side P ks) B.padding ss)
          (retainedMask R.terminal (side P ka) B.padding st)
          (fun _ x y => min 1 (|B.initialPolynomialLoss M n j r x y| /
            (rate ka + B.base x y)))) ^ (4⁻¹ : ℝ)) := by
  let E := B.initialClippedEndpointPrefixCharge M j { r with usage := r.terminal } ka coefficient
  let D := rowNormPow 4 P r.source.rate (retainedMask R.source (side P ks) B.padding ss)
    (retainedMask R.terminal (side P ka) B.padding st)
    (fun _ x y => min 1 (|B.initialPolynomialLoss M n j r x y| / (rate ka + B.base x y)))
  have hE : 0 ≤ E := B.initialClippedEndpointPrefixCharge_nonneg M j _ ka coefficient
  have hD : 0 ≤ D := rowNormPow_nonneg (mul_nonneg (Nat.cast_nonneg P) hr) _
  have hp : B.initialComputedPrecisionMoment M n r R ks ka ss st coefficient ζ Lh Lρ j false 0 ≤
      8 * (E + D) := by
    unfold initialComputedPrecisionMoment
    simp only [Bool.not_false, Fin.isValue, and_self, ↓reduceIte]
    exact (min_le_right _ _).trans (min_le_right _ _)
  have hcost := B.initialComputedPrecisionMoment_nonneg M n r hr R ks ka ss st
    coefficient ζ Lh Lρ j false 0
  have hroot := Real.rpow_le_rpow hcost hp (by norm_num : (0 : ℝ) ≤ 4⁻¹)
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 8) (add_nonneg hE hD)] at hroot
  apply hroot.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply (Real.rpow_add_le_add_rpow hE hD (by norm_num) (by norm_num)).trans
  apply add_le_add _ le_rfl
  have hb := B.initialClippedEndpointPrefixCharge_sum_root_le hcharge hrate H M ks ka ha hi
    { r with usage := r.terminal } hs ht htask {j} (fun _ => 1) (by simp) coefficient
  simpa only [sum_singleton, one_mul, mul_one, requestPrecision, E] using hb

/-- Paid deterministic first-coordinate tail: telescoped child endpoints have a
geometric payment; the semantic deficit keeps its literal rarity-weighted rooted sum. -/
@[expose] def initialComputedFirstTailBudget (B : BudgetData HP P) (M n : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (R : RoleProfile 3)
    (ks ka : ℕ) (ss st : List (ZMod P)) (coefficient floor : ℝ) : ℝ :=
  let m := Nat.log2 M + 1
  let q := fun j => ((2 + 256 / dyadicFloor floor m j) /
    (compatibleCapacity HP.K m j : ℝ)) ^ (4⁻¹ : ℝ)
  let K := (max (512 * (6 * B.binCap + 3) ^ 3) (32768 * B.binCap ^ 3)) ^ (4⁻¹ : ℝ) *
    |coefficient| * (2 : ℝ) ^ (-B.requestPrecision M r) * (2 : ℝ) ^ (-B.rankCharge)
  let D := fun i => rowNormPow 4 P r.source.rate
    (retainedMask R.source (side P ks) B.padding ss)
    (retainedMask R.terminal (side P ka) B.padding st)
    (fun _ x y => min 1 (|B.initialPolynomialLoss M n i r x y| / (rate ka + B.base x y)))
  (8 : ℝ) ^ (4⁻¹ : ℝ) *
    (K * ((2 + 256 / floor) ^ (4⁻¹ : ℝ) *
      (4 * ∑' h, LogSpaceEstimation.scaleMajorant h) / 63) +
      ∑ j ∈ range m, q j * ∑ i ∈ Ico j m, (28 : ℝ) ^ (m - i) * D i ^ (4⁻¹ : ℝ))

/-- The actual computed first-mean roots, including all large-slack prefixes, receive
this payment. No bounded-slack window condition or parent accuracy is assumed. -/
theorem initialComputedPrecisionMoment_first_tail_le (B : BudgetData HP P)
    (hcharge : 0 ≤ B.rankCharge) (hrate : B.binRate = rate) (H : Horizon P)
    (M n ks ka : ℕ) (ha : ka ≤ H.maxExponent)
    (hi : ∀ bin ∈ B.bins, bin ≤ H.maxExponent)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (hr : 0 ≤ r.source.rate)
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka)
    (htask : r.task = .row 0 (.pilotInput ⟨0, HP.k_pos⟩))
    (R : RoleProfile 3) (ss st : List (ZMod P)) (coefficient ζ Lh Lρ floor : ℝ)
    (hf : 0 < floor) :
    (∑ j ∈ range (Nat.log2 M + 1),
      (((2 + 256 / dyadicFloor floor (Nat.log2 M + 1) j) /
        (compatibleCapacity HP.K (Nat.log2 M + 1) j : ℝ)) ^ (4⁻¹ : ℝ)) *
      ∑ i ∈ Ico j (Nat.log2 M + 1), (28 : ℝ) ^ (Nat.log2 M + 1 - i) *
        B.initialComputedPrecisionMoment M n r R ks ka ss st coefficient ζ Lh Lρ i false 0 ^
          (4⁻¹ : ℝ)) ≤
      B.initialComputedFirstTailBudget M n r R ks ka ss st coefficient floor := by
  unfold initialComputedFirstTailBudget
  extract_lets m q K D
  have hK : 0 ≤ K := by
    have hc := B.binCap_nonneg
    dsimp only [K]
    positivity
  have hq (j : ℕ) : 0 ≤ q j := by
    have hfl := dyadicFloor_pos hf m j
    exact Real.rpow_nonneg (by positivity) _
  have hwindow := compatible_growing_mean_tail_le hf
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4)
      (tsum_nonneg fun h => LogSpaceEstimation.scaleMajorant_nonneg h)) HP.K m
    (fun i => B.initialClippedEndpointWindow M i ka { r with usage := r.terminal })
    (fun i _ => B.initialClippedEndpointWindow_growing M i ka _)
  calc
    _ ≤ ∑ j ∈ range m, q j * ∑ i ∈ Ico j m, (28 : ℝ) ^ (m - i) *
        ((8 : ℝ) ^ (4⁻¹ : ℝ) *
          (K * B.initialClippedEndpointWindow M i ka { r with usage := r.terminal } +
            D i ^ (4⁻¹ : ℝ))) := by
      apply sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_left _ (hq j)
      apply sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left
        (B.initialComputedPrecisionMoment_first_root_le hcharge hrate H M n i ks ka
          ha hi r hr hs ht htask R ss st coefficient ζ Lh Lρ) (by positivity)
    _ = (8 : ℝ) ^ (4⁻¹ : ℝ) *
        (K * (∑ j ∈ range m, q j * ∑ i ∈ Ico j m,
          (28 : ℝ) ^ (m - i) * B.initialClippedEndpointWindow M i ka
            { r with usage := r.terminal }) +
          ∑ j ∈ range m, q j * ∑ i ∈ Ico j m,
            (28 : ℝ) ^ (m - i) * D i ^ (4⁻¹ : ℝ)) := by
      simp only [mul_add, sum_add_distrib, mul_sum]
      congr 1
      · apply sum_congr rfl
        intro j _
        apply sum_congr rfl
        intros
        ring
      · apply sum_congr rfl
        intro j _
        apply sum_congr rfl
        intros
        ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (add_le_add (mul_le_mul_of_nonneg_left hwindow hK) le_rfl) (by positivity)

/-- Uniform deterministic first-mean pre payment, retaining the semantic
omitted/inactive deficit separately. Structural charge is fixed in `B` before requests. -/
@[expose] def initialComputedFirstPreBudget (B : BudgetData HP P) (M n : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (R : RoleProfile 3)
    (ks ka : ℕ) (ss st : List (ZMod P)) (coefficient : ℝ) (floor : ℝ) : ℝ :=
  let m := Nat.log2 M + 1
  let K := (max (512 * (6 * B.binCap + 3) ^ 3) (32768 * B.binCap ^ 3)) ^ (4⁻¹ : ℝ) *
    |coefficient| * (2 : ℝ) ^ (-B.requestPrecision M r) * (2 : ℝ) ^ (-B.rankCharge)
  let E := 4 * ∑' h, LogSpaceEstimation.scaleMajorant h
  let D := fun i => rowNormPow 4 P r.source.rate
    (retainedMask R.source (side P ks) B.padding ss)
    (retainedMask R.terminal (side P ka) B.padding st)
    (fun _ x y => min 1 (|B.initialPolynomialLoss M n i r x y| / (rate ka + B.base x y)))
  (8 : ℝ) ^ (4⁻¹ : ℝ) * (K * (floor * E / 511) +
    ∑ i ∈ range m, dyadicFloor floor m i * D i ^ (4⁻¹ : ℝ))

/-- Uniform deterministic first-mean final payment, retaining the semantic
omitted/inactive deficit separately. Structural charge is fixed in `B` before requests. -/
@[expose] def initialComputedFirstFinalBudget (B : BudgetData HP P) (M n : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (R : RoleProfile 3)
    (ks ka : ℕ) (ss st : List (ZMod P)) (coefficient : ℝ) : ℝ :=
  let K := (max (512 * (6 * B.binCap + 3) ^ 3) (32768 * B.binCap ^ 3)) ^ (4⁻¹ : ℝ) *
    |coefficient| * (2 : ℝ) ^ (-B.requestPrecision M r) * (2 : ℝ) ^ (-B.rankCharge)
  let E := 4 * ∑' h, LogSpaceEstimation.scaleMajorant h
  let D := fun i => rowNormPow 4 P r.source.rate
    (retainedMask R.source (side P ks) B.padding ss)
    (retainedMask R.terminal (side P ka) B.padding st)
    (fun _ x y => min 1 (|B.initialPolynomialLoss M n i r x y| / (rate ka + B.base x y)))
  (8 : ℝ) ^ (4⁻¹ : ℝ) * (K * E + D (Nat.log2 M) ^ (4⁻¹ : ℝ))

/-- Uniform deterministic first-mean raw payment, retaining the semantic
omitted/inactive deficit separately. Structural charge is fixed in `B` before requests. -/
@[expose] def initialComputedFirstRawBudget (B : BudgetData HP P) (M n : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (R : RoleProfile 3)
    (ks ka : ℕ) (ss st : List (ZMod P)) (coefficient : ℝ) (floor Rraw : ℝ) : ℝ :=
  let m := Nat.log2 M + 1
  let K := (max (512 * (6 * B.binCap + 3) ^ 3) (32768 * B.binCap ^ 3)) ^ (4⁻¹ : ℝ) *
    |coefficient| * (2 : ℝ) ^ (-B.requestPrecision M r) * (2 : ℝ) ^ (-B.rankCharge)
  let E := 4 * ∑' h, LogSpaceEstimation.scaleMajorant h
  let D := fun i => rowNormPow 4 P r.source.rate
    (retainedMask R.source (side P ks) B.padding ss)
    (retainedMask R.terminal (side P ka) B.padding st)
    (fun _ x y => min 1 (|B.initialPolynomialLoss M n i r x y| / (rate ka + B.base x y)))
  8 * (K ^ 4 * ((64 * (HP.K : ℝ) * Rraw ^ 4 / ((HP.K + 1) * floor ^ 4)) * E ^ 4 / 63) +
    ∑ i ∈ range m, (64 * (HP.K : ℝ) * Rraw ^ 4 /
      ((compatibleCapacity HP.K m i : ℝ) * dyadicFloor floor m i ^ 4)) * D i)

/-- The stationary first-mean roots use the exact telescoped endpoints and floor. -/
theorem initialComputedPrecisionMoment_first_pre_le (B : BudgetData HP P)
    (hcharge : 0 ≤ B.rankCharge) (hrate : B.binRate = rate) (H : Horizon P)
    (M n ks ka : ℕ) (ha : ka ≤ H.maxExponent)
    (hi : ∀ bin ∈ B.bins, bin ≤ H.maxExponent)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (hr : 0 ≤ r.source.rate)
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka)
    (htask : r.task = .row 0 (.pilotInput ⟨0, HP.k_pos⟩))
    (R : RoleProfile 3) (ss st : List (ZMod P)) (coefficient ζ Lh Lρ : ℝ)
    (floor : ℝ) (hf : 0 ≤ floor) :
    (∑ j ∈ range (Nat.log2 M + 1), dyadicFloor floor (Nat.log2 M + 1) j *
      B.initialComputedPrecisionMoment M n r R ks ka ss st coefficient ζ Lh Lρ j false 0 ^
        (4⁻¹ : ℝ)) ≤
      B.initialComputedFirstPreBudget M n r R ks ka ss st coefficient floor := by
  let m := Nat.log2 M + 1
  let K := (max (512 * (6 * B.binCap + 3) ^ 3) (32768 * B.binCap ^ 3)) ^ (4⁻¹ : ℝ) *
    |coefficient| * (2 : ℝ) ^ (-B.requestPrecision M r) * (2 : ℝ) ^ (-B.rankCharge)
  let E := 4 * ∑' h, LogSpaceEstimation.scaleMajorant h
  let D := fun i => rowNormPow 4 P r.source.rate
    (retainedMask R.source (side P ks) B.padding ss)
    (retainedMask R.terminal (side P ka) B.padding st)
    (fun _ x y => min 1 (|B.initialPolynomialLoss M n i r x y| / (rate ka + B.base x y)))
  have hE : 0 ≤ E := mul_nonneg (by norm_num) (tsum_nonneg fun h =>
    LogSpaceEstimation.scaleMajorant_nonneg h)
  have hK : 0 ≤ K := by have hc := B.binCap_nonneg; dsimp only [K]; positivity
  have hg := compatible_growing_mean_pre_le hf hE m
    (fun i => B.initialClippedEndpointWindow M i ka { r with usage := r.terminal })
    (fun i _ => B.initialClippedEndpointWindow_growing M i ka _)
  change _ ≤ (8 : ℝ) ^ (4⁻¹ : ℝ) * (K * (floor * E / 511) + _)
  calc
    _ ≤ ∑ i ∈ range m, dyadicFloor floor m i * ((8 : ℝ) ^ (4⁻¹ : ℝ) *
      (K * B.initialClippedEndpointWindow M i ka { r with usage := r.terminal } +
        D i ^ (4⁻¹ : ℝ))) := by
      apply sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left
        (B.initialComputedPrecisionMoment_first_root_le hcharge hrate H M n i ks ka
          ha hi r hr hs ht htask R ss st coefficient ζ Lh Lρ) (dyadicFloor_nonneg hf m i)
    _ = (8 : ℝ) ^ (4⁻¹ : ℝ) * (K * (∑ i ∈ range m,
      dyadicFloor floor m i * B.initialClippedEndpointWindow M i ka
        { r with usage := r.terminal }) + _) := by
      simp only [mul_add, sum_add_distrib, mul_sum]
      congr 1 <;> apply sum_congr rfl <;> intros <;> ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (add_le_add (mul_le_mul_of_nonneg_left hg hK) le_rfl) (by positivity)

/-- Final slack is one, including when the scheduled child is zero. No positive
scheduled-child premise is inferred from positive parent precision. -/
theorem initialComputedPrecisionMoment_first_final_le (B : BudgetData HP P)
    (hcharge : 0 ≤ B.rankCharge) (hrate : B.binRate = rate) (H : Horizon P)
    (M n ks ka : ℕ) (ha : ka ≤ H.maxExponent)
    (hi : ∀ bin ∈ B.bins, bin ≤ H.maxExponent)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (hr : 0 ≤ r.source.rate)
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka)
    (htask : r.task = .row 0 (.pilotInput ⟨0, HP.k_pos⟩))
    (R : RoleProfile 3) (ss st : List (ZMod P)) (coefficient ζ Lh Lρ : ℝ) :
    B.initialComputedPrecisionMoment M n r R ks ka ss st coefficient ζ Lh Lρ
      (Nat.log2 M) false 0 ^ (4⁻¹ : ℝ) ≤
      B.initialComputedFirstFinalBudget M n r R ks ka ss st coefficient := by
  let K := (max (512 * (6 * B.binCap + 3) ^ 3) (32768 * B.binCap ^ 3)) ^ (4⁻¹ : ℝ) *
    |coefficient| * (2 : ℝ) ^ (-B.requestPrecision M r) * (2 : ℝ) ^ (-B.rankCharge)
  have hK : 0 ≤ K := by have hc := B.binCap_nonneg; dsimp only [K]; positivity
  have hslack : dyadicSlack (Nat.log2 M + 1) (Nat.log2 M) ≤ 16 * B.slack := by
    simp only [dyadicSlack, Nat.sub_self, pow_zero]
    have h := B.slack_pos
    omega
  have hg := B.initialClippedEndpointWindow_uniform M (Nat.log2 M) ka
    { r with usage := r.terminal } hslack
  apply (B.initialComputedPrecisionMoment_first_root_le hcharge hrate H M n
    (Nat.log2 M) ks ka ha hi r hr hs ht htask R ss st coefficient ζ Lh Lρ).trans
  exact mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left hg hK) le_rfl) (by positivity)

/-- Actual semantic first-mean moments after group zero in the joint fixed-depth,
bounded-budget family. The row width is paid using the bounded field horizon.
The initial inactive group, centered noises and second preparation are separate. -/
theorem initialPolynomialLoss_row_bounded_family (B : BudgetData HP P)
    (hcharge : 0 ≤ B.rankCharge) (M n j ks ka : ℕ) (hM : 1 < M) (hj : 0 < j)
    (hbins : B.bins = range (n + 1)) (hrate : B.binRate = rate)
    (hlo : B.slack * (1 + 4 * (n + ka)) < M)
    (hhi : M ≤ 32 * B.slack * n) (ha : 2 * ka ≤ n) (hP : P ≤ 2 ^ (n + 1))
    (H : Horizon P) (hks : ks ≤ H.maxExponent)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka)
    (hC : ∀ x y, 0 ≤ B.base x y) (R : RoleProfile 3) (ss st : List (ZMod P)) :
    rowNormPow 4 P r.source.rate
      (retainedMask R.source (side P ks) B.padding ss)
      (retainedMask R.terminal (side P ka) B.padding st)
      (fun _ x y => min 1 (|B.initialPolynomialLoss M n j r x y| /
        (rate ka + B.base x y))) ≤
      32 * ((2 : ℝ) ^ (-B.requestPrecision M r) *
        (2 : ℝ) ^ (-(B.rankCharge * r.task.rank))) ^ 4 := by
  have hc : ∀ bin ∈ B.bins, LogSpaceEstimation.scaleCutoff B.slack
      (B.sampleScale {r with usage := r.terminal} (some bin)) < M := by
    intro bin hb
    rw [hbins, mem_range] at hb
    exact B.retained_scaleCutoff_lt {r with usage := r.terminal} M n ka hrate ht hlo
      bin (by omega)
  have hz := B.initialInactiveCharge_eq_zero_of_pos M j hM hj r hc
  have hp (x y : ZMod P) :
      min 1 (|B.initialPolynomialLoss M n j r x y| / (rate ka + B.base x y)) ≤
        rate n / rate ka := by
    have hb := B.initialPolynomialLoss_div_le M n j ka r hrate hC x y
    rw [initialMeanCharge, hz, add_zero] at hb
    rw [abs_of_nonneg (B.initialPolynomialLoss_nonneg M n j r hrate hC x y)]
    exact (min_le_right _ _).trans hb
  rw [hs]
  exact (grid_row_moment_le B.padding R.source ks ss H hks _ _
    (div_nonneg (rate_pos n).le (rate_pos ka).le) (fun σ x y => by
      rw [abs_of_nonneg (le_min (by norm_num) (div_nonneg (abs_nonneg _)
        (add_nonneg (rate_pos ka).le (hC x y))))]
      exact hp x y)).trans
    (B.bounded_family_omission_row hcharge n M ks ka hhi ha hP r hs ht)

/-- Exceptional initial semantic row moment, paid with any literal exponential
weight at most 2⁻ᵈ. Unlike the positive-prefix bound this permits the full inactive
mass, uses the clipped bound one, and retains the structural rank salary. -/
theorem initialPolynomialLoss_first_weighted_family (B : BudgetData HP P)
    (M n ks ka q : ℕ) (hq : 1 ≤ q)
    (hlo : B.slack * (1 + 4 * (n + ka)) < M) (hP : P ≤ 2 ^ (n + 1))
    (H : Horizon P) (hks : ks ≤ H.maxExponent)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka)
    (hC : ∀ x y, 0 ≤ B.base x y)
    (R : RoleProfile 3) (ss st : List (ZMod P)) :
    (2 : ℝ) ^ (-(q : ℝ) * dyadicSlack (Nat.log2 M + 1) 0) *
      rowNormPow 4 P r.source.rate
        (retainedMask R.source (side P ks) B.padding ss)
        (retainedMask R.terminal (side P ka) B.padding st)
        (fun _ x y => min 1 (|B.initialPolynomialLoss M n 0 r x y| /
          (rate ka + B.base x y))) ≤
      32 * ((2 : ℝ) ^ (-B.requestPrecision M r) *
        (2 : ℝ) ^ (-(B.rankCharge * r.task.rank))) ^ 4 := by
  have hb : rowNormPow 4 P r.source.rate
      (retainedMask R.source (side P ks) B.padding ss)
      (retainedMask R.terminal (side P ka) B.padding st)
      (fun _ x y => min 1 (|B.initialPolynomialLoss M n 0 r x y| /
        (rate ka + B.base x y))) ≤ 16 * (P : ℝ) := by
    rw [hs]
    apply (grid_row_moment_le B.padding R.source ks ss H hks _ _
      (by norm_num : (0 : ℝ) ≤ 1) ?_).trans_eq (by ring)
    intro σ x y
    rw [abs_of_nonneg]
    · exact min_le_left _ _
    · exact le_min (by norm_num) (div_nonneg (abs_nonneg _)
        (add_nonneg (rate_pos ka).le (hC x y)))
  have he : (2 : ℝ) ^ (-(q : ℝ) * dyadicSlack (Nat.log2 M + 1) 0) ≤
      (2 : ℝ) ^ (-(dyadicSlack (Nat.log2 M + 1) 0 : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
    nlinarith [Nat.cast_nonneg (α := ℝ) (dyadicSlack (Nat.log2 M + 1) 0)]
  calc
    _ ≤ (2 : ℝ) ^ (-(q : ℝ) * dyadicSlack (Nat.log2 M + 1) 0) * (16 * (P : ℝ)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ ≤ (2 : ℝ) ^ (-(dyadicSlack (Nat.log2 M + 1) 0 : ℝ)) * (16 * (P : ℝ)) :=
      mul_le_mul_of_nonneg_right he (by positivity)
    _ = 16 * (P : ℝ) * (2 : ℝ) ^
        (-(dyadicSlack (Nat.log2 M + 1) 0 : ℝ)) := by ring
    _ ≤ _ := B.bounded_family_initial_row_decay n M ks ka hlo hP r hs ht

/-- One slope-one envelope pays every rooted semantic prefix, including the
exceptional inactive prefix. The same fixed structural rank salary survives both cases;
compatible schedule sums can therefore be applied without a horizon factor. -/
theorem initialPolynomialLoss_root_bounded_family (B : BudgetData HP P)
    (hcharge : 0 ≤ B.rankCharge) (M n j ks ka : ℕ) (hM : 1 < M)
    (hbins : B.bins = range (n + 1)) (hrate : B.binRate = rate)
    (hlo : B.slack * (1 + 4 * (n + ka)) < M)
    (hhi : M ≤ 32 * B.slack * n) (ha : 2 * ka ≤ n) (hP : P ≤ 2 ^ (n + 1))
    (H : Horizon P) (hks : ks ≤ H.maxExponent)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka)
    (hC : ∀ x y, 0 ≤ B.base x y) (R : RoleProfile 3) (ss st : List (ZMod P)) :
    rowNormPow 4 P r.source.rate
      (retainedMask R.source (side P ks) B.padding ss)
      (retainedMask R.terminal (side P ka) B.padding st)
      (fun _ x y => min 1 (|B.initialPolynomialLoss M n j r x y| /
        (rate ka + B.base x y))) ^ (4⁻¹ : ℝ) ≤
      ((32 : ℝ) ^ (4⁻¹ : ℝ) * (2 : ℝ) ^ (-B.requestPrecision M r) *
        (2 : ℝ) ^ (-(B.rankCharge * r.task.rank))) *
          (2 : ℝ) ^ dyadicSlack (Nat.log2 M + 1) j := by
  let D := rowNormPow 4 P r.source.rate
    (retainedMask R.source (side P ks) B.padding ss)
    (retainedMask R.terminal (side P ka) B.padding st)
    (fun _ x y => min 1 (|B.initialPolynomialLoss M n j r x y| /
      (rate ka + B.base x y)))
  let t := (2 : ℝ) ^ (-B.requestPrecision M r) *
    (2 : ℝ) ^ (-(B.rankCharge * r.task.rank))
  have hD : 0 ≤ D := rowNormPow_nonneg
    (by rw [hs]; exact mul_nonneg (Nat.cast_nonneg P) (rate_pos ks).le) _
  have htn : 0 ≤ t := by dsimp only [t]; positivity
  have hb : D ≤ 32 * (t * (2 : ℝ) ^ dyadicSlack (Nat.log2 M + 1) j) ^ 4 := by
    by_cases hj : j = 0
    · subst j
      have h := B.initialPolynomialLoss_first_weighted_family M n ks ka 4
        (by decide) hlo hP H hks r hs ht hC R ss st
      let d := dyadicSlack (Nat.log2 M + 1) 0
      have he : (2 : ℝ) ^ (-(4 : ℝ) * d) * (2 ^ d) ^ 4 = 1 := by
        rw [← pow_mul, ← Real.rpow_natCast, ← Real.rpow_add (by norm_num)]
        push_cast
        ring_nf
        norm_num
      have hw : 0 < (2 : ℝ) ^ (-(4 : ℝ) * d) := by positivity
      apply (mul_le_mul_iff_right₀ hw).mp
      change (2 : ℝ) ^ (-(4 : ℝ) * d) * D ≤ _ at h
      change (2 : ℝ) ^ (-(4 : ℝ) * d) * D ≤
        (2 : ℝ) ^ (-(4 : ℝ) * d) * (32 * (t * (2 : ℝ) ^ d) ^ 4)
      calc
        _ ≤ 32 * t ^ 4 := h
        _ = (32 * t ^ 4) * ((2 : ℝ) ^ (-(4 : ℝ) * d) * (2 ^ d) ^ 4) := by
          rw [he, mul_one]
        _ = _ := by ring
    · have hb := B.initialPolynomialLoss_row_bounded_family hcharge M n j ks ka hM
        (Nat.pos_of_ne_zero hj) hbins hrate hlo hhi ha hP H hks r hs ht hC R ss st
      exact hb.trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ htn (le_mul_of_one_le_right htn
          (one_le_pow₀ (by norm_num))) 4) (by norm_num : (0 : ℝ) ≤ 32))
  have hr := Real.rpow_le_rpow hD hb (by norm_num : (0 : ℝ) ≤ 4⁻¹)
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 32) (by positivity)] at hr
  have he : ((t * (2 : ℝ) ^ dyadicSlack (Nat.log2 M + 1) j) ^ 4) ^
      (4⁻¹ : ℝ) = t * (2 : ℝ) ^ dyadicSlack (Nat.log2 M + 1) j := by
    convert Real.pow_rpow_inv_natCast (by positivity : 0 ≤ t * (2 : ℝ) ^
      dyadicSlack (Nat.log2 M + 1) j) (by decide : (4 : ℕ) ≠ 0) using 1
  rw [he] at hr
  simpa only [t, mul_assoc] using hr

/-- All three literal exceptional-group weights pay the actual clipped semantic
row moment. Raw uses prefix one (index zero), not the next schedule coefficient.
The tail is deterministic; no centered noise receives this rarity factor. These are
component payments, not an assembled reserve or recursive availability certificate. -/
theorem initialPolynomialLoss_first_schedule_family (B : BudgetData HP P)
    (M n ks ka : ℕ)
    (hlo : B.slack * (1 + 4 * (n + ka)) < M) (hP : P ≤ 2 ^ (n + 1))
    (H : Horizon P) (hks : ks ≤ H.maxExponent)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka)
    (hC : ∀ x y, 0 ≤ B.base x y)
    (R : RoleProfile 3) (ss st : List (ZMod P)) (floor Rraw : ℝ) (hf : 0 < floor) :
    let m := Nat.log2 M + 1
    let D := rowNormPow 4 P r.source.rate
      (retainedMask R.source (side P ks) B.padding ss)
      (retainedMask R.terminal (side P ka) B.padding st)
      (fun _ x y => min 1 (|B.initialPolynomialLoss M n 0 r x y| /
        (rate ka + B.base x y)))
    let Q := 32 * ((2 : ℝ) ^ (-B.requestPrecision M r) *
      (2 : ℝ) ^ (-(B.rankCharge * r.task.rank))) ^ 4
    dyadicFloor floor m 0 ^ 4 * D ≤ floor ^ 4 * Q ∧
    (64 * (HP.K : ℝ) * Rraw ^ 4 /
      ((compatibleCapacity HP.K m 0 : ℝ) * dyadicFloor floor m 0 ^ 4)) * D ≤
      (64 * (HP.K : ℝ) * Rraw ^ 4 / ((HP.K + 1) * floor ^ 4)) * Q ∧
    ((((2 + 256 / dyadicFloor floor m 0) / (compatibleCapacity HP.K m 0 : ℝ)) ^
      (4⁻¹ : ℝ)) * 28 ^ m) ^ 4 * D ≤
      ((2 + 256 / floor) ^ (4⁻¹ : ℝ)) ^ 4 * Q := by
  dsimp only
  let m := Nat.log2 M + 1
  let D := rowNormPow 4 P r.source.rate
    (retainedMask R.source (side P ks) B.padding ss)
    (retainedMask R.terminal (side P ka) B.padding st)
    (fun _ x y => min 1 (|B.initialPolynomialLoss M n 0 r x y| /
      (rate ka + B.base x y)))
  have hD : 0 ≤ D := rowNormPow_nonneg
    (by rw [hs]; exact mul_nonneg (Nat.cast_nonneg P) (rate_pos ks).le) _
  have hexp (k : ℕ) : ((1 / (2 : ℝ) ^ k) ^ dyadicSlack m 0) =
      (2 : ℝ) ^ (-(k : ℝ) * dyadicSlack m 0) := by
    rw [one_div, inv_pow, ← pow_mul, ← Real.rpow_natCast,
      ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    push_cast
    ring
  have h40 := B.initialPolynomialLoss_first_weighted_family M n ks ka 40
    (by decide) hlo hP H hks r hs ht hC R ss st
  have h24 := B.initialPolynomialLoss_first_weighted_family M n ks ka 24
    (by decide) hlo hP H hks r hs ht hC R ss st
  have hfloor : dyadicFloor floor m 0 ^ 4 =
      floor ^ 4 * (2 : ℝ) ^ (-(40 : ℝ) * dyadicSlack m 0) := by
    rw [dyadicFloor, mul_pow, ← pow_mul, Nat.mul_comm _ 4, pow_mul]
    have he := hexp 40
    norm_num only [Nat.cast_ofNat] at he
    convert congrArg (fun x : ℝ => floor ^ 4 * x) he using 1; norm_num
  have hraw := compatible_false_weight_eq floor HP.K m 0 Rraw
  have hrawexp : (1 / 16777216 : ℝ) ^ dyadicSlack m 0 =
      (2 : ℝ) ^ (-(24 : ℝ) * dyadicSlack m 0) := by
    convert hexp 24 using 1; norm_num
  have htail := compatible_first_rarity_decay hf HP.K m (by dsimp only [m]; omega)
  have htailexp : ((1 / 64 : ℝ) ^ dyadicSlack m 0) ^ 4 =
      (2 : ℝ) ^ (-(24 : ℝ) * dyadicSlack m 0) := by
    rw [← pow_mul, Nat.mul_comm _ 4, pow_mul]
    convert hexp 24 using 1; norm_num
  refine ⟨?_, ?_, ?_⟩
  · rw [hfloor, mul_assoc]
    exact mul_le_mul_of_nonneg_left h40 (by positivity)
  · rw [hraw, hrawexp, mul_assoc]
    exact mul_le_mul_of_nonneg_left h24 (by positivity)
  · have ht0 : 0 ≤ ((2 + 256 / dyadicFloor floor m 0) /
        (compatibleCapacity HP.K m 0 : ℝ)) ^ (4⁻¹ : ℝ) * 28 ^ m := by
      have hh := (dyadicFloor_pos hf m 0).le
      positivity
    apply (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ht0 htail 4) hD).trans
    rw [mul_pow, htailexp, mul_assoc]
    exact mul_le_mul_of_nonneg_left h24 (by positivity)

/-- The three literal first-mean payments are nonnegative. -/
lemma initialComputedFirstBudgets_nonneg (B : BudgetData HP P) (M n ks ka : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (hr : 0 ≤ r.source.rate)
    (R : RoleProfile 3) (ss st : List (ZMod P)) (coefficient floor : ℝ) (hf : 0 ≤ floor) :
    0 ≤ B.initialComputedFirstPreBudget M n r R ks ka ss st coefficient floor ∧
    0 ≤ B.initialComputedFirstFinalBudget M n r R ks ka ss st coefficient ∧
    0 ≤ B.initialComputedFirstTailBudget M n r R ks ka ss st coefficient floor := by
  let D := fun i => rowNormPow 4 P r.source.rate
    (retainedMask R.source (side P ks) B.padding ss)
    (retainedMask R.terminal (side P ka) B.padding st)
    (fun _ x y => min 1 (|B.initialPolynomialLoss M n i r x y| /
      (rate ka + B.base x y)))
  have hroot (i : ℕ) : 0 ≤ D i ^ (4⁻¹ : ℝ) := Real.rpow_nonneg
    (rowNormPow_nonneg (mul_nonneg (Nat.cast_nonneg P) hr) _) _
  have hE : 0 ≤ ∑' h, LogSpaceEstimation.scaleMajorant h :=
    tsum_nonneg fun h => LogSpaceEstimation.scaleMajorant_nonneg h
  have hcap := B.binCap_nonneg
  refine ⟨?_, ?_, ?_⟩
  · unfold initialComputedFirstPreBudget
    apply mul_nonneg (by positivity)
    apply add_nonneg (by positivity)
    exact sum_nonneg fun i _ => mul_nonneg (dyadicFloor_nonneg hf _ _) (hroot i)
  · unfold initialComputedFirstFinalBudget
    exact mul_nonneg (by positivity) (add_nonneg (by positivity) (hroot _))
  · unfold initialComputedFirstTailBudget
    apply mul_nonneg (by positivity)
    apply add_nonneg (by positivity)
    apply sum_nonneg
    intro j _
    have hfl := dyadicFloor_nonneg hf (Nat.log2 M + 1) j
    apply mul_nonneg (Real.rpow_nonneg (by positivity) _)
    exact sum_nonneg fun i _ => mul_nonneg (by positivity) (hroot i)

/-- The first coordinate's actual numerical reserve: complete deterministic first-mean
budgets plus the computed first-noise minimum. The second mean and noise are excluded. -/
@[expose] def initialComputedFirstCoordinateReserve (B : BudgetData HP P) (M n : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (R : RoleProfile 3)
    (ks ka : ℕ) (ss st : List (ZMod P)) (coefficient ζ Lh Lρ floor cap C Cpre : ℝ) : ℝ :=
  let m := Nat.log2 M + 1
  let a := fun j => B.initialComputedPrecisionMoment M n r R ks ka ss st coefficient ζ Lh Lρ
    j true 0
  let Rraw := (2 * max cap 16) ^ (4⁻¹ : ℝ)
  initialSeparatedReserve HP C Cpre
    (B.initialComputedFirstPreBudget M n r R ks ka ss st coefficient floor +
      ∑ j ∈ range m, dyadicFloor floor m j * a j ^ (4⁻¹ : ℝ))
    (B.initialComputedFirstFinalBudget M n r R ks ka ss st coefficient +
      a (Nat.log2 M) ^ (4⁻¹ : ℝ))
    (B.initialComputedFirstTailBudget M n r R ks ka ss st coefficient floor +
      ∑ j ∈ range m, (28 : ℝ) ^ (m - j) * a j ^ (4⁻¹ : ℝ))
    (64 * (B.initialComputedFirstRawBudget M n r R ks ka ss st coefficient floor Rraw +
      ∑ j ∈ range m, (64 * (HP.K : ℝ) * Rraw ^ 4 /
        ((compatibleCapacity HP.K m j : ℝ) * dyadicFloor floor m j ^ 4)) * a j))

/-- Homogeneous scalar envelope for complete first-coordinate reserve allocation.
The noise tail retains unconditional factor-28 propagation; only the deterministic
mean term carries the rarity coefficient. All constants are primitive structural data. -/
@[expose] def initialFirstCoordinatePayment (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (floor cap C Cpre x : ℝ) : ℝ :=
  initialSeparatedReserve HP C Cpre
    (((8 : ℝ) ^ (4⁻¹ : ℝ) + 1) * x * floor / 511)
    (((8 : ℝ) ^ (4⁻¹ : ℝ) + 1) * x)
    (((8 : ℝ) ^ (4⁻¹ : ℝ) * (2 + 256 / floor) ^ (4⁻¹ : ℝ) / 63 + 458752 / 57) * x)
    (64 * 9 * x ^ 4 * (64 * (HP.K : ℝ) * ((2 * max cap 16) ^ (4⁻¹ : ℝ)) ^ 4 /
      ((HP.K + 1) * floor ^ 4)) / 63)

/-- A charge is chosen before precision and requests for the homogeneous first-coordinate
payment. This scalar fact alone asserts neither semantic hypotheses nor recursive success. -/
theorem initialFirstCoordinatePayment_exists_charge
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (floor cap C Cpre L : ℝ) :
    ∃ A : ℕ, ∀ t : ℝ, initialFirstCoordinatePayment HP floor cap C Cpre
      (L * (2 : ℝ) ^ (-(A : ℝ)) * t) ≤ t ^ 4 := by
  let F := initialFirstCoordinatePayment HP floor cap C Cpre
  have hhom (x y : ℝ) : F (x * y) = F x * y ^ 4 := by
    dsimp only [F, initialFirstCoordinatePayment, initialSeparatedReserve]
    ring
  obtain ⟨A, hA⟩ := exists_nat_gt (F L)
  have hpow : (A : ℝ) ≤ (2 : ℝ) ^ A := by
    exact_mod_cast (Nat.lt_two_pow_self (n := A)).le
  have hlarge : F L ≤ ((2 : ℝ) ^ A) ^ 4 :=
    hA.le.trans (hpow.trans (le_self_pow₀ (one_le_pow₀ (by norm_num)) (by decide : 4 ≠ 0)))
  refine ⟨A, fun t => ?_⟩
  change F (L * ((2 : ℝ) ^ (-(A : ℝ))) * t) ≤ t ^ 4
  rw [mul_assoc, hhom, mul_pow, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
  have hp : (0 : ℝ) < 2 ^ A := by positivity
  have hh := mul_le_mul_of_nonneg_right hlarge (by positivity : 0 ≤ ((2 : ℝ) ^ A)⁻¹ ^ 4)
  rw [← mul_pow, mul_inv_cancel₀ hp.ne', one_pow] at hh
  calc
    F L * ((((2 : ℝ) ^ A)⁻¹) ^ 4 * t ^ 4) =
      (F L * (((2 : ℝ) ^ A)⁻¹) ^ 4) * t ^ 4 := by ring
    _ ≤ 1 * t ^ 4 := mul_le_mul_of_nonneg_right hh (by positivity)
    _ = _ := one_mul _

/-- First-coordinate separated-reserve assembly with the actual computed noise minimum.
The complete existing first-mean budgets are preserved. Supported semantic noise remains
as four explicit residuals; this is not a paid combined certificate or a total reserve
bound, and it makes no claim of joint successful recursion. -/
theorem initialComputedFirstCoordinate_reserve_le (B : BudgetData HP P)
    (M n ks ka : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hr : 0 ≤ r.source.rate) (hadm : B.initialNormalizedNoiseAdmissible M r ka)
    (R : RoleProfile 3) (ss st : List (ZMod P))
    (coefficient ζ Lh Lρ floor cap C Cpre : ℝ) (hf : 0 < floor) :
    let m := Nat.log2 M + 1
    let K := initialNormalizedNoiseConstant B.binCap coefficient *
      (2 : ℝ) ^ (-B.requestPrecision M { r with usage := r.terminal }) *
      (2 : ℝ) ^ (-B.rankCharge)
    let S := fun j => B.initialRelativeNoiseBudget M r R.source R.terminal
      R.source_terminal ks ka ss st B.base (j + 1)
    let a := fun j => B.initialComputedPrecisionMoment M n r R ks ka ss st coefficient
      ζ Lh Lρ j true 0
    let Rraw := (2 * max cap 16) ^ (4⁻¹ : ℝ)
    let w := fun j => 64 * (HP.K : ℝ) * Rraw ^ 4 /
      ((compatibleCapacity HP.K m j : ℝ) * dyadicFloor floor m j ^ 4)
    let μpre := B.initialComputedFirstPreBudget M n r R ks ka ss st coefficient floor
    let μfinal := B.initialComputedFirstFinalBudget M n r R ks ka ss st coefficient
    let μtail := B.initialComputedFirstTailBudget M n r R ks ka ss st coefficient floor
    let μraw := B.initialComputedFirstRawBudget M n r R ks ka ss st coefficient floor Rraw
    initialSeparatedReserve HP C Cpre
      (μpre + ∑ j ∈ range m, dyadicFloor floor m j * a j ^ (4⁻¹ : ℝ))
      (μfinal + a (Nat.log2 M) ^ (4⁻¹ : ℝ))
      (μtail + ∑ j ∈ range m, (28 : ℝ) ^ (m - j) * a j ^ (4⁻¹ : ℝ))
      (64 * (μraw + ∑ j ∈ range m, w j * a j)) ≤
    initialSeparatedReserve HP C Cpre
      (μpre + (8 : ℝ) ^ (4⁻¹ : ℝ) * (K * floor / 511 +
        ∑ j ∈ range m, dyadicFloor floor m j * S j ^ (4⁻¹ : ℝ)))
      (μfinal + (8 : ℝ) ^ (4⁻¹ : ℝ) * (K / 16 + S (Nat.log2 M) ^ (4⁻¹ : ℝ)))
      (μtail + (8 : ℝ) ^ (4⁻¹ : ℝ) * (K * (1792 / 57) +
        ∑ j ∈ range m, (28 : ℝ) ^ (m - j) * S j ^ (4⁻¹ : ℝ)))
      (64 * (μraw + 8 * ((64 * (HP.K : ℝ) * Rraw ^ 4 /
        ((HP.K + 1) * floor ^ 4)) * K ^ 4 / 63 + ∑ j ∈ range m, w j * S j))) := by
  extract_lets m K S a Rraw w μpre μfinal μtail μraw
  obtain ⟨hp, hfinal, htail, hraw⟩ := B.initialComputedPrecisionMoment_firstNoise_schedule_le
    M n ks ka r hr hadm R ss st coefficient ζ Lh Lρ floor Rraw hf
  obtain ⟨hpn, hfn, htn⟩ := B.initialComputedFirstBudgets_nonneg M n ks ka r hr
    R ss st coefficient floor hf.le
  have ha (j : ℕ) : 0 ≤ a j := B.initialComputedPrecisionMoment_nonneg M n r hr R ks ka
    ss st coefficient ζ Lh Lρ j true 0
  apply initialSeparatedReserve_mono HP C Cpre
  · exact add_nonneg hpn (sum_nonneg fun j _ =>
      mul_nonneg (dyadicFloor_nonneg hf.le m j) (Real.rpow_nonneg (ha j) _))
  · exact add_nonneg hfn (Real.rpow_nonneg (ha _) _)
  · exact add_nonneg htn (sum_nonneg fun j _ =>
      mul_nonneg (by positivity) (Real.rpow_nonneg (ha j) _))
  · exact add_le_add le_rfl hp
  · exact add_le_add le_rfl hfinal
  · exact add_le_add le_rfl htail
  · exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hraw) (by norm_num : (0 : ℝ) ≤ 64)

/-- All four deterministic first-mean budgets share one scalar endpoint payment on
an explicit fixed-depth, bounded-budget family. Semantic loss includes the inactive
first group. This theorem neither asserts recursive child availability nor pays noise. -/
theorem initialComputedFirstBudgets_bounded_family (B : BudgetData HP P)
    (hcharge : 0 ≤ B.rankCharge) (M n ks ka : ℕ) (hM : 1 < M)
    (hbins : B.bins = range (n + 1)) (hrate : B.binRate = rate)
    (hlo : B.slack * (1 + 4 * (n + ka)) < M)
    (hhi : M ≤ 32 * B.slack * n) (ha : 2 * ka ≤ n) (hP : P ≤ 2 ^ (n + 1))
    (H : Horizon P) (hks : ks ≤ H.maxExponent)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka)
    (hC : ∀ x y, 0 ≤ B.base x y) (R : RoleProfile 3) (ss st : List (ZMod P))
    (coefficient floor Rraw : ℝ) (hf : 0 < floor) :
    let K := (max (512 * (6 * B.binCap + 3) ^ 3) (32768 * B.binCap ^ 3)) ^
      (4⁻¹ : ℝ) * |coefficient| * (2 : ℝ) ^ (-B.requestPrecision M r) *
        (2 : ℝ) ^ (-B.rankCharge)
    let S := (32 : ℝ) ^ (4⁻¹ : ℝ) * (2 : ℝ) ^ (-B.requestPrecision M r) *
      (2 : ℝ) ^ (-(B.rankCharge * r.task.rank))
    let x := 2 * (K * (4 * ∑' h, LogSpaceEstimation.scaleMajorant h) + S)
    B.initialComputedFirstPreBudget M n r R ks ka ss st coefficient floor ≤
      (8 : ℝ) ^ (4⁻¹ : ℝ) * x * floor / 511 ∧
    B.initialComputedFirstFinalBudget M n r R ks ka ss st coefficient ≤
      (8 : ℝ) ^ (4⁻¹ : ℝ) * x ∧
    B.initialComputedFirstTailBudget M n r R ks ka ss st coefficient floor ≤
      (8 : ℝ) ^ (4⁻¹ : ℝ) * x * (2 + 256 / floor) ^ (4⁻¹ : ℝ) / 63 ∧
    B.initialComputedFirstRawBudget M n r R ks ka ss st coefficient floor Rraw ≤
      8 * x ^ 4 * (64 * (HP.K : ℝ) * Rraw ^ 4 / ((HP.K + 1) * floor ^ 4)) / 63 := by
  extract_lets K S x
  let m := Nat.log2 M + 1
  let E := 4 * ∑' h, LogSpaceEstimation.scaleMajorant h
  let D := fun i => rowNormPow 4 P r.source.rate
    (retainedMask R.source (side P ks) B.padding ss)
    (retainedMask R.terminal (side P ka) B.padding st)
    (fun _ x y => min 1 (|B.initialPolynomialLoss M n i r x y| /
      (rate ka + B.base x y)))
  have hK : 0 ≤ K := by have hc := B.binCap_nonneg; dsimp only [K]; positivity
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have hE : 0 ≤ E := mul_nonneg (by norm_num)
    (tsum_nonneg fun h => LogSpaceEstimation.scaleMajorant_nonneg h)
  have hD (i : ℕ) : 0 ≤ D i := rowNormPow_nonneg
    (by rw [hs]; exact mul_nonneg (Nat.cast_nonneg P) (rate_pos ks).le) _
  have hg (i : ℕ) : D i ^ (4⁻¹ : ℝ) ≤ S * (2 : ℝ) ^ dyadicSlack m i :=
    B.initialPolynomialLoss_root_bounded_family hcharge M n i ks ka hM hbins hrate
      hlo hhi ha hP H hks r hs ht hC R ss st
  have hp := compatible_growing_mean_pre_le hf.le hS m
    (fun i => D i ^ (4⁻¹ : ℝ)) (fun i _ => hg i)
  have ht' := compatible_growing_mean_tail_le hf hS HP.K m
    (fun i => D i ^ (4⁻¹ : ℝ)) (fun i _ => hg i)
  have hr := compatible_growing_mean_raw_le hf HP.K m Rraw
    (fun i => D i ^ (4⁻¹ : ℝ))
    (fun i _ => ⟨Real.rpow_nonneg (hD i) _, hg i⟩)
  have hpow (i : ℕ) : (D i ^ (4⁻¹ : ℝ)) ^ 4 = D i := by
    convert Real.rpow_inv_natCast_pow (hD i) (by decide : (4 : ℕ) ≠ 0) using 1
  simp_rw [hpow] at hr
  have hfinal := hg (Nat.log2 M)
  have hd : dyadicSlack m (Nat.log2 M) = 1 := by simp [m, dyadicSlack]
  rw [hd, pow_one] at hfinal
  have hx : K * E + S ≤ x := by dsimp only [x, E]; nlinarith
  have hx0 : 0 ≤ x := (add_nonneg (mul_nonneg hK hE) hS).trans hx
  have hp4 : (K * E) ^ 4 + S ^ 4 ≤ x ^ 4 := by
    have hke := mul_nonneg hK hE
    have h1 := pow_le_pow_left₀ hke (show K * E ≤ x / 2 by dsimp only [x, E]; linarith) 4
    have h2 := pow_le_pow_left₀ hS (show S ≤ x / 2 by dsimp only [x, E]; linarith) 4
    nlinarith [pow_nonneg hx0 4]
  refine ⟨?_, ?_, ?_, ?_⟩
  · change (8 : ℝ) ^ (4⁻¹ : ℝ) * (K * (floor * E / 511) + _) ≤ _
    apply (mul_le_mul_of_nonneg_left (add_le_add_right hp _) (by positivity)).trans
    nlinarith [mul_le_mul_of_nonneg_left hx (by positivity :
      0 ≤ (8 : ℝ) ^ (4⁻¹ : ℝ) * floor / 511)]
  · change (8 : ℝ) ^ (4⁻¹ : ℝ) * (K * E + D (Nat.log2 M) ^ (4⁻¹ : ℝ)) ≤ _
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    dsimp only [x, E]
    nlinarith
  · change (8 : ℝ) ^ (4⁻¹ : ℝ) *
      (K * ((2 + 256 / floor) ^ (4⁻¹ : ℝ) * E / 63) + _) ≤ _
    apply (mul_le_mul_of_nonneg_left (add_le_add_right ht' _) (by positivity)).trans
    nlinarith [mul_le_mul_of_nonneg_left hx (by positivity :
      0 ≤ (8 : ℝ) ^ (4⁻¹ : ℝ) * (2 + 256 / floor) ^ (4⁻¹ : ℝ) / 63)]
  · change 8 * (K ^ 4 * (_ * E ^ 4 / 63) + _) ≤ _
    apply (mul_le_mul_of_nonneg_left (add_le_add_right hr _) (by norm_num : (0 : ℝ) ≤ 8)).trans
    nlinarith [mul_le_mul_of_nonneg_left hp4 (by positivity :
      0 ≤ 8 * (64 * (HP.K : ℝ) * Rraw ^ 4 / ((HP.K + 1) * floor ^ 4)) / 63)]

/-- A structural charge is fixed after the decoder, floor, capacity and endpoint
constants, before field width, depth, budget or request exponents. On the explicit
bounded family it pays the entire conditional first mean, including semantic loss.
The other mean, centered noises and successful recursive child IH remain separate. -/
theorem initialComputedFirstBudgets_exists_charge
    (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (binCap coefficient floor cap C Cpre : ℝ) (hf : 0 < floor) :
    ∃ A : ℕ, ∀ {P : ℕ} [Fact P.Prime] (B : BudgetData HP P),
      B.binCap = binCap → B.rankCharge = A →
      ∀ (M n ks ka : ℕ), 1 < M → B.bins = range (n + 1) → B.binRate = rate →
      B.slack * (1 + 4 * (n + ka)) < M → M ≤ 32 * B.slack * n →
      2 * ka ≤ n → P ≤ 2 ^ (n + 1) →
      ∀ (H : Horizon P), ks ≤ H.maxExponent →
      ∀ (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)), 1 ≤ r.task.rank →
      r.source.rate = rate ks → r.terminal.rate = rate ka →
      (∀ x y, 0 ≤ B.base x y) → ∀ (R : RoleProfile 3) (ss st : List (ZMod P)),
      initialSeparatedReserve HP C Cpre
        (B.initialComputedFirstPreBudget M n r R ks ka ss st coefficient floor)
        (B.initialComputedFirstFinalBudget M n r R ks ka ss st coefficient)
        (B.initialComputedFirstTailBudget M n r R ks ka ss st coefficient floor)
        (64 * B.initialComputedFirstRawBudget M n r R ks ka ss st coefficient floor
          ((2 * max cap 16) ^ (4⁻¹ : ℝ))) ≤
        ((2 : ℝ) ^ (-B.requestPrecision M r)) ^ 4 := by
  let E := 4 * ∑' h, LogSpaceEstimation.scaleMajorant h
  let L := 2 * ((max (512 * (6 * binCap + 3) ^ 3) (32768 * binCap ^ 3)) ^
    (4⁻¹ : ℝ) * |coefficient| * E + (32 : ℝ) ^ (4⁻¹ : ℝ))
  obtain ⟨A, hA⟩ := initialFirstTransportPayment_exists_charge HP floor cap C Cpre L
  refine ⟨A, ?_⟩
  intro P _ B hcap hcharge M n ks ka hM hbins hrate hlo hhi ha hP H hks r hrank hs ht hC R ss st
  have hcharge0 : 0 ≤ B.rankCharge := by rw [hcharge]; positivity
  obtain ⟨hp, hfinal, htail, hraw⟩ := B.initialComputedFirstBudgets_bounded_family
    hcharge0 M n ks ka hM hbins hrate hlo hhi ha hP H hks r hs ht hC R ss st
    coefficient floor ((2 * max cap 16) ^ (4⁻¹ : ℝ)) hf
  let K := (max (512 * (6 * B.binCap + 3) ^ 3) (32768 * B.binCap ^ 3)) ^
    (4⁻¹ : ℝ) * |coefficient| * (2 : ℝ) ^ (-B.requestPrecision M r) *
      (2 : ℝ) ^ (-B.rankCharge)
  let S := (32 : ℝ) ^ (4⁻¹ : ℝ) * (2 : ℝ) ^ (-B.requestPrecision M r) *
    (2 : ℝ) ^ (-(B.rankCharge * r.task.rank))
  let x := 2 * (K * E + S)
  have hbc := B.binCap_nonneg
  have hsum : 0 ≤ ∑' h, LogSpaceEstimation.scaleMajorant h :=
    tsum_nonneg fun h => LogSpaceEstimation.scaleMajorant_nonneg h
  have hE : 0 ≤ E := mul_nonneg (by norm_num)
    (tsum_nonneg fun h => LogSpaceEstimation.scaleMajorant_nonneg h)
  have hx : 0 ≤ x := by dsimp only [x, K, S]; positivity
  have hsalary : (2 : ℝ) ^ (-(B.rankCharge * r.task.rank)) ≤
      (2 : ℝ) ^ (-B.rankCharge) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hr : (1 : ℝ) ≤ r.task.rank := by exact_mod_cast hrank
    nlinarith
  have hscalar : x ≤ L * (2 : ℝ) ^ (-(A : ℝ)) *
      (2 : ℝ) ^ (-B.requestPrecision M r) := by
    have hh := mul_le_mul_of_nonneg_left hsalary (by positivity :
      0 ≤ (32 : ℝ) ^ (4⁻¹ : ℝ) * (2 : ℝ) ^ (-B.requestPrecision M r))
    dsimp only [x, K, S, L]
    rw [hcap, hcharge] at *
    nlinarith only [hh]
  obtain ⟨hpn, hfn, htn⟩ := B.initialComputedFirstBudgets_nonneg M n ks ka r
    (by rw [hs]; exact (rate_pos ks).le) R ss st coefficient floor hf.le
  have hpaid : initialSeparatedReserve HP C Cpre
      (B.initialComputedFirstPreBudget M n r R ks ka ss st coefficient floor)
      (B.initialComputedFirstFinalBudget M n r R ks ka ss st coefficient)
      (B.initialComputedFirstTailBudget M n r R ks ka ss st coefficient floor)
      (64 * B.initialComputedFirstRawBudget M n r R ks ka ss st coefficient floor
        ((2 * max cap 16) ^ (4⁻¹ : ℝ))) ≤
      initialFirstTransportPayment HP floor cap C Cpre x := by
    unfold initialFirstTransportPayment
    apply initialSeparatedReserve_mono HP C Cpre
    · exact hpn
    · exact hfn
    · exact htn
    · exact hp
    · exact hfinal
    · exact htail
    · convert mul_le_mul_of_nonneg_left hraw (by norm_num : (0 : ℝ) ≤ 64) using 1; ring
  exact hpaid.trans ((initialFirstTransportPayment_mono HP floor cap C Cpre hf.le hx
    hscalar).trans (hA _))

/-- One structural charge pays the complete conditional first-coordinate reserve.
The fixed-depth/bounded-budget/full-bin family needed by semantic first means is retained.
Noise is paid unconditionally, including factor-28 tails. This certificate excludes the
second coordinate and does not construct the endpoint IH or joint recursive availability. -/
theorem initialComputedFirstCoordinateReserve_exists_charge
    (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (binCap coefficient floor cap C Cpre : ℝ) (hf : 0 < floor) :
    ∃ A : ℕ, ∀ {P : ℕ} [Fact P.Prime] (B : BudgetData HP P),
      B.binCap = binCap → B.rankCharge = A → B.binRate = rate →
      B.cutoff = (fun i => boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1)
        rate 1 i (fun _ => 1)) →
      ∀ (M n ks ka : ℕ), 1 < M → B.bins = range (n + 1) →
      B.slack * (1 + 4 * (n + ka)) < M → M ≤ 32 * B.slack * n →
      2 * ka ≤ n → P ≤ 2 ^ (n + 1) →
      ∀ (H : Horizon P), n ≤ H.maxExponent → ks ≤ H.maxExponent →
      ∀ (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (R : RoleProfile 3)
        (ss st : List (ZMod P)),
      r.source = gridChannel R.source ks ss → r.terminal = gridChannel R.terminal ka st →
      r.task = .row 0 (.pilotInput ⟨0, HP.k_pos⟩) → 0 ≤ B.requestPrecision M r →
      (∀ x y, 0 ≤ B.base x y) → B.base *ᵥ 1 ≤ 1 → ∀ (ζ Lh Lρ : ℝ),
      B.initialComputedFirstCoordinateReserve M n r R ks ka ss st coefficient ζ Lh Lρ
        floor cap C Cpre ≤ ((2 : ℝ) ^ (-B.requestPrecision M r)) ^ 4 := by
  let E := 4 * ∑' h, LogSpaceEstimation.scaleMajorant h
  let Lmean := 2 * ((max (512 * (6 * binCap + 3) ^ 3) (32768 * binCap ^ 3)) ^
    (4⁻¹ : ℝ) * |coefficient| * E + (32 : ℝ) ^ (4⁻¹ : ℝ))
  let Lnoise := 2 * (initialNormalizedNoiseConstant binCap coefficient + 256 * binCap)
  let L := |Lmean| + |Lnoise|
  obtain ⟨A, hA⟩ := initialFirstCoordinatePayment_exists_charge HP floor cap C Cpre L
  refine ⟨A, ?_⟩
  intro P _ B hcap hcharge hrate hcutoff M n ks ka hM hbins hlo hhi ha hP H hn hks
    r R ss st hs ht htask hprecision hbase hrow ζ Lh Lρ
  let e := (2 : ℝ) ^ (-B.requestPrecision M r)
  let a := (2 : ℝ) ^ (-B.rankCharge)
  let T := (max (512 * (6 * B.binCap + 3) ^ 3) (32768 * B.binCap ^ 3)) ^
    (4⁻¹ : ℝ) * |coefficient| * e * a
  let S := (32 : ℝ) ^ (4⁻¹ : ℝ) * e * (2 : ℝ) ^ (-(B.rankCharge * r.task.rank))
  let x := 2 * (T * E + S)
  let y := 2 * (initialNormalizedNoiseConstant B.binCap coefficient + 256 * B.binCap) * e * a
  let z := L * (2 : ℝ) ^ (-(A : ℝ)) * e
  let Rraw := (2 * max cap 16) ^ (4⁻¹ : ℝ)
  have hcharge0 : 0 ≤ B.rankCharge := by rw [hcharge]; positivity
  have hcap0 := B.binCap_nonneg
  have hsum : 0 ≤ ∑' h, LogSpaceEstimation.scaleMajorant h :=
    tsum_nonneg LogSpaceEstimation.scaleMajorant_nonneg
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hx : 0 ≤ x := by dsimp only [x, T, S, e, a]; positivity
  have hy : 0 ≤ y := by dsimp only [y, initialNormalizedNoiseConstant, e, a]; positivity
  have hz : 0 ≤ z := by dsimp only [z, L, e]; positivity
  have hrank : (1 : ℝ) ≤ r.task.rank := by
    rw [htask]
    norm_num [HierarchyTask.rank, BoundedRowTask.localTask, CorrectionRowTask.rank,
      PilotRowTask.rank, PilotTask.rank]
  have hsalary : (2 : ℝ) ^ (-(B.rankCharge * r.task.rank)) ≤ a := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith
  have hxm : x ≤ Lmean * a * e := by
    have hh := mul_le_mul_of_nonneg_left hsalary (show 0 ≤ (32 : ℝ) ^ (4⁻¹ : ℝ) * e by
      dsimp only [e]; positivity)
    dsimp only [x, T, S, Lmean]
    rw [hcap]
    nlinarith only [hh]
  have hLmean : Lmean ≤ L := (le_abs_self _).trans (le_add_of_nonneg_right (abs_nonneg _))
  have hLnoise : Lnoise ≤ L := (le_abs_self _).trans (le_add_of_nonneg_left (abs_nonneg _))
  have hxz : x ≤ z := by
    apply hxm.trans
    have hh := mul_le_mul_of_nonneg_right hLmean (show 0 ≤ a * e by
      dsimp only [a, e]; positivity)
    simpa only [z, a, hcharge, mul_assoc] using hh
  have hyz : y ≤ z := by
    have hh := mul_le_mul_of_nonneg_right hLnoise (show 0 ≤ a * e by
      dsimp only [a, e]; positivity)
    simpa only [y, z, Lnoise, a, hcap, hcharge, mul_assoc, mul_comm, mul_left_comm] using hh
  have hsrate : r.source.rate = rate ks := by rw [hs]; rfl
  have htrate : r.terminal.rate = rate ka := by rw [ht]; rfl
  obtain ⟨hm0, hm1, hm2, hm3⟩ := B.initialComputedFirstBudgets_bounded_family
    hcharge0 M n ks ka hM hbins hrate hlo hhi ha hP H hks r hsrate htrate hbase R ss st
    coefficient floor Rraw hf
  obtain ⟨hz0, hz1, hz2, hz3⟩ := B.initialComputedPrecisionMoment_firstNoise_polynomial_schedule
    hcharge0 hrate hcutoff H (fun bin hb => by rw [hbins, mem_range] at hb; omega)
    M n ks ka (by omega) r R ss st hs ht htask (by omega) hprecision hbase hrow
    coefficient ζ Lh Lρ floor Rraw hf
  change _ ≤ (8 : ℝ) ^ (4⁻¹ : ℝ) * x * floor / 511 at hm0
  change _ ≤ (8 : ℝ) ^ (4⁻¹ : ℝ) * x at hm1
  change _ ≤ (8 : ℝ) ^ (4⁻¹ : ℝ) * x * (2 + 256 / floor) ^ (4⁻¹ : ℝ) / 63 at hm2
  change _ ≤ 8 * x ^ 4 * (64 * (HP.K : ℝ) * Rraw ^ 4 / ((HP.K + 1) * floor ^ 4)) / 63 at hm3
  change _ ≤ floor * y / 511 at hz0
  change _ ≤ y / 4 at hz1
  change _ ≤ y * (458752 / 57) at hz2
  change _ ≤ (64 * (HP.K : ℝ) * Rraw ^ 4 / ((HP.K + 1) * floor ^ 4)) * y ^ 4 / 63 at hz3
  obtain ⟨hpn, hfn, htn⟩ := B.initialComputedFirstBudgets_nonneg M n ks ka r
    (by rw [hsrate]; exact (rate_pos ks).le) R ss st coefficient floor hf.le
  have hroot (j : ℕ) : 0 ≤ B.initialComputedPrecisionMoment M n r R ks ka ss st coefficient
      ζ Lh Lρ j true 0 ^ (4⁻¹ : ℝ) := Real.rpow_nonneg
    (B.initialComputedPrecisionMoment_nonneg M n r (by rw [hsrate]; exact (rate_pos ks).le)
      R ks ka ss st coefficient ζ Lh Lρ j true 0) _
  have hpaid : B.initialComputedFirstCoordinateReserve M n r R ks ka ss st coefficient
      ζ Lh Lρ floor cap C Cpre ≤ initialFirstCoordinatePayment HP floor cap C Cpre z := by
    unfold initialComputedFirstCoordinateReserve initialFirstCoordinatePayment
    dsimp only
    apply initialSeparatedReserve_mono HP C Cpre
    · exact add_nonneg hpn (sum_nonneg fun j _ =>
        mul_nonneg (dyadicFloor_nonneg hf.le _ _) (hroot j))
    · exact add_nonneg hfn (hroot _)
    · exact add_nonneg htn (sum_nonneg fun j _ => mul_nonneg (by positivity) (hroot j))
    · apply (add_le_add hm0 hz0).trans
      calc
        _ ≤ (8 : ℝ) ^ (4⁻¹ : ℝ) * z * floor / 511 + floor * z / 511 := by gcongr
        _ = _ := by ring
    · apply (add_le_add hm1 hz1).trans
      have hfinal : y / 4 ≤ z := by linarith
      nlinarith only [mul_le_mul_of_nonneg_left hxz
        (show 0 ≤ (8 : ℝ) ^ (4⁻¹ : ℝ) by positivity), hfinal]
    · apply (add_le_add hm2 hz2).trans
      calc
        _ ≤ (8 : ℝ) ^ (4⁻¹ : ℝ) * z * (2 + 256 / floor) ^ (4⁻¹ : ℝ) / 63 +
            z * (458752 / 57) := by gcongr
        _ = _ := by ring
    · apply (mul_le_mul_of_nonneg_left (add_le_add hm3 hz3) (by norm_num : (0 : ℝ) ≤ 64)).trans
      have hx4 := pow_le_pow_left₀ hx hxz 4
      have hy4 := pow_le_pow_left₀ hy hyz 4
      have hc : 0 ≤ 64 * (HP.K : ℝ) * Rraw ^ 4 / ((HP.K + 1) * floor ^ 4) := by positivity
      dsimp only [Rraw] at hc ⊢
      nlinarith only [mul_le_mul_of_nonneg_left hx4 hc, mul_le_mul_of_nonneg_left hy4 hc]
  exact hpaid.trans (hA e)

/-- The existing computed final first-mean payment consumes the joint semantic schedule.
Transport still pays its own structural charge. This does not certify the complete
reserve: the other three statistics remain. -/
theorem initialComputedFirstFinalBudget_bounded_family (B : BudgetData HP P)
    (hcharge : 0 ≤ B.rankCharge) (M n ks ka : ℕ) (hM : 1 < M)
    (hbins : B.bins = range (n + 1)) (hrate : B.binRate = rate)
    (hlo : B.slack * (1 + 4 * (n + ka)) < M)
    (hhi : M ≤ 32 * B.slack * n) (ha : 2 * ka ≤ n) (hP : P ≤ 2 ^ (n + 1))
    (H : Horizon P) (hks : ks ≤ H.maxExponent)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka)
    (hC : ∀ x y, 0 ≤ B.base x y) (R : RoleProfile 3) (ss st : List (ZMod P))
    (coefficient : ℝ) :
    B.initialComputedFirstFinalBudget M n r R ks ka ss st coefficient ≤
      (8 : ℝ) ^ (4⁻¹ : ℝ) *
        (((max (512 * (6 * B.binCap + 3) ^ 3) (32768 * B.binCap ^ 3)) ^
          (4⁻¹ : ℝ) * |coefficient| * (2 : ℝ) ^ (-B.requestPrecision M r) *
          (2 : ℝ) ^ (-B.rankCharge)) * (4 * ∑' h, LogSpaceEstimation.scaleMajorant h) +
        (32 : ℝ) ^ (4⁻¹ : ℝ) * (2 : ℝ) ^ (-B.requestPrecision M r)) := by
  have hj : 0 < Nat.log2 M := by
    have hp := Nat.lt_pow_succ_log_self (b := 2) (by decide) M
    rw [← Nat.log2_eq_log_two] at hp
    by_contra hz
    have he : Nat.log2 M = 0 := by omega
    rw [he] at hp
    norm_num at hp
    omega
  have hb := B.initialPolynomialLoss_row_bounded_family hcharge M n (Nat.log2 M)
    ks ka hM hj hbins hrate hlo hhi ha hP H hks r hs ht hC R ss st
  have hsalary : (2 : ℝ) ^ (-(B.rankCharge * r.task.rank)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      (neg_nonpos.mpr (mul_nonneg hcharge (Nat.cast_nonneg _)))
  have hb := hb.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity)
      (mul_le_of_le_one_right (by positivity) hsalary) 4) (by norm_num : (0 : ℝ) ≤ 32))
  have hroot := Real.rpow_le_rpow
    (rowNormPow_nonneg (mul_nonneg (Nat.cast_nonneg P) (by rw [hs]; exact (rate_pos ks).le)) _)
    hb (by norm_num : (0 : ℝ) ≤ 4⁻¹)
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 32) (by positivity)] at hroot
  have he : (((2 : ℝ) ^ (-B.requestPrecision M r)) ^ 4) ^ (4⁻¹ : ℝ) =
      (2 : ℝ) ^ (-B.requestPrecision M r) := by
    convert Real.pow_rpow_inv_natCast (by positivity :
      0 ≤ (2 : ℝ) ^ (-B.requestPrecision M r)) (by decide : (4 : ℕ) ≠ 0) using 1
  rw [he] at hroot
  exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hroot) (by positivity)

/-- Final first-mean payment used by the actual reserve. On the bounded budget family
it takes the smaller of the original exact semantic budget and the paid semantic bound.
Outside that family the original unconditional envelope is retained. -/
@[expose] def initialComputedFirstFinalPayment (B : BudgetData HP P) (M n : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (R : RoleProfile 3)
    (ks ka : ℕ) (ss st : List (ZMod P)) (coefficient : ℝ) : ℝ :=
  let old := B.initialComputedFirstFinalBudget M n r R ks ka ss st coefficient
  if 1 < M ∧ B.slack * (1 + 4 * (n + ka)) < M ∧ M ≤ 32 * B.slack * n ∧
      2 * ka ≤ n ∧ P ≤ 2 ^ (n + 1) then
    min old ((8 : ℝ) ^ (4⁻¹ : ℝ) *
      (((max (512 * (6 * B.binCap + 3) ^ 3) (32768 * B.binCap ^ 3)) ^
        (4⁻¹ : ℝ) * |coefficient| * (2 : ℝ) ^ (-B.requestPrecision M r) *
        (2 : ℝ) ^ (-B.rankCharge)) * (4 * ∑' h, LogSpaceEstimation.scaleMajorant h) +
      (32 : ℝ) ^ (4⁻¹ : ℝ) * (2 : ℝ) ^ (-B.requestPrecision M r)))
  else old

/-- The paid final payment preserves the original unconditional guarantee. -/
theorem initialComputedFirstFinalPayment_le (B : BudgetData HP P) (M n : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (R : RoleProfile 3)
    (ks ka : ℕ) (ss st : List (ZMod P)) (coefficient : ℝ) :
    B.initialComputedFirstFinalPayment M n r R ks ka ss st coefficient ≤
      B.initialComputedFirstFinalBudget M n r R ks ka ss st coefficient := by
  unfold initialComputedFirstFinalPayment
  split_ifs
  · exact min_le_left _ _
  · exact le_rfl

/-- Literal computed final statistic with its bounded-family semantic payment. This is
consumed by the existing separated-reserve theorem, not a second estimator interface. -/
theorem initialComputedPrecisionMoment_first_final_payment_le (B : BudgetData HP P)
    (hcharge : 0 ≤ B.rankCharge) (hrate : B.binRate = rate) (H : Horizon P)
    (M n ks ka : ℕ) (ha : ka ≤ H.maxExponent) (hks : ks ≤ H.maxExponent)
    (hbins : B.bins = range (n + 1)) (hn : n ≤ H.maxExponent)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka)
    (htask : r.task = .row 0 (.pilotInput ⟨0, HP.k_pos⟩))
    (hC : ∀ x y, 0 ≤ B.base x y)
    (R : RoleProfile 3) (ss st : List (ZMod P)) (coefficient ζ Lh Lρ : ℝ) :
    B.initialComputedPrecisionMoment M n r R ks ka ss st coefficient ζ Lh Lρ
      (Nat.log2 M) false 0 ^ (4⁻¹ : ℝ) ≤
      B.initialComputedFirstFinalPayment M n r R ks ka ss st coefficient := by
  have hp := B.initialComputedPrecisionMoment_first_final_le hcharge hrate H M n ks ka
    ha (fun bin hb => by rw [hbins, mem_range] at hb; omega) r
    (by rw [hs]; exact (rate_pos ks).le) hs ht htask R ss st coefficient ζ Lh Lρ
  unfold initialComputedFirstFinalPayment
  split_ifs with h
  · exact le_min hp (hp.trans (B.initialComputedFirstFinalBudget_bounded_family hcharge
      M n ks ka h.1 hbins hrate h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2
      H hks r hs ht hC R ss st coefficient))
  · exact hp

/-- Aggregate raw first-mean charge uses the weighted endpoint theorem, with literal
postincrement indexing and no unconditional weighted-moment envelope. -/
theorem initialComputedPrecisionMoment_first_raw_le (B : BudgetData HP P)
    (hcharge : 0 ≤ B.rankCharge) (hrate : B.binRate = rate) (H : Horizon P)
    (M n ks ka : ℕ) (ha : ka ≤ H.maxExponent)
    (hi : ∀ bin ∈ B.bins, bin ≤ H.maxExponent)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka)
    (htask : r.task = .row 0 (.pilotInput ⟨0, HP.k_pos⟩))
    (R : RoleProfile 3) (ss st : List (ZMod P)) (coefficient ζ Lh Lρ : ℝ)
    (floor Rraw : ℝ) (hf : 0 < floor) :
    (∑ j ∈ range (Nat.log2 M + 1), (64 * (HP.K : ℝ) * Rraw ^ 4 /
      ((compatibleCapacity HP.K (Nat.log2 M + 1) j : ℝ) *
        dyadicFloor floor (Nat.log2 M + 1) j ^ 4)) *
      B.initialComputedPrecisionMoment M n r R ks ka ss st coefficient ζ Lh Lρ j false 0) ≤
      B.initialComputedFirstRawBudget M n r R ks ka ss st coefficient floor Rraw := by
  let m := Nat.log2 M + 1
  let K := (max (512 * (6 * B.binCap + 3) ^ 3) (32768 * B.binCap ^ 3)) ^ (4⁻¹ : ℝ) *
    |coefficient| * (2 : ℝ) ^ (-B.requestPrecision M r) * (2 : ℝ) ^ (-B.rankCharge)
  let E := 4 * ∑' h, LogSpaceEstimation.scaleMajorant h
  let D := fun i => rowNormPow 4 P r.source.rate
    (retainedMask R.source (side P ks) B.padding ss)
    (retainedMask R.terminal (side P ka) B.padding st)
    (fun _ x y => min 1 (|B.initialPolynomialLoss M n i r x y| / (rate ka + B.base x y)))
  have hK : 0 ≤ K := by have hc := B.binCap_nonneg; dsimp only [K]; positivity
  let w := fun j => 64 * (HP.K : ℝ) * Rraw ^ 4 /
    ((compatibleCapacity HP.K m j : ℝ) * dyadicFloor floor m j ^ 4)
  have hw (j : ℕ) : 0 ≤ w j := by dsimp only [w]; positivity
  have hg := compatible_growing_mean_raw_le hf HP.K m Rraw
    (fun i => B.initialClippedEndpointWindow M i ka { r with usage := r.terminal })
    (fun i _ => ⟨by unfold initialClippedEndpointWindow
                    exact sum_nonneg fun _ _ => by split_ifs <;> positivity,
      B.initialClippedEndpointWindow_growing M i ka _⟩)
  have hb := B.initialComputedPrecisionMoment_first_weighted_le hcharge hrate H M n ks ka
    ha hi r hs ht htask R ss st coefficient ζ Lh Lρ (range m) w (fun j _ => hw j)
  exact hb.trans (mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left hg (pow_nonneg hK 4)) le_rfl) (by norm_num))

private lemma four_sum_pow_le (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hd : 0 ≤ d) :
    ((a + b) + (c + d)) ^ 4 ≤ 64 * ((a ^ 4 + b ^ 4) + (c ^ 4 + d ^ 4)) := by
  have h := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg
    (f := ![a, b, c, d]) (univ : Finset (Fin 4)) (by norm_num : (1 : ℝ) ≤ 4)
    (fun i _ => by fin_cases i <;> assumption)
  norm_num only [Real.rpow_natCast, Fin.sum_univ_succ, Matrix.cons_val_zero,
    Matrix.cons_val_succ, sum_empty, add_zero, card_univ,
    Fintype.card_fin, Nat.cast_ofNat, show (4 : ℝ) - 1 = 3 by norm_num,
    show (4 : ℝ) ^ (3 : ℝ) = 64 by norm_num] at h
  simpa only [Real.rpow_ofNat, add_assoc] using h

section Polynomial
variable (B : BudgetData HP P) (M : ℕ) (hM : 0 < M) (n : ℕ)
  (hbins : B.bins = range (n + 1)) (hrate : B.binRate = rate)
  (hcutoff : B.cutoff = fun i => boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1)
    rate 1 i (fun _ => 1))
  (haux : B.auxiliary = fun _ => polynomialPrepCutoff4 HP.θ)
  (hD : B.padding ≠ 0) (H : Horizon P) (hn : n ≤ H.maxExponent)
  (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (R : RoleProfile 3)
  (ks ka : ℕ) (ss st : List (ZMod P))
  (hs : r.source = gridChannel R.source ks ss)
  (ht : r.terminal = gridChannel R.terminal ka st)
  (hks : ks ≤ H.maxExponent)
  (hC : ∀ x y, 0 ≤ B.base x y) (hC1 : B.base *ᵥ 1 ≤ 1)

include hM hbins hrate hcutoff haux hD hn hs ht hks hC hC1

/-- Actual computed histories pay absolute error before the nonlinear preparation.
The group costs can be supplied by `completedGroup_initial_compressed_error`, retaining
its bin-count cube and the strict-IH endpoint importance sums. The semantic deficit and
its centered noise are derived, rather than assumed as parent-error premises. -/
theorem initial_compressed_prefix_absolute
    (exponent : HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℕ)
    (ζ floor : ℝ)
    (A C : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ) (ε : ℕ → ℝ)
    (hA : ∀ j < Nat.log2 M + 1,
      B.completedGroup (fun m q => if m < M then B.compressedHistory exponent ζ floor m q
        else none) M (dyadicSlack (Nat.log2 M + 1) j) (.pilotInput ⟨0, HP.k_pos⟩)
        { r with usage := r.terminal } = some (A j))
    (hCrun : ∀ j < Nat.log2 M + 1,
      B.completedGroup (fun m q => if m < M then B.evaluate m q else none)
        M (dyadicSlack (Nat.log2 M + 1) j) (.pilotInput ⟨0, HP.k_pos⟩)
        { r with usage := r.terminal } = some (C j))
    (herr : ∀ j < Nat.log2 M + 1, rowNormPow 4 P r.source.rate
      (fun σ x => r.source.retains (channels B.padding) σ x)
      (fun σ y => r.terminal.retains (channels B.padding) σ y) (A j - C j) ≤ ε j) :
    ∃ groups,
      (List.range (Nat.log2 M + 1)).mapM (fun j =>
        B.completedGroup (fun m q => if m < M then B.compressedHistory exponent ζ floor m q
          else none) M (dyadicSlack (Nat.log2 M + 1) j) (.pilotInput ⟨0, HP.k_pos⟩)
          { r with usage := r.terminal }) = some groups ∧
      let F := fun p σ x y => ((groups.take p).map (fun T => T σ x y)).sum
      ∀ j < Nat.log2 M + 1,
        rowNormPow 4 P (rate ks) (retainedMask R.source (side P ks) B.padding ss)
          (retainedMask R.terminal (side P ka) B.padding st)
          (fun σ x y => F (j + 1) σ x y - B.base x y) ≤
        B.initialTransportMoment M n r R ks ka ss st ε j := by
  have hsr : 0 ≤ r.source.rate := by rw [hs]; exact (rate_pos ks).le
  obtain ⟨groups, reference, hgroups, href, hpref, _⟩ :=
    B.initial_compressed_prefix_error exponent ζ floor M { r with usage := r.terminal }
      hsr A C ε hA hCrun herr
  let F : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ :=
    fun p σ x y => ((groups.take p).map (fun T => T σ x y)).sum
  let G : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ :=
    fun p σ x y => ((reference.take p).map (fun T => T σ x y)).sum
  have hG : B.initialPrefixes M r = some G := by
    unfold initialPrefixes
    rw [href]
    rfl
  refine ⟨groups, hgroups, ?_⟩
  change ∀ j < Nat.log2 M + 1, _
  intro j hj
  dsimp only [initialTransportMoment]
  have hdiff := hpref (j + 1) (by omega)
  simp only [hs, ht, gridChannel, CorrectionRowTask.Channel.retains, channels,
    semanticSide_grid] at hdiff
  have hsemantic := B.initialPrefix_absolute_moment M hM n hbins hrate hcutoff haux hD H hn
    r R ks ka ss st hs ht hks hC hC1 G hG j hj
  dsimp only at hsemantic
  have hadd := rowNormPow_add_le
    (X := retainedMask R.source (side P ks) B.padding ss)
    (Y := retainedMask R.terminal (side P ka) B.padding st)
    (mul_nonneg (Nat.cast_nonneg P) (rate_pos ks).le)
    (fun σ x y => F (j + 1) σ x y - G (j + 1) σ x y)
    (fun σ x y => G (j + 1) σ x y - B.base x y)
  have he : (fun σ x y => F (j + 1) σ x y - G (j + 1) σ x y +
      (G (j + 1) σ x y - B.base x y)) =
      (fun σ x y => F (j + 1) σ x y - B.base x y) := by
    funext σ x y; ring
  rw [he] at hadd
  apply hadd.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 8)
  apply add_le_add _ hsemantic
  convert hdiff using 1; congr 8

/-- The transported conditional-mean discrepancy combines directly with the semantic
history's omitted/inactive deficit. Unlike the absolute preparation input, this deterministic
payment does not charge semantic centered noise. All prefix transport costs remain literal. -/
theorem initial_compressed_mean_moment
    (exponent : HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℕ)
    (ζ floor : ℝ)
    (A C : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ) (ε : ℕ → ℝ)
    (hA : ∀ j < Nat.log2 M + 1,
      B.completedGroup (fun m q => if m < M then B.compressedHistory exponent ζ floor m q
        else none) M (dyadicSlack (Nat.log2 M + 1) j) (.pilotInput ⟨0, HP.k_pos⟩)
        { r with usage := r.terminal } = some (A j))
    (hCrun : ∀ j < Nat.log2 M + 1,
      B.completedGroup (fun m q => if m < M then B.evaluate m q else none)
        M (dyadicSlack (Nat.log2 M + 1) j) (.pilotInput ⟨0, HP.k_pos⟩)
        { r with usage := r.terminal } = some (C j))
    (herr : ∀ j < Nat.log2 M + 1, rowNormPow 4 P r.source.rate
      (fun σ x => r.source.retains (channels B.padding) σ x)
      (fun σ y => r.terminal.retains (channels B.padding) σ y) (A j - C j) ≤ ε j) :
    ∃ groups,
      (List.range (Nat.log2 M + 1)).mapM (fun j =>
        B.completedGroup (fun m q => if m < M then B.compressedHistory exponent ζ floor m q
          else none) M (dyadicSlack (Nat.log2 M + 1) j) (.pilotInput ⟨0, HP.k_pos⟩)
          { r with usage := r.terminal }) = some groups ∧
      let F := fun p σ x y => ((groups.take p).map (fun T => T σ x y)).sum
      let Xs := retainedMask R.source (side P ks) B.padding ss
      let Ya := retainedMask R.terminal (side P ka) B.padding st
      ∀ j < Nat.log2 M + 1,
        rowNormPow 4 P (rate ks) Xs Ya
          (fun _ x y => rowSliceMean Xs Ya (F (j + 1)) x y - B.base x y) ≤
        8 * (((j + 1 : ℕ) : ℝ) ^ 3 * ∑ i ∈ range (j + 1), ε i +
          rowNormPow 4 P (rate ks) Xs Ya (fun _ => B.initialPolynomialLoss M n j r)) := by
  have hsr : 0 ≤ r.source.rate := by rw [hs]; exact (rate_pos ks).le
  obtain ⟨groups, reference, hgroups, href, hpref, _⟩ :=
    B.initial_compressed_prefix_error exponent ζ floor M { r with usage := r.terminal }
      hsr A C ε hA hCrun herr
  let F : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ :=
    fun p σ x y => ((groups.take p).map (fun T => T σ x y)).sum
  let G : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ :=
    fun p σ x y => ((reference.take p).map (fun T => T σ x y)).sum
  have hG : B.initialPrefixes M r = some G := by
    unfold initialPrefixes
    rw [href]
    rfl
  refine ⟨groups, hgroups, ?_⟩
  change ∀ j < Nat.log2 M + 1, _
  intro j hj
  have hdiff := hpref (j + 1) (by omega)
  simp only [hs, ht, gridChannel, CorrectionRowTask.Channel.retains, channels,
    semanticSide_grid] at hdiff
  let Xs := retainedMask R.source (side P ks) B.padding ss
  let Ya := retainedMask R.terminal (side P ka) B.padding st
  have hNu : 0 ≤ (P : ℝ) * rate ks := mul_nonneg (Nat.cast_nonneg P) (rate_pos ks).le
  have hm (x y : ZMod P) : B.base x y - rowSliceMean Xs Ya (G (j + 1)) x y =
      B.initialPolynomialLoss M n j r x y := by
    have h := B.initialPrefix_polynomial_mean M hM n hbins hrate hcutoff haux hD H hn
      r R.source R.terminal R.source_terminal ks ka ss st hs ht hks hC hC1 G hG j hj x y
    change B.base x y - _ = B.initialPolynomialLoss M n j r x y at h
    convert h using 1; congr 8
  have he : (fun (_σ : Environment P 3) x y => rowSliceMean Xs Ya (G (j + 1)) x y - B.base x y) =
      (fun (_σ : Environment P 3) x y => -B.initialPolynomialLoss M n j r x y) := by
    funext σ x y
    linarith [hm x y]
  have hjensen := rowNormPow_sliceMean_fourth_le hNu Xs Ya
    (fun σ x y => F (j + 1) σ x y - G (j + 1) σ x y)
  have hlin : rowSliceMean Xs Ya (fun σ x y => F (j + 1) σ x y - G (j + 1) σ x y) =
      fun x y => rowSliceMean Xs Ya (F (j + 1)) x y -
        rowSliceMean Xs Ya (G (j + 1)) x y := by
    funext x y
    simp only [rowSliceMean, expect_sub_distrib]
  rw [hlin] at hjensen
  have hb := rowNormPow_sub_le_centered (X := Xs) (Y := Ya) hNu
    (fun _ => rowSliceMean Xs Ya (F (j + 1))) (rowSliceMean Xs Ya (G (j + 1))) B.base
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 8)
  apply add_le_add
  · apply hjensen.trans
    convert hdiff using 1; congr 8
  · rw [he]
    simp only [rowNormPow, abs_neg, Xs, Ya, le_refl]

/-- The actual computed prefix pays polynomial preparation and full-rank gate
sensitivity. The usage walk is executed on that very prefix; its centered noise is paid
unconditionally. Neither a free prefix family nor parent accuracy is a premise. -/
theorem initial_compressed_preparation
    (exponent : HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℕ)
    (ζ floor : ℝ)
    (A C : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ) (ε : ℕ → ℝ)
    (hA : ∀ j < Nat.log2 M + 1,
      B.completedGroup (fun m q => if m < M then B.compressedHistory exponent ζ floor m q
        else none) M (dyadicSlack (Nat.log2 M + 1) j) (.pilotInput ⟨0, HP.k_pos⟩)
        { r with usage := r.terminal } = some (A j))
    (hCrun : ∀ j < Nat.log2 M + 1,
      B.completedGroup (fun m q => if m < M then B.evaluate m q else none)
        M (dyadicSlack (Nat.log2 M + 1) j) (.pilotInput ⟨0, HP.k_pos⟩)
        { r with usage := r.terminal } = some (C j))
    (herr : ∀ j < Nat.log2 M + 1, rowNormPow 4 P r.source.rate
      (fun σ x => r.source.retains (channels B.padding) σ x)
      (fun σ y => r.terminal.retains (channels B.padding) σ y) (A j - C j) ≤ ε j)
    (bin ku : ℕ) (husage : ka ≤ ku)
    (hu : r.usage = gridChannel R.terminal ku st)
    {Lh Lρ : ℝ} (hLh : 0 ≤ Lh) (hLρ : 0 ≤ Lρ)
    (hh : ∀ a b, |polynomialPrepCutoff4 HP.θ a - polynomialPrepCutoff4 HP.θ b| ≤ Lh * |a - b|)
    (hρ : ∀ a b, |HP.ρ a - HP.ρ b| ≤ Lρ * |a - b|) :
    ∃ groups,
      (List.range (Nat.log2 M + 1)).mapM (fun j =>
        B.completedGroup (fun m q => if m < M then B.compressedHistory exponent ζ floor m q
          else none) M (dyadicSlack (Nat.log2 M + 1) j) (.pilotInput ⟨0, HP.k_pos⟩)
          { r with usage := r.terminal }) = some groups ∧
      let F := fun p σ x y => ((groups.take p).map (fun T => T σ x y)).sum
      ∀ j < Nat.log2 M + 1,
        rowNormPow 4 P (rate ks) (retainedMask R.source (side P ks) B.padding ss)
          (retainedMask R.terminal (side P ku) B.padding st)
          (fun _ => secondMeanEnvelope R B.padding ss st ks ka ku Lh Lρ ζ
            (F (j + 1)) B.base) ≤
          P * (|ζ| * (Lh + Lρ) / rate ka) ^ 4 *
            B.initialTransportMoment M n r R ks ka ss st ε j ∧
        ∀ (W : List (Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)),
          (List.range (Nat.log2 M + 1)).mapM (fun i =>
            B.complete M r (B.binPreparation bin r (F (i + 1)))
              (dyadicSlack (Nat.log2 M + 1) i)) = some W →
          (∀ x y, actualClippedMean HP R.source R.terminal (side P ks) (side P ka)
            (side P ku) B.padding ss st ka B.base ζ
            (firstSignalIncrement F ka
              (secondSignalIncrement (fun i σ x y => W[i - 1]?.getD 0 σ x y) ζ))
            0 1 j x y ≤
            secondMeanEnvelope R B.padding ss st ks ka ku Lh Lρ ζ (F (j + 1)) B.base x y) ∧
          rowNormPow 4 P r.source.rate (retainedMask R.source (side P ks) B.padding ss)
            (retainedMask R.terminal (side P ku) B.padding st)
            (actualNoiseEntry R.source R.terminal (side P ks) (side P ka) (side P ku)
              B.padding ss st ka B.base (firstSignalIncrement F ka
                (secondSignalIncrement (fun i σ x y => W[i - 1]?.getD 0 σ x y) ζ))
              0 1 j) ≤
            (|ζ| * (2 : ℝ) ^ (-B.requestPrecision M r) *
              (1 / 64 : ℝ) ^ dyadicSlack (Nat.log2 M + 1) j) ^ 4 := by
  obtain ⟨groups, hgroups, habs⟩ := B.initial_compressed_prefix_absolute M hM n hbins hrate
    hcutoff haux hD H hn r R ks ka ss st hs ht hks hC hC1 exponent ζ floor A C ε hA hCrun herr
  refine ⟨groups, hgroups, ?_⟩
  dsimp only
  intro j hj
  refine ⟨(secondMeanEnvelope_moment R B.padding ss st ks ka ku husage hLh hLρ ζ
    _ B.base (mul_nonneg (Nat.cast_nonneg P) (rate_pos ks).le)).trans
      (mul_le_mul_of_nonneg_left (habs j hj) (by positivity)), ?_⟩
  intro W hW
  constructor
  · exact B.initialSecondSignal_clippedMean_le M bin ka ku r R ks ss st hs ht hu
      (congrFun haux bin) _ W hW hLρ hh hρ ζ j hj
  · exact B.initialSecondSignal_noise_moment M bin
      (fun d => by rw [haux]; exact ⟨polynomialPrepCutoff4_nonneg _ _,
        polynomialPrepCutoff4_le_one _ _⟩) r R ks ku ss st hs hu _ W hW ka B.base ζ j hj

/-- All four actual row moments paid on their respective rank and usage masks.
The only supplied error bounds are executed group perturbations, obtainable from strict
own-request rooted precision via `completedGroup_initial_compressed_precision`. -/
theorem initial_compressed_four_moments
    (exponent : HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℕ)
    (ζ floor : ℝ)
    (A C : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ) (ε : ℕ → ℝ)
    (hA : ∀ j < Nat.log2 M + 1,
      B.completedGroup (fun m q => if m < M then B.compressedHistory exponent ζ floor m q
        else none) M (dyadicSlack (Nat.log2 M + 1) j) (.pilotInput ⟨0, HP.k_pos⟩)
        { r with usage := r.terminal } = some (A j))
    (hCrun : ∀ j < Nat.log2 M + 1,
      B.completedGroup (fun m q => if m < M then B.evaluate m q else none)
        M (dyadicSlack (Nat.log2 M + 1) j) (.pilotInput ⟨0, HP.k_pos⟩)
        { r with usage := r.terminal } = some (C j))
    (herr : ∀ j < Nat.log2 M + 1, rowNormPow 4 P r.source.rate
      (fun σ x => r.source.retains (channels B.padding) σ x)
      (fun σ y => r.terminal.retains (channels B.padding) σ y) (A j - C j) ≤ ε j)
    (bin ku : ℕ) (husage : ka ≤ ku)
    (hu : r.usage = gridChannel R.terminal ku st)
    {Lh Lρ : ℝ} (hLh : 0 ≤ Lh) (hLρ : 0 ≤ Lρ)
    (hh : ∀ a b, |polynomialPrepCutoff4 HP.θ a - polynomialPrepCutoff4 HP.θ b| ≤ Lh * |a - b|)
    (hρ : ∀ a b, |HP.ρ a - HP.ρ b| ≤ Lρ * |a - b|) :
    ∃ groups,
      (List.range (Nat.log2 M + 1)).mapM (fun j =>
        B.completedGroup (fun m q => if m < M then B.compressedHistory exponent ζ floor m q
          else none) M (dyadicSlack (Nat.log2 M + 1) j) (.pilotInput ⟨0, HP.k_pos⟩)
          { r with usage := r.terminal }) = some groups ∧
      let F := fun p σ x y => ((groups.take p).map (fun T => T σ x y)).sum
      ∀ W,
        (List.range (Nat.log2 M + 1)).mapM (fun i =>
          B.complete M r (B.binPreparation bin r (F (i + 1)))
            (dyadicSlack (Nat.log2 M + 1) i)) = some W →
        let Δ := firstSignalIncrement F ka
          (secondSignalIncrement (fun i σ x y => W[i - 1]?.getD 0 σ x y) ζ)
        ∀ j < Nat.log2 M + 1, ∀ (ν : Fin 2),
          rowNormPow 4 P r.source.rate (retainedMask R.source (side P ks) B.padding ss)
            (retainedMask R.terminal (if ν = 0 then side P ka else side P ku) B.padding st)
            (fun _ x y => actualClippedMean HP R.source R.terminal (side P ks) (side P ka)
              (side P ku) B.padding ss st ka B.base ζ Δ 0 ν j x y) ≤
            B.initialComputedRelativeMoment M n r R ks ka ss st ε ζ Lh Lρ j false ν ∧
          rowNormPow 4 P r.source.rate (retainedMask R.source (side P ks) B.padding ss)
            (retainedMask R.terminal (if ν = 0 then side P ka else side P ku) B.padding st)
            (actualNoiseEntry R.source R.terminal (side P ks) (side P ka) (side P ku)
              B.padding ss st ka B.base Δ 0 ν j) ≤
            B.initialComputedRelativeMoment M n r R ks ka ss st ε ζ Lh Lρ j true ν := by
  obtain ⟨groups, hgroups, hprep⟩ := B.initial_compressed_preparation M hM n hbins hrate
    hcutoff haux hD H hn r R ks ka ss st hs ht hks hC hC1 exponent ζ floor A C ε hA hCrun herr
    bin ku husage hu hLh hLρ hh hρ
  obtain ⟨gmean, hgmean, hmean⟩ := B.initial_compressed_mean_moment M hM n hbins hrate
    hcutoff haux hD H hn r R ks ka ss st hs ht hks hC hC1 exponent ζ floor A C ε hA hCrun herr
  have he := Option.some.inj (hgmean.symm.trans hgroups)
  subst gmean
  have hnonempty : B.bins.Nonempty := by rw [hbins]; exact ⟨0, mem_range.mpr (by omega)⟩
  obtain ⟨gnoise, hgnoise, hnoise⟩ := B.initial_compressed_first_noise M hM hnonempty
    exponent ζ floor r R ks ka ss st hs ht A C ε hA hCrun herr
  have he := Option.some.inj (hgnoise.symm.trans hgroups)
  subst gnoise
  refine ⟨groups, hgroups, ?_⟩
  dsimp only
  intro W hW j hj ν
  have hNu : 0 ≤ (P : ℝ) * r.source.rate := by
    rw [hs]; exact mul_nonneg (Nat.cast_nonneg _) (rate_pos ks).le
  fin_cases ν <;> simp only [Fin.zero_eta, Fin.mk_one]
  · constructor
    · have hb := actualClippedMean_first_prefix_row_le HP R.source R.terminal
        (side P ks) (side P ka) (side P ku) B.padding ss st
        (fun p σ x y => ((groups.take p).map (fun T => T σ x y)).sum) ka B.base hC ζ
        (secondSignalIncrement (fun i σ x y => W[i - 1]?.getD 0 σ x y) ζ) j hNu
      apply hb.trans
      simp only [initialComputedRelativeMoment, initialComputedMoment, Bool.false_eq_true,
        ↓reduceIte, Fin.isValue]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      convert hmean j hj using 1
      congr 8
      exact congrArg (fun c => c.rate) hs
    · have hz := hnoise j hj B.base hC (side P ku)
        (secondSignalIncrement (fun i σ x y => W[i - 1]?.getD 0 σ x y) ζ)
      simpa only [initialComputedRelativeMoment, initialComputedMoment, ↓reduceIte,
        Fin.isValue, and_self] using le_min hz.1 hz.2
  · obtain ⟨hp, hz⟩ := (hprep j hj).2 W hW
    constructor
    · have hb : rowNormPow 4 P r.source.rate
          (retainedMask R.source (side P ks) B.padding ss)
          (retainedMask R.terminal (side P ku) B.padding st)
          (fun _ x y => actualClippedMean HP R.source R.terminal (side P ks) (side P ka)
            (side P ku) B.padding ss st ka B.base ζ
            (firstSignalIncrement (fun p σ x y => ((groups.take p).map
              (fun T => T σ x y)).sum) ka
              (secondSignalIncrement (fun i σ x y => W[i - 1]?.getD 0 σ x y) ζ)) 0 1 j x y) ≤
          rowNormPow 4 P r.source.rate
            (retainedMask R.source (side P ks) B.padding ss)
            (retainedMask R.terminal (side P ku) B.padding st)
            (fun _ => secondMeanEnvelope R B.padding ss st ks ka ku Lh Lρ ζ
              (fun σ x y => ((groups.take (j + 1)).map (fun T => T σ x y)).sum) B.base) := by
        apply (rowNormPow_le_mul hNu (c := 1) ?_).trans_eq (one_mul _)
        intro σ x y _ _
        have hnon : 0 ≤ actualClippedMean HP R.source R.terminal
            (side P ks) (side P ka) (side P ku) B.padding ss st ka B.base ζ
            (firstSignalIncrement (fun p σ x y => ((groups.take p).map
              (fun T => T σ x y)).sum) ka
              (secondSignalIncrement (fun i σ x y => W[i - 1]?.getD 0 σ x y) ζ)) 0 1 j x y := by
          simp only [actualClippedMean, Fin.isValue, one_ne_zero, ↓reduceIte]
          positivity
        rw [one_mul, abs_of_nonneg hnon]
        exact pow_le_pow_left₀ (by positivity) ((hp x y).trans (le_abs_self _)) 4
      apply hb.trans
      simpa only [initialComputedRelativeMoment, initialComputedMoment, Bool.false_eq_true,
        Fin.isValue, one_ne_zero, and_false, ↓reduceIte, hs, gridChannel] using (hprep j hj).1
    · simpa only [initialComputedRelativeMoment, initialComputedMoment, Fin.isValue,
        one_ne_zero, and_false, ↓reduceIte] using hz

/-- The literal computed first clipped coordinate from own-request scalar rooted IH.
Positive means are compared before signed pairing, then stationary completed group means
and correlated prefixes are summed. Rounded masses, endpoint guards and precision remain
explicit. Ordinary progress and the saturated second coordinate are separate payments. -/
theorem initial_compressed_precision_clipped_first
    (exponent : HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℕ)
    (ζ floor : ℝ)
    (D : ℕ → ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hzero : ∀ bin, D bin 0 = 0) (coefficient : ℝ)
    (ih : ∀ bin ∈ B.bins, ∀ m < M, 0 < m →
      let q := { r with usage := r.terminal }
      let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
        q.source (midpoint q) q.terminal (B.binRate bin)
      B.compressedBin m bin (exponent Q.direct) ζ floor Q.direct = some (D bin m) ∧
      rootDistPow 4 P Q.direct.source.rate
        (fun σ x => Q.direct.source.retains (channels B.padding) σ x)
        (fun σ y => Q.direct.usage.retains (channels B.padding) σ y) (D bin m)
        (denseChild B.padding id Q.direct (B.cutoff bin) (B.auxiliary bin)
          HP.ρ HP.K B.base) ≤
        coefficient ^ 4 * ((2 : ℝ) ^ (-B.requestPrecision m Q.direct)) ^ 4 ∧
      ∃ R, B.compressedBin m bin (exponent Q.right) ζ floor Q.right = some R)
    (Lt : ℕ)
    (second : Environment P 3 → ZMod P → ℕ → ZMod P → ℝ) :
    ∃ groups,
      (List.range (Nat.log2 M + 1)).mapM (fun j =>
        B.completedGroup (fun m q => if m < M then B.compressedHistory exponent ζ floor m q
          else none) M (dyadicSlack (Nat.log2 M + 1) j) (.pilotInput ⟨0, HP.k_pos⟩)
          { r with usage := r.terminal }) = some groups ∧
      let F := fun p σ x y => ((groups.take p).map (fun T => T σ x y)).sum
      let Xs := retainedMask R.source (side P ks) B.padding ss
      let Ya := retainedMask R.terminal (side P ka) B.padding st
      ∀ j < Nat.log2 M + 1,
        rowNormPow 4 P r.source.rate Xs Ya
          (fun _ x y => actualClippedMean HP R.source R.terminal (side P ks) (side P ka)
            Lt B.padding ss st ka B.base ζ (firstSignalIncrement F ka second) 0 0 j x y) ≤
        8 * (((∑ i ∈ range (j + 1),
          (B.initialClippedRootGroupCharge M (dyadicSlack (Nat.log2 M + 1) i)
            { r with usage := r.terminal } ka coefficient) ^ (4⁻¹ : ℝ)) ^ 4) +
          rowNormPow 4 P r.source.rate Xs Ya (fun _ x y =>
            min 1 (|B.initialPolynomialLoss M n j r x y| / (rate ka + B.base x y)))) := by
  have hne : B.bins.Nonempty := by rw [hbins]; exact ⟨0, mem_range.mpr (by omega)⟩
  have hsr : 0 ≤ r.source.rate := by rw [hs]; exact (rate_pos ks).le
  have hk : 2 * (1 + 32 / HP.η) ≤ HP.K := by
    have hk1 : (1 : ℝ) ≤ HP.k := by exact_mod_cast HP.k_pos
    have hdiv := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hk1 (by norm_num : (0 : ℝ) ≤ 32)) HP.η_pos.le
    have hg := HP.gate
    norm_num only [mul_one] at hdiv
    nlinarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 32) HP.η_pos.le]
  have hprep (bin : ℕ) (v : ℝ) (hv : B.cutoff bin v ≠ 0) : B.auxiliary bin v = 1 := by
    rw [hcutoff] at hv
    rw [haux]
    exact HP.routedBin_prep_eq_one (by norm_num)
      (fun w hw => polynomialSwitch4_of_le (by norm_num) hw) rate_pos rate_antitone
      bin (fun _ => 1) hv
  let q := { r with usage := r.terminal }
  have hp (j : ℕ) (i : {i // i ∈ B.bins}) :=
    B.pairedSample_initial_compressed_clipped_precision hrate hcutoff hD H exponent ζ floor
      M (dyadicSlack (Nat.log2 M + 1) j) i.val hM q R.source R.terminal R.source_terminal
      ks ka ss st hs ht hks
      (by have hi : i.val ∈ range (n + 1) := by simpa only [hbins] using i.property
          have hb := mem_range.mp hi; omega)
      (hprep i.val) hC hC1 hk (D i.val) (hzero i.val) coefficient (ih i.val i.property)
  choose A C hA hCrun herr using hp
  let a := fun j i => if hi : i ∈ B.bins then A j ⟨i, hi⟩ else 0
  let c := fun j i => if hi : i ∈ B.bins then C j ⟨i, hi⟩ else 0
  let ε := fun j bin =>
    let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
      q.source (midpoint q) q.terminal (B.binRate bin)
    let fine := LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j)
      B.slack (B.sampleScale q (some bin))
    let coarse := LogSpaceEstimation.lastBudget M (2 * dyadicSlack (Nat.log2 M + 1) j)
      B.slack (B.sampleScale q (some bin))
    if fine = coarse then 0 else
    8 * (B.initialClippedRootCoefficient ka bin) *
      (B.initialEndpointCharge fine Q.direct coefficient +
        B.initialEndpointCharge coarse Q.direct coefficient)
  have hg (j : ℕ) := B.completedGroup_initial_compressed_clipped_mean exponent ζ floor M
    (dyadicSlack (Nat.log2 M + 1) j) hne q R.source R.terminal R.source_terminal
    ks ka ss st hs ht (a j) (c j) (ε j)
    (fun i hi => by simpa only [a, dite_eq_left hi] using hA j ⟨i, hi⟩)
    (fun i hi => by simpa only [c, dite_eq_left hi] using hCrun j ⟨i, hi⟩)
    (fun x y => rate ka + B.base x y)
    (fun x y => add_pos_of_pos_of_nonneg (rate_pos ka) (hC x y))
    (fun i hi => by simpa only [a, c, dite_eq_left hi] using herr j ⟨i, hi⟩)
  choose F G hF hG he using hg
  have hem (j : ℕ) : rowNormPow 4 P r.source.rate
      (fun σ x => q.source.retains (channels B.padding) σ x)
      (fun σ y => q.usage.retains (channels B.padding) σ y)
      (fun _ x y => min 1 (|rowSliceMean
        (fun σ x => q.source.retains (channels B.padding) σ x)
        (fun σ y => q.usage.retains (channels B.padding) σ y) (F j - G j) x y| /
        (rate ka + B.base x y))) ≤
      B.initialClippedRootGroupCharge M (dyadicSlack (Nat.log2 M + 1) j) q ka coefficient := by
    convert he j using 1 <;>
      simp only [q, hs, ht, gridChannel, CorrectionRowTask.Channel.retains, channels,
        semanticSide_grid, X, Y, rowNormPow, rowSliceMean,
        initialClippedRootGroupCharge, ε]
  obtain ⟨groups, reference, hgroups, href, hprefix⟩ :=
    B.initial_compressed_prefix_clipped_mean exponent ζ floor M q hsr F G
      (fun j => B.initialClippedRootGroupCharge M (dyadicSlack (Nat.log2 M + 1) j)
        q ka coefficient) (fun j _ => hF j) (fun j _ => hG j)
      (fun x y => rate ka + B.base x y)
      (fun x y => add_pos_of_pos_of_nonneg (rate_pos ka) (hC x y)) (fun j _ => hem j)
  let f : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ :=
    fun p σ x y => ((groups.take p).map (fun T => T σ x y)).sum
  let g : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ :=
    fun p σ x y => ((reference.take p).map (fun T => T σ x y)).sum
  have hgrun : B.initialPrefixes M r = some g := by
    unfold initialPrefixes
    rw [href]
    rfl
  refine ⟨groups, hgroups, ?_⟩
  dsimp only
  intro j hj
  let Xs := retainedMask R.source (side P ks) B.padding ss
  let Ya := retainedMask R.terminal (side P ka) B.padding st
  have hNu : 0 ≤ (P : ℝ) * r.source.rate := mul_nonneg (Nat.cast_nonneg _) hsr
  have hm (x y : ZMod P) : B.base x y - rowSliceMean Xs Ya (g (j + 1)) x y =
      B.initialPolynomialLoss M n j r x y := by
    have h := B.initialPrefix_polynomial_mean M hM n hbins hrate hcutoff haux hD H hn
      r R.source R.terminal R.source_terminal ks ka ss st hs ht hks hC hC1 g hgrun j hj x y
    change B.base x y - _ = B.initialPolynomialLoss M n j r x y at h
    exact h
  simp_rw [actualClippedMean_first_prefix_eq]
  have hmean (x y : ZMod P) : rowSliceMean Xs Ya (f (j + 1)) x y - B.base x y =
      rowSliceMean Xs Ya (f (j + 1) - g (j + 1)) x y +
        -B.initialPolynomialLoss M n j r x y := by
    simp only [rowSliceMean, Pi.sub_apply, Matrix.sub_apply, expect_sub_distrib]
    have h := hm x y
    unfold rowSliceMean at h
    linarith
  change rowNormPow 4 P r.source.rate Xs Ya
    (fun _ x y => min 1 (|rowSliceMean Xs Ya (f (j + 1)) x y - B.base x y| /
      (rate ka + B.base x y))) ≤ _
  simp_rw [hmean]
  apply (rowNormPow_clipped_add_le hNu Xs Ya
    (rowSliceMean Xs Ya (f (j + 1) - g (j + 1)))
    (fun x y => -B.initialPolynomialLoss M n j r x y)
    (fun x y => rate ka + B.base x y)
    (fun x y => add_pos_of_pos_of_nonneg (rate_pos ka) (hC x y))).trans
  simp only [abs_neg]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 8)
  apply add_le_add _ le_rfl
  have hp := hprefix (j + 1) (by omega)
  convert hp using 1;
    simp only [q, hs, ht, gridChannel, CorrectionRowTask.Channel.retains, channels,
      semanticSide_grid, retainedMask, Xs, Ya, f, g, rowNormPow, rowSliceMean,
      Pi.sub_apply]

/-- The literal computed first clipped coordinate from own-request scalar rooted IH.
The signed stationary prefix telescopes before absolute values, clipping and root bounds.
Only the surviving fine endpoints are paid. Rounded masses, endpoint guards and precision remain
explicit. Ordinary progress and the saturated second coordinate are separate payments. -/
theorem initial_compressed_precision_clipped_endpoint_first
    (exponent : HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℕ)
    (ζ floor : ℝ)
    (D : ℕ → ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hzero : ∀ bin, D bin 0 = 0) (coefficient : ℝ)
    (ih : ∀ bin ∈ B.bins, ∀ m < M, 0 < m →
      let q := { r with usage := r.terminal }
      let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
        q.source (midpoint q) q.terminal (B.binRate bin)
      B.compressedBin m bin (exponent Q.direct) ζ floor Q.direct = some (D bin m) ∧
      rootDistPow 4 P Q.direct.source.rate
        (fun σ x => Q.direct.source.retains (channels B.padding) σ x)
        (fun σ y => Q.direct.usage.retains (channels B.padding) σ y) (D bin m)
        (denseChild B.padding id Q.direct (B.cutoff bin) (B.auxiliary bin)
          HP.ρ HP.K B.base) ≤
        coefficient ^ 4 * ((2 : ℝ) ^ (-B.requestPrecision m Q.direct)) ^ 4 ∧
      ∃ R, B.compressedBin m bin (exponent Q.right) ζ floor Q.right = some R)
    (Lt : ℕ)
    (second : Environment P 3 → ZMod P → ℕ → ZMod P → ℝ) :
    ∃ groups,
      (List.range (Nat.log2 M + 1)).mapM (fun j =>
        B.completedGroup (fun m q => if m < M then B.compressedHistory exponent ζ floor m q
          else none) M (dyadicSlack (Nat.log2 M + 1) j) (.pilotInput ⟨0, HP.k_pos⟩)
          { r with usage := r.terminal }) = some groups ∧
      let F := fun p σ x y => ((groups.take p).map (fun T => T σ x y)).sum
      let Xs := retainedMask R.source (side P ks) B.padding ss
      let Ya := retainedMask R.terminal (side P ka) B.padding st
      ∀ j < Nat.log2 M + 1,
        rowNormPow 4 P r.source.rate Xs Ya
          (fun _ x y => actualClippedMean HP R.source R.terminal (side P ks) (side P ka)
            Lt B.padding ss st ka B.base ζ (firstSignalIncrement F ka second) 0 0 j x y) ≤
        8 * (B.initialClippedEndpointPrefixCharge M j { r with usage := r.terminal } ka
          coefficient +
          rowNormPow 4 P r.source.rate Xs Ya (fun _ x y =>
            min 1 (|B.initialPolynomialLoss M n j r x y| / (rate ka + B.base x y)))) := by
  have hne : B.bins.Nonempty := by rw [hbins]; exact ⟨0, mem_range.mpr (by omega)⟩
  have hsr : 0 ≤ r.source.rate := by rw [hs]; exact (rate_pos ks).le
  have hk : 2 * (1 + 32 / HP.η) ≤ HP.K := by
    have hk1 : (1 : ℝ) ≤ HP.k := by exact_mod_cast HP.k_pos
    have hdiv := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hk1 (by norm_num : (0 : ℝ) ≤ 32)) HP.η_pos.le
    have hg := HP.gate
    norm_num only [mul_one] at hdiv
    nlinarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 32) HP.η_pos.le]
  have hprep (bin : ℕ) (v : ℝ) (hv : B.cutoff bin v ≠ 0) : B.auxiliary bin v = 1 := by
    rw [hcutoff] at hv
    rw [haux]
    exact HP.routedBin_prep_eq_one (by norm_num)
      (fun w hw => polynomialSwitch4_of_le (by norm_num) hw) rate_pos rate_antitone
      bin (fun _ => 1) hv
  let q := { r with usage := r.terminal }
  obtain ⟨groups, reference, hgroups, href, hprefix⟩ :=
    B.initial_compressed_prefix_clipped_endpoint hrate hcutoff hD H exponent ζ floor M hM
      hne q R.source R.terminal R.source_terminal ks ka ss st hs ht rfl hks
      (fun bin hb => by
        have hi : bin ∈ range (n + 1) := by simpa only [hbins] using hb
        have hb' := mem_range.mp hi
        omega)
      (fun bin _ => hprep bin) hC hC1 hk D hzero coefficient ih
  let f : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ :=
    fun p σ x y => ((groups.take p).map (fun T => T σ x y)).sum
  let g : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ :=
    fun p σ x y => ((reference.take p).map (fun T => T σ x y)).sum
  have hgrun : B.initialPrefixes M r = some g := by
    unfold initialPrefixes
    rw [href]
    rfl
  refine ⟨groups, hgroups, ?_⟩
  dsimp only
  intro j hj
  let Xs := retainedMask R.source (side P ks) B.padding ss
  let Ya := retainedMask R.terminal (side P ka) B.padding st
  have hNu : 0 ≤ (P : ℝ) * r.source.rate := mul_nonneg (Nat.cast_nonneg _) hsr
  have hm (x y : ZMod P) : B.base x y - rowSliceMean Xs Ya (g (j + 1)) x y =
      B.initialPolynomialLoss M n j r x y := by
    have h := B.initialPrefix_polynomial_mean M hM n hbins hrate hcutoff haux hD H hn
      r R.source R.terminal R.source_terminal ks ka ss st hs ht hks hC hC1 g hgrun j hj x y
    change B.base x y - _ = B.initialPolynomialLoss M n j r x y at h
    exact h
  simp_rw [actualClippedMean_first_prefix_eq]
  have hmean (x y : ZMod P) : rowSliceMean Xs Ya (f (j + 1)) x y - B.base x y =
      rowSliceMean Xs Ya (f (j + 1) - g (j + 1)) x y +
        -B.initialPolynomialLoss M n j r x y := by
    simp only [rowSliceMean, Pi.sub_apply, Matrix.sub_apply, expect_sub_distrib]
    have h := hm x y
    unfold rowSliceMean at h
    linarith
  change rowNormPow 4 P r.source.rate Xs Ya
    (fun _ x y => min 1 (|rowSliceMean Xs Ya (f (j + 1)) x y - B.base x y| /
      (rate ka + B.base x y))) ≤ _
  simp_rw [hmean]
  apply (rowNormPow_clipped_add_le hNu Xs Ya
    (rowSliceMean Xs Ya (f (j + 1) - g (j + 1)))
    (fun x y => -B.initialPolynomialLoss M n j r x y)
    (fun x y => rate ka + B.base x y)
    (fun x y => add_pos_of_pos_of_nonneg (rate_pos ka) (hC x y))).trans
  simp only [abs_neg]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 8)
  apply add_le_add _ le_rfl
  have hp := hprefix j hj
  convert hp using 1; rfl

/-- Literal all-four payment from strict lower-budget own-request rooted precision.
No parent accuracy or four-max budgets are premises. The child hypothesis is conditional:
this does not prove simultaneous recursive availability. The first-noise minimum consumes
actual centered spectral group discrepancies; uniform absorption has an explicit family. -/
theorem initial_compressed_precision_moments
    (exponent : HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℕ)
    (ζ floor : ℝ)
    (D : ℕ → ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hzero : ∀ bin, D bin 0 = 0) (coefficient : ℝ)
    (ih : ∀ bin ∈ B.bins, ∀ m < M, 0 < m →
      let q := { r with usage := r.terminal }
      let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
        q.source (midpoint q) q.terminal (B.binRate bin)
      B.compressedBin m bin (exponent Q.direct) ζ floor Q.direct = some (D bin m) ∧
      rootDistPow 4 P Q.direct.source.rate
        (fun σ x => Q.direct.source.retains (channels B.padding) σ x)
        (fun σ y => Q.direct.usage.retains (channels B.padding) σ y) (D bin m)
        (denseChild B.padding id Q.direct (B.cutoff bin) (B.auxiliary bin)
          HP.ρ HP.K B.base) ≤
        coefficient ^ 4 * ((2 : ℝ) ^ (-B.requestPrecision m Q.direct)) ^ 4 ∧
      ∃ R, B.compressedBin m bin (exponent Q.right) ζ floor Q.right = some R)
    (bin ku : ℕ) (husage : ka ≤ ku)
    (hu : r.usage = gridChannel R.terminal ku st)
    {Lh Lρ : ℝ} (hLh : 0 ≤ Lh) (hLρ : 0 ≤ Lρ)
    (hh : ∀ a b, |polynomialPrepCutoff4 HP.θ a - polynomialPrepCutoff4 HP.θ b| ≤ Lh * |a - b|)
    (hρ : ∀ a b, |HP.ρ a - HP.ρ b| ≤ Lρ * |a - b|) :
    ∃ groups,
      (List.range (Nat.log2 M + 1)).mapM (fun j =>
        B.completedGroup (fun m q => if m < M then B.compressedHistory exponent ζ floor m q
          else none) M (dyadicSlack (Nat.log2 M + 1) j) (.pilotInput ⟨0, HP.k_pos⟩)
          { r with usage := r.terminal }) = some groups ∧
      let F := fun p σ x y => ((groups.take p).map (fun T => T σ x y)).sum
      ∀ W,
        (List.range (Nat.log2 M + 1)).mapM (fun i =>
          B.complete M r (B.binPreparation bin r (F (i + 1)))
            (dyadicSlack (Nat.log2 M + 1) i)) = some W →
        let Δ := firstSignalIncrement F ka
          (secondSignalIncrement (fun i σ x y => W[i - 1]?.getD 0 σ x y) ζ)
        ∀ j < Nat.log2 M + 1, ∀ (ν : Fin 2),
          rowNormPow 4 P r.source.rate (retainedMask R.source (side P ks) B.padding ss)
            (retainedMask R.terminal (if ν = 0 then side P ka else side P ku) B.padding st)
            (fun _ x y => actualClippedMean HP R.source R.terminal (side P ks) (side P ka)
              (side P ku) B.padding ss st ka B.base ζ Δ 0 ν j x y) ≤
            B.initialComputedPrecisionMoment M n r R ks ka ss st coefficient ζ Lh Lρ j false ν ∧
          rowNormPow 4 P r.source.rate (retainedMask R.source (side P ks) B.padding ss)
            (retainedMask R.terminal (if ν = 0 then side P ka else side P ku) B.padding st)
            (actualNoiseEntry R.source R.terminal (side P ks) (side P ka) (side P ku)
              B.padding ss st ka B.base Δ 0 ν j) ≤
            B.initialComputedPrecisionMoment M n r R ks ka ss st coefficient ζ Lh Lρ j true ν := by
  have hnonempty : B.bins.Nonempty := by rw [hbins]; exact ⟨0, mem_range.mpr (by omega)⟩
  have hg (j : ℕ) := B.completedGroup_initial_compressed_precision exponent ζ floor M
    (dyadicSlack (Nat.log2 M + 1) j) hM hnonempty { r with usage := r.terminal }
    R.source R.terminal R.source_terminal ks ka ss st hs ht D hzero coefficient ih
  choose A C hA hCrun herr using hg
  have hc (j : ℕ) := B.completedGroup_initial_compressed_centered_precision
    exponent ζ floor M (dyadicSlack (Nat.log2 M + 1) j) hM hnonempty
    { r with usage := r.terminal } R.source R.terminal R.source_terminal
    ks ka ss st hs ht D hzero coefficient
    (fun bin hb _ m _ hm hp => ih bin hb m hm hp)
  have hcenter (j : ℕ) : rowNormPow 4 P r.source.rate
      (retainedMask R.source (side P ks) B.padding ss)
      (retainedMask R.terminal (side P ka) B.padding st)
      (fun σ x y => (A j - C j) σ x y - rowSliceMean
        (retainedMask R.source (side P ks) B.padding ss)
        (retainedMask R.terminal (side P ka) B.padding st) (A j - C j) x y) ≤
      B.initialCenteredGroupCharge M (dyadicSlack (Nat.log2 M + 1) j)
        { r with usage := r.terminal } coefficient := by
    obtain ⟨a, c, ha, hc, he, _⟩ := hc j
    have hea : a = A j := Option.some.inj (ha.symm.trans (hA j))
    have hec : c = C j := Option.some.inj (hc.symm.trans (hCrun j))
    subst a
    subst c
    simpa only [initialCenteredGroupCharge, hs, ht, gridChannel,
      CorrectionRowTask.Channel.retains, channels, semanticSide_grid, X, Y, retainedMask,
      rowNormPow, rowSliceMean] using he
  obtain ⟨groups, hgroups, hrows⟩ := B.initial_compressed_four_moments M hM n hbins hrate
    hcutoff haux hD H hn r R ks ka ss st hs ht hks hC hC1 exponent ζ floor A C
    (fun i => B.initialRootGroupCharge M (dyadicSlack (Nat.log2 M + 1) i)
      { r with usage := r.terminal } coefficient)
    (fun j _ => hA j) (fun j _ => hCrun j) (fun j _ => herr j)
    bin ku husage hu hLh hLρ hh hρ
  refine ⟨groups, hgroups, ?_⟩
  dsimp only
  intro W hW j hj
  obtain ⟨gmean, hgmean, hmean⟩ := B.initial_compressed_precision_clipped_first M hM n hbins
    hrate hcutoff haux hD H hn r R ks ka ss st hs ht hks hC hC1 exponent ζ floor D hzero
    coefficient ih (side P ku)
    (secondSignalIncrement (fun i σ x y => W[i - 1]?.getD 0 σ x y) ζ)
  obtain ⟨gendpoint, hgendpoint, hendpoint⟩ :=
    B.initial_compressed_precision_clipped_endpoint_first M hM n hbins hrate hcutoff haux
      hD H hn r R ks ka ss st hs ht hks hC hC1 exponent ζ floor D hzero coefficient ih
      (side P ku) (secondSignalIncrement (fun i σ x y => W[i - 1]?.getD 0 σ x y) ζ)
  have heendpoint := Option.some.inj (hgendpoint.symm.trans hgroups)
  subst gendpoint
  have he := Option.some.inj (hgmean.symm.trans hgroups)
  subst gmean
  let F := fun p σ x y => ((groups.take p).map (fun T => T σ x y)).sum
  let Δ := firstSignalIncrement F ka
    (secondSignalIncrement (fun i σ x y => W[i - 1]?.getD 0 σ x y) ζ)
  let cost := B.initialComputedPrecisionMoment M n r R ks ka ss st coefficient ζ Lh Lρ j
  let mean := fun (ν : Fin 2) => rowNormPow 4 P r.source.rate
    (retainedMask R.source (side P ks) B.padding ss)
    (retainedMask R.terminal (if ν = 0 then side P ka else side P ku) B.padding st)
    (fun _ x y => actualClippedMean HP R.source R.terminal (side P ks) (side P ka)
      (side P ku) B.padding ss st ka B.base ζ Δ 0 ν j x y)
  let centered := fun (ν : Fin 2) => rowNormPow 4 P r.source.rate
    (retainedMask R.source (side P ks) B.padding ss)
    (retainedMask R.terminal (if ν = 0 then side P ka else side P ku) B.padding st)
    (actualNoiseEntry R.source R.terminal (side P ks) (side P ka) (side P ku)
      B.padding ss st ka B.base Δ 0 ν j)
  have hm0 : mean 0 ≤ cost false 0 := by
    dsimp only [mean, cost]
    simp only [initialComputedPrecisionMoment, Bool.not_false,
      and_self, ↓reduceIte]
    exact le_min (hrows W hW j hj 0).1 (le_min (hmean j hj) (hendpoint j hj))
  have hn0 : centered 0 ≤ cost true 0 := by
    dsimp only [centered, cost]
    simp only [initialComputedPrecisionMoment, initialComputedCenteredNoise,
      Bool.not_true, Bool.false_eq_true, false_and, ↓reduceIte, and_self]
    apply le_min (hrows W hW j hj 0).2
    have hb := B.initial_compressed_centered_first_noise exponent ζ floor M hM hnonempty
      r R ks ka ss st hs ht A C coefficient (fun i _ => hA i)
      (fun i _ => hCrun i) (fun i _ => hcenter i) groups hgroups hC (side P ku)
      (secondSignalIncrement (fun i σ x y => W[i - 1]?.getD 0 σ x y) ζ) j hj
    apply le_min hb
    split_ifs with hadm
    · obtain ⟨hcharge, hrate', htask, hp, H', ha, hi⟩ := hadm
      obtain ⟨g, hg, hn⟩ := B.initial_compressed_normalized_noise_consumer hcharge hrate' H'
        exponent ζ floor M hM hnonempty r R ks ka ss st hs ht htask ha hi hp D hzero
        coefficient (fun _ bin hb _ m _ hm hp => ih bin hb m hm hp) hC
      have he : g = groups := Option.some.inj (hg.symm.trans hgroups)
      subst g
      exact hn (side P ku)
        (secondSignalIncrement (fun i σ x y => W[i - 1]?.getD 0 σ x y) ζ) j hj
    · exact hb
  have hm1 := B.initialSecondSignal_relative_mean_moment M bin ka ku husage r R ks ss st
    hs ht hu (congrFun haux bin) F W hW hC hLh hLρ hh hρ ζ j hj hm0 hn0
  intro ν
  change mean ν ≤ cost false ν ∧ centered ν ≤ cost true ν
  by_cases hν : ν = 0
  · subst ν
    exact ⟨hm0, hn0⟩
  · have hν1 : ν = 1 := by fin_cases ν <;> simp_all
    subst ν
    constructor
    · dsimp only [mean, cost]
      simp only [initialComputedPrecisionMoment, Bool.not_false, and_self, ↓reduceIte]
      apply le_min (hrows W hW j hj 1).1
      simpa only [cost, initialComputedPrecisionMoment, Bool.not_false, Bool.not_true,
        Bool.false_eq_true, false_and, (show (0 : Fin 2) ≠ 1 by decide),
        (show (1 : Fin 2) ≠ 0 by decide), and_false, and_self, ↓reduceIte] using hm1
    · dsimp only [centered, cost]
      simp only [initialComputedPrecisionMoment, Bool.not_true, Bool.false_eq_true,
        false_and, (show (1 : Fin 2) ≠ 0 by decide), and_false, and_self, ↓reduceIte]
      apply le_min (hrows W hW j hj 1).2
      split_ifs with hadm
      · obtain ⟨_, _, _, ⟨H', hks'⟩, _⟩ := hadm
        have hz := B.initialSecondSignal_noise_allocated M bin r R H' ks ka ku hks' husage
          ss st hs ht hu (congrFun haux bin) F W hW B.base ζ j hj
        change rowNormPow 4 P r.source.rate
          (retainedMask R.source (side P ks) B.padding ss)
          (retainedMask R.terminal (side P ku) B.padding st)
          (actualNoiseEntry R.source R.terminal (side P ks) (side P ka) (side P ku)
            B.padding ss st ka B.base Δ (fun _ _ _ _ => 0) 1 j) ≤ _
        exact hz
      · exact (hrows W hW j hj 1).2

/-- The four literal row maxima are paid from own-request lower-budget rooted precision.
Minkowski retains all explicit computed costs and their separate masks. -/
theorem initial_compressed_precision_fourMax
    (exponent : HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℕ)
    (ζ floor : ℝ)
    (D : ℕ → ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hzero : ∀ bin, D bin 0 = 0) (coefficient : ℝ)
    (ih : ∀ bin ∈ B.bins, ∀ m < M, 0 < m →
      let q := { r with usage := r.terminal }
      let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
        q.source (midpoint q) q.terminal (B.binRate bin)
      B.compressedBin m bin (exponent Q.direct) ζ floor Q.direct = some (D bin m) ∧
      rootDistPow 4 P Q.direct.source.rate
        (fun σ x => Q.direct.source.retains (channels B.padding) σ x)
        (fun σ y => Q.direct.usage.retains (channels B.padding) σ y) (D bin m)
        (denseChild B.padding id Q.direct (B.cutoff bin) (B.auxiliary bin)
          HP.ρ HP.K B.base) ≤
        coefficient ^ 4 * ((2 : ℝ) ^ (-B.requestPrecision m Q.direct)) ^ 4 ∧
      ∃ R, B.compressedBin m bin (exponent Q.right) ζ floor Q.right = some R)
    (bin ku : ℕ) (husage : ka ≤ ku)
    (hu : r.usage = gridChannel R.terminal ku st)
    {Lh Lρ : ℝ} (hLh : 0 ≤ Lh) (hLρ : 0 ≤ Lρ)
    (hh : ∀ a b, |polynomialPrepCutoff4 HP.θ a - polynomialPrepCutoff4 HP.θ b| ≤ Lh * |a - b|)
    (hρ : ∀ a b, |HP.ρ a - HP.ρ b| ≤ Lρ * |a - b|) :
    ∃ groups,
      (List.range (Nat.log2 M + 1)).mapM (fun j =>
        B.completedGroup (fun m q => if m < M then B.compressedHistory exponent ζ floor m q
          else none) M (dyadicSlack (Nat.log2 M + 1) j) (.pilotInput ⟨0, HP.k_pos⟩)
          { r with usage := r.terminal }) = some groups ∧
      let F := fun p σ x y => ((groups.take p).map (fun T => T σ x y)).sum
      ∀ W,
        (List.range (Nat.log2 M + 1)).mapM (fun i =>
          B.complete M r (B.binPreparation bin r (F (i + 1)))
            (dyadicSlack (Nat.log2 M + 1) i)) = some W →
        let Δ := firstSignalIncrement F ka
          (secondSignalIncrement (fun i σ x y => W[i - 1]?.getD 0 σ x y) ζ)
        let a := fun j noise ν =>
          B.initialComputedPrecisionMoment M n r R ks ka ss st coefficient
            ζ Lh Lρ j noise ν ^ (4⁻¹ : ℝ)
        ∀ j < Nat.log2 M + 1,
          vertexNormPow 4 P r.source.rate (retainedMask R.source (side P ks) B.padding ss)
            (actualFourMax HP R.source R.terminal (side P ks) (side P ka) (side P ku)
              B.padding ss st ka B.base ζ Δ 0 j) ≤
            ((a j false 0 + a j false 1) + (a j true 0 + a j true 1)) ^ 4 ∧
          rowNormPow 4 P r.source.rate
            (retainedMask R.source (side P ks) B.padding ss)
            (retainedMask R.terminal (side P ka) B.padding st)
            (fun σ x y =>
              let truth := requestSignals ζ B.padding id r (fun _ => B.base)
                (B.binPreparation bin r (fun _ => B.base)) σ x y
              clippedError (truth 0) (truth 1)
                (uncompressedRow (Δ σ x) 0 (j + 1) y)) ≤
            ((a j false 0 + a j false 1) + (a j true 0 + a j true 1)) ^ 4 := by
  obtain ⟨groups, hgroups, hrows⟩ := B.initial_compressed_precision_moments M hM n hbins hrate
    hcutoff haux hD H hn r R ks ka ss st hs ht hks hC hC1 exponent ζ floor D hzero coefficient
    ih bin ku husage hu hLh hLρ hh hρ
  refine ⟨groups, hgroups, ?_⟩
  dsimp only
  intro W hW j hj
  let F := fun p σ x y => ((groups.take p).map (fun T => T σ x y)).sum
  let Δ := firstSignalIncrement F ka
    (secondSignalIncrement (fun i σ x y => W[i - 1]?.getD 0 σ x y) ζ)
  let cost := B.initialComputedPrecisionMoment M n r R ks ka ss st coefficient ζ Lh Lρ j
  have hNu : 0 ≤ (P : ℝ) * r.source.rate := by
    rw [hs]; exact mul_nonneg (Nat.cast_nonneg _) (rate_pos ks).le
  have hnon (noise : Bool) (ν : Fin 2) : 0 ≤ cost noise ν := by
    cases noise
    · exact (rowNormPow_nonneg hNu _).trans (hrows W hW j hj ν).1
    · exact (rowNormPow_nonneg hNu _).trans (hrows W hW j hj ν).2
  have hpow (noise : Bool) (ν : Fin 2) :
      (cost noise ν ^ (4⁻¹ : ℝ)) ^ 4 = cost noise ν :=
    Real.rpow_inv_natCast_pow (hnon noise ν) (by decide : 4 ≠ 0)
  have hm (ν : Fin 2) : rowNormPow 4 P r.source.rate
      (retainedMask R.source (side P ks) B.padding ss)
      (retainedMask R.terminal (if ν = 0 then side P ka else side P ku) B.padding st)
      (fun _ x y => actualClippedMean HP R.source R.terminal (side P ks) (side P ka)
        (side P ku) B.padding ss st ka B.base ζ Δ 0 ν j x y) ≤
      (cost false ν ^ (4⁻¹ : ℝ)) ^ 4 := by
    rw [hpow]; exact (hrows W hW j hj ν).1
  have hz (ν : Fin 2) : rowNormPow 4 P r.source.rate
      (retainedMask R.source (side P ks) B.padding ss)
      (retainedMask R.terminal (if ν = 0 then side P ka else side P ku) B.padding st)
      (actualNoiseEntry R.source R.terminal (side P ks) (side P ka) (side P ku)
        B.padding ss st ka B.base Δ 0 ν j) ≤ (cost true ν ^ (4⁻¹ : ℝ)) ^ 4 := by
    rw [hpow]; exact (hrows W hW j hj ν).2
  constructor
  · apply actualFourMax_budget HP R.source R.terminal (side P ks) (side P ka) (side P ku)
      B.padding ss st ka B.base ζ Δ 0 j hNu
      (fun ν => cost false ν ^ (4⁻¹ : ℝ)) (fun ν => cost true ν ^ (4⁻¹ : ℝ))
      (fun ν => Real.rpow_nonneg (hnon false ν) _)
      (fun ν => Real.rpow_nonneg (hnon true ν) _)
    · intro ν
      exact (vertex_row_max (retainedMask R.source (side P ks) B.padding ss)
        (retainedMask R.terminal (if ν = 0 then side P ka else side P ku) B.padding st)
        hNu _).trans (hm ν)
    · intro ν
      exact actualNoiseMax_budget _ _ _ _ _ _ _ _ _ B.base hC Δ 0 hNu ν j (hz ν)
  · simp_rw [B.requestSignals_eq_genuineTarget bin ka ku r R ks ss st hs ht hu
      (congrFun haux bin) B.base ζ]
    have hsub : side P ku ≤ side P ka := by
      apply (ceilDiv_le_iff_le_mul (by positivity : 0 < (2 : ℕ) ^ ku)).2
      have h := le_smul_ceilDiv (by positivity : 0 < (2 : ℕ) ^ ka) (b := P)
      exact h.trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) husage))
    have hb := raw_prefix_four_budget HP R.source R.terminal
      (side P ks) (side P ka) (side P ku) B.padding ss st ka B.base hC ζ Δ 0 j
      (B.preparationPrefix_zero_off M bin ka ku r R ks ss st hs hu F W hW ζ j hj)
      (fun σ y hy => mem_retentionBox.mpr (fun v =>
        (mem_retentionBox.mp hy v).trans_le hsub)) hNu
      (fun ν => cost false ν ^ (4⁻¹ : ℝ)) (fun ν => cost true ν ^ (4⁻¹ : ℝ))
      (fun ν => Real.rpow_nonneg (hnon false ν) _)
      (fun ν => Real.rpow_nonneg (hnon true ν) _) hm hz
    exact hb

/-- The literal decoded-history sharp reserve is paid by explicit numerical costs of
strict lower-budget own-request rooted hypotheses. No parent accuracy, supplied four-max
budget or desired reserve is assumed. The first noise uses the minimum of the absolute
and pairwise conditional payments. The second bound consumes the joint stationary, final,
raw and actual rarity-tail deterministic first-mean payments, separately from semantic
deficit, second mean and both centered noises. Raw is charged after aggregating weighted
first moments, rather than using the old unconditional fourth-moment envelope. The original
unconditional envelope remains available as the first bound.
The third bound assembles the complete first mean on the bounded family using the same
scalar as `initialFirstTransportPayment`. Its fixed-charge certificate is
`initialComputedFirstBudgets_exists_charge`; the second mean, noises and simultaneous IH
remain separate obligations. -/
theorem initial_compressed_precision_reserve
    (exponent : HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℕ)
    (ζ floor : ℝ)
    (D : ℕ → ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hzero : ∀ bin, D bin 0 = 0) (coefficient : ℝ)
    (ih : ∀ bin ∈ B.bins, ∀ m < M, 0 < m →
      let q := { r with usage := r.terminal }
      let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
        q.source (midpoint q) q.terminal (B.binRate bin)
      B.compressedBin m bin (exponent Q.direct) ζ floor Q.direct = some (D bin m) ∧
      rootDistPow 4 P Q.direct.source.rate
        (fun σ x => Q.direct.source.retains (channels B.padding) σ x)
        (fun σ y => Q.direct.usage.retains (channels B.padding) σ y) (D bin m)
        (denseChild B.padding id Q.direct (B.cutoff bin) (B.auxiliary bin)
          HP.ρ HP.K B.base) ≤
        coefficient ^ 4 * ((2 : ℝ) ^ (-B.requestPrecision m Q.direct)) ^ 4 ∧
      ∃ R, B.compressedBin m bin (exponent Q.right) ζ floor Q.right = some R)
    (bin ku : ℕ) (husage : ka ≤ ku)
    (hu : r.usage = gridChannel R.terminal ku st)
    {Lh Lρ : ℝ} (hLh : 0 ≤ Lh) (hLρ : 0 ≤ Lρ)
    (hh : ∀ a b, |polynomialPrepCutoff4 HP.θ a - polynomialPrepCutoff4 HP.θ b| ≤ Lh * |a - b|)
    (hρ : ∀ a b, |HP.ρ a - HP.ρ b| ≤ Lρ * |a - b|)
    (hka : ka ≤ H.maxExponent) (hfloor : 0 < floor)
    (hcharge : 0 ≤ B.rankCharge)
    (htask : r.task = .row 0 (.pilotInput ⟨0, HP.k_pos⟩)) (cap Cdecoder Cpre : ℝ) :
    ∃ groups,
      (List.range (Nat.log2 M + 1)).mapM (fun j =>
        B.completedGroup (fun m q => if m < M then B.compressedHistory exponent ζ floor m q
          else none) M (dyadicSlack (Nat.log2 M + 1) j) (.pilotInput ⟨0, HP.k_pos⟩)
          { r with usage := r.terminal }) = some groups ∧
      let F := fun p σ x y => ((groups.take p).map (fun T => T σ x y)).sum
      ∀ W,
        (List.range (Nat.log2 M + 1)).mapM (fun i =>
          B.complete M r (B.binPreparation bin r (F (i + 1)))
            (dyadicSlack (Nat.log2 M + 1) i)) = some W →
        let a := fun j noise ν =>
          B.initialComputedPrecisionMoment M n r R ks ka ss st coefficient
            ζ Lh Lρ j noise ν ^ (4⁻¹ : ℝ)
        (B.initialFourMaxReserve M bin ka ζ floor r R ks ku ss st B.base F W cap
          Cdecoder Cpre ≤ initialNumericalReserve HP M floor cap Cdecoder Cpre
            (fun j => (a j false 0 + a j false 1) + (a j true 0 + a j true 1))) ∧
(B.initialFourMaxReserve M bin ka ζ floor r R ks ku ss st B.base F W cap
          Cdecoder Cpre ≤
          initialSeparatedReserve HP Cdecoder Cpre
            (B.initialComputedFirstPreBudget M n r R ks ka ss st coefficient floor +
              ∑ j ∈ range (Nat.log2 M + 1), dyadicFloor floor (Nat.log2 M + 1) j *
                (a j false 1 + (a j true 0 + a j true 1)))
            (B.initialComputedFirstFinalPayment M n r R ks ka ss st coefficient +
              (a (Nat.log2 M) false 1 + (a (Nat.log2 M) true 0 + a (Nat.log2 M) true 1)))
            ((B.initialComputedFirstTailBudget M n r R ks ka ss st coefficient floor +
              ∑ j ∈ range (Nat.log2 M + 1),
              (((2 + 256 / dyadicFloor floor (Nat.log2 M + 1) j) /
                (compatibleCapacity HP.K (Nat.log2 M + 1) j : ℝ)) ^ (4⁻¹ : ℝ)) *
              ∑ i ∈ Ico j (Nat.log2 M + 1), (28 : ℝ) ^ (Nat.log2 M + 1 - i) *
                a i false 1) +
              ∑ i ∈ range (Nat.log2 M + 1), (28 : ℝ) ^ (Nat.log2 M + 1 - i) *
                (a i true 0 + a i true 1))
            (64 * (B.initialComputedFirstRawBudget M n r R ks ka ss st coefficient floor
                ((2 * max cap 16) ^ (4⁻¹ : ℝ)) +
              ∑ j ∈ range (Nat.log2 M + 1),
                (64 * (HP.K : ℝ) * ((2 * max cap 16) ^ (4⁻¹ : ℝ)) ^ 4 /
                  ((compatibleCapacity HP.K (Nat.log2 M + 1) j : ℝ) *
                    dyadicFloor floor (Nat.log2 M + 1) j ^ 4)) *
                ((a j false 1 ^ 4) + (a j true 0 ^ 4 + a j true 1 ^ 4))))) ∧
        (1 < M → B.slack * (1 + 4 * (n + ka)) < M → M ≤ 32 * B.slack * n →
        2 * ka ≤ n → P ≤ 2 ^ (n + 1) →
        let K := (max (512 * (6 * B.binCap + 3) ^ 3) (32768 * B.binCap ^ 3)) ^
          (4⁻¹ : ℝ) * |coefficient| * (2 : ℝ) ^ (-B.requestPrecision M r) *
            (2 : ℝ) ^ (-B.rankCharge)
        let S := (32 : ℝ) ^ (4⁻¹ : ℝ) * (2 : ℝ) ^ (-B.requestPrecision M r) *
          (2 : ℝ) ^ (-(B.rankCharge * r.task.rank))
        let x := 2 * (K * (4 * ∑' h, LogSpaceEstimation.scaleMajorant h) + S)
        B.initialFourMaxReserve M bin ka ζ floor r R ks ku ss st B.base F W cap
          Cdecoder Cpre ≤
          initialSeparatedReserve HP Cdecoder Cpre
            ((8 : ℝ) ^ (4⁻¹ : ℝ) * x * floor / 511 +
              ∑ j ∈ range (Nat.log2 M + 1), dyadicFloor floor (Nat.log2 M + 1) j *
                (a j false 1 + (a j true 0 + a j true 1)))
            ((8 : ℝ) ^ (4⁻¹ : ℝ) * x +
              (a (Nat.log2 M) false 1 + (a (Nat.log2 M) true 0 + a (Nat.log2 M) true 1)))
            (((8 : ℝ) ^ (4⁻¹ : ℝ) * x * (2 + 256 / floor) ^ (4⁻¹ : ℝ) / 63 +
              ∑ j ∈ range (Nat.log2 M + 1),
              (((2 + 256 / dyadicFloor floor (Nat.log2 M + 1) j) /
                (compatibleCapacity HP.K (Nat.log2 M + 1) j : ℝ)) ^ (4⁻¹ : ℝ)) *
              ∑ i ∈ Ico j (Nat.log2 M + 1), (28 : ℝ) ^ (Nat.log2 M + 1 - i) *
                a i false 1) +
              ∑ i ∈ range (Nat.log2 M + 1), (28 : ℝ) ^ (Nat.log2 M + 1 - i) *
                (a i true 0 + a i true 1))
            (64 * (8 * x ^ 4 * (64 * (HP.K : ℝ) * ((2 * max cap 16) ^ (4⁻¹ : ℝ)) ^ 4 /
                ((HP.K + 1) * floor ^ 4)) / 63 +
              ∑ j ∈ range (Nat.log2 M + 1),
                (64 * (HP.K : ℝ) * ((2 * max cap 16) ^ (4⁻¹ : ℝ)) ^ 4 /
                  ((compatibleCapacity HP.K (Nat.log2 M + 1) j : ℝ) *
                    dyadicFloor floor (Nat.log2 M + 1) j ^ 4)) *
                ((a j false 1 ^ 4) + (a j true 0 ^ 4 + a j true 1 ^ 4))))) := by
  obtain ⟨groups, hgroups, hpaid⟩ := B.initial_compressed_precision_fourMax M hM n hbins hrate
    hcutoff haux hD H hn r R ks ka ss st hs ht hks hC hC1 exponent ζ floor D hzero coefficient
    ih bin ku husage hu hLh hLρ hh hρ
  obtain ⟨grows, hgrows, hrows⟩ := B.initial_compressed_precision_moments M hM n hbins hrate
    hcutoff haux hD H hn r R ks ka ss st hs ht hks hC hC1 exponent ζ floor D hzero coefficient
    ih bin ku husage hu hLh hLρ hh hρ
  have he := Option.some.inj (hgrows.symm.trans hgroups)
  subst grows
  refine ⟨groups, hgroups, ?_⟩
  dsimp only
  intro W hW
  have hr : 0 ≤ r.source.rate := by rw [hs]; exact (rate_pos ks).le
  constructor
  · apply B.initialFourMaxReserve_le M bin ka ζ floor hfloor.le r hr R ks ku ss st B.base _ W
      cap Cdecoder Cpre _ (fun j => by
        have hc (noise : Bool) (ν : Fin 2) :=
          B.initialComputedPrecisionMoment_nonneg M n r hr R ks ka ss st
            coefficient ζ Lh Lρ j noise ν
        exact add_nonneg
          (add_nonneg (Real.rpow_nonneg (hc false 0) _) (Real.rpow_nonneg (hc false 1) _))
          (add_nonneg (Real.rpow_nonneg (hc true 0) _) (Real.rpow_nonneg (hc true 1) _)))
    · intro j hj
      have h := (hpaid W hW j hj).1
      simp only [hs, gridChannel, CorrectionRowTask.Channel.retains, channels,
        semanticSide_grid] at h ⊢
      convert h using 1; congr 8
    · intro j hj
      have h := (hpaid W hW j hj).2
      simp only [hs, ht, gridChannel, CorrectionRowTask.Channel.retains, channels,
        semanticSide_grid] at h ⊢
      convert h using 1; congr 8
  · let F := fun p σ x y => ((groups.take p).map (fun T => T σ x y)).sum
    let a := fun j noise ν =>
      B.initialComputedPrecisionMoment M n r R ks ka ss st coefficient ζ Lh Lρ j noise ν ^
        (4⁻¹ : ℝ)
    have hsep : B.initialFourMaxReserve M bin ka ζ floor r R ks ku ss st B.base F W cap
          Cdecoder Cpre ≤
          initialSeparatedReserve HP Cdecoder Cpre
            (B.initialComputedFirstPreBudget M n r R ks ka ss st coefficient floor +
              ∑ j ∈ range (Nat.log2 M + 1), dyadicFloor floor (Nat.log2 M + 1) j *
                ((a j false 1) + (a j true 0 + a j true 1)))
            (B.initialComputedFirstFinalPayment M n r R ks ka ss st coefficient +
              (a (Nat.log2 M) false 1 + (a (Nat.log2 M) true 0 + a (Nat.log2 M) true 1)))
            ((B.initialComputedFirstTailBudget M n r R ks ka ss st coefficient floor +
              ∑ j ∈ range (Nat.log2 M + 1),
              (((2 + 256 / dyadicFloor floor (Nat.log2 M + 1) j) /
                (compatibleCapacity HP.K (Nat.log2 M + 1) j : ℝ)) ^ (4⁻¹ : ℝ)) *
              ∑ i ∈ Ico j (Nat.log2 M + 1), (28 : ℝ) ^ (Nat.log2 M + 1 - i) *
                a i false 1) +
              ∑ i ∈ range (Nat.log2 M + 1), (28 : ℝ) ^ (Nat.log2 M + 1 - i) *
                (a i true 0 + a i true 1))
            (64 * (B.initialComputedFirstRawBudget M n r R ks ka ss st coefficient floor
                ((2 * max cap 16) ^ (4⁻¹ : ℝ)) +
              ∑ j ∈ range (Nat.log2 M + 1),
                (64 * (HP.K : ℝ) * ((2 * max cap 16) ^ (4⁻¹ : ℝ)) ^ 4 /
                  ((compatibleCapacity HP.K (Nat.log2 M + 1) j : ℝ) *
                    dyadicFloor floor (Nat.log2 M + 1) j ^ 4)) *
                (((a j false 1) ^ 4) + (a j true 0 ^ 4 + a j true 1 ^ 4)))) := by
      apply B.initialFourMaxReserve_le_tail M bin ka ζ floor hfloor.le r hr R ks ku ss st B.base _ W
        cap Cdecoder Cpre (fun j =>
          let a := fun noise ν => B.initialComputedPrecisionMoment M n r R ks ka ss st
            coefficient ζ Lh Lρ j noise ν ^ (4⁻¹ : ℝ)
          (a false 0 + a false 1) + (a true 0 + a true 1)) _ _ _ _ (fun j => by
          have hc (noise : Bool) (ν : Fin 2) :=
            B.initialComputedPrecisionMoment_nonneg M n r hr R ks ka ss st
              coefficient ζ Lh Lρ j noise ν
          exact add_nonneg
            (add_nonneg (Real.rpow_nonneg (hc false 0) _) (Real.rpow_nonneg (hc false 1) _))
            (add_nonneg (Real.rpow_nonneg (hc true 0) _) (Real.rpow_nonneg (hc true 1) _)))
      · have hp := B.initialComputedPrecisionMoment_first_pre_le hcharge hrate H M n ks ka
          hka (fun bin hi => by rw [hbins, mem_range] at hi; omega) r hr
          (by simp only [hs, gridChannel]) (by simp only [ht, gridChannel]) htask
          R ss st coefficient ζ Lh Lρ floor hfloor.le
        dsimp only [a]
        simp only [mul_add, sum_add_distrib]
        linarith only [hp]
      · have hp := B.initialComputedPrecisionMoment_first_final_payment_le hcharge hrate H M n ks ka
          hka hks hbins hn r
          (by simp only [hs, gridChannel]) (by simp only [ht, gridChannel]) htask hC
          R ss st coefficient ζ Lh Lρ
        dsimp only [a]
        linarith only [hp]
      · intro j hj
        have h := (hpaid W hW j hj).1
        simp only [hs, gridChannel, CorrectionRowTask.Channel.retains, channels,
          semanticSide_grid] at h ⊢
        convert h using 1; congr 8
      · let cost := B.initialComputedPrecisionMoment M n r R ks ka ss st coefficient ζ Lh Lρ
        let w := fun j => 64 * (HP.K : ℝ) * ((2 * max cap 16) ^ (4⁻¹ : ℝ)) ^ 4 /
          ((compatibleCapacity HP.K (Nat.log2 M + 1) j : ℝ) *
            dyadicFloor floor (Nat.log2 M + 1) j ^ 4)
        have hw (j : ℕ) : 0 ≤ w j := by dsimp only [w]; positivity
        have hc (j : ℕ) (noise : Bool) (ν : Fin 2) : 0 ≤ cost j noise ν :=
          B.initialComputedPrecisionMoment_nonneg M n r hr R ks ka ss st coefficient
            ζ Lh Lρ j noise ν
        have hp := B.initialComputedPrecisionMoment_first_raw_le hcharge hrate H M n ks ka
          hka (fun bin hi => by rw [hbins, mem_range] at hi; omega) r
          (by simp only [hs, gridChannel]) (by simp only [ht, gridChannel]) htask
          R ss st coefficient ζ Lh Lρ floor ((2 * max cap 16) ^ (4⁻¹ : ℝ)) hfloor
        have hsum : (∑ j ∈ range (Nat.log2 M + 1), w j *
            (let a := fun noise ν => cost j noise ν ^ (4⁻¹ : ℝ)
             ((a false 0 + a false 1) + (a true 0 + a true 1)) ^ 4)) ≤
            (64 * (B.initialComputedFirstRawBudget M n r R ks ka ss st coefficient floor
              ((2 * max cap 16) ^ (4⁻¹ : ℝ)) +
              ∑ j ∈ range (Nat.log2 M + 1), w j *
                ((cost j false 1 ^ (4⁻¹ : ℝ)) ^ 4 +
                  ((cost j true 0 ^ (4⁻¹ : ℝ)) ^ 4 + (cost j true 1 ^ (4⁻¹ : ℝ)) ^ 4)))) := by
          apply le_trans (sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
            (four_sum_pow_le _ _ _ _
              (Real.rpow_nonneg (hc j false 0) _) (Real.rpow_nonneg (hc j false 1) _)
              (Real.rpow_nonneg (hc j true 0) _) (Real.rpow_nonneg (hc j true 1) _)) (hw j))
          simp only [mul_add, sum_add_distrib, mul_left_comm (w _) 64, ← mul_sum]
          have hpow (j : ℕ) : (cost j false 0 ^ (4⁻¹ : ℝ)) ^ 4 = cost j false 0 :=
            Real.rpow_inv_natCast_pow (hc j false 0) (by decide : 4 ≠ 0)
          simp_rw [hpow]
          change (∑ j ∈ range (Nat.log2 M + 1), w j * cost j false 0) ≤ _ at hp
          linarith only [hp]
        apply le_trans _ hsum
        apply sum_le_sum
        intro j hj
        apply mul_le_mul_of_nonneg_left _ (hw j)
        have hh := (hpaid W hW j (mem_range.mp hj)).2
        simp only [hs, ht, gridChannel, CorrectionRowTask.Channel.retains, channels,
          semanticSide_grid] at hh ⊢
        convert hh using 1
        congr 8
      · let F := fun p σ x y => ((groups.take p).map (fun T => T σ x y)).sum
        let Δ := firstSignalIncrement F ka
          (secondSignalIncrement (fun i σ x y => W[i - 1]?.getD 0 σ x y) ζ)
        let cost := B.initialComputedPrecisionMoment M n r R ks ka ss st coefficient ζ Lh Lρ
        let a := fun ν i => cost i false ν ^ (4⁻¹ : ℝ)
        let b := fun ν i => cost i true ν ^ (4⁻¹ : ℝ)
        have hNu := mul_nonneg (Nat.cast_nonneg P) hr
        have hc (i : ℕ) (noise : Bool) (ν : Fin 2) : 0 ≤ cost i noise ν :=
          B.initialComputedPrecisionMoment_nonneg M n r hr R ks ka ss st
            coefficient ζ Lh Lρ i noise ν
        have hm (ν : Fin 2) (i : ℕ) (hi : i < Nat.log2 M + 1) :
            rowNormPow 4 P r.source.rate (retainedMask R.source (side P ks) B.padding ss)
              (retainedMask R.terminal (if ν = 0 then side P ka else side P ku) B.padding st)
              (fun _ => actualClippedMean HP R.source R.terminal (side P ks) (side P ka)
                (side P ku) B.padding ss st ka B.base ζ Δ 0 ν i) ≤ a ν i ^ 4 := by
          rw [show a ν i ^ 4 = cost i false ν from
            Real.rpow_inv_natCast_pow (hc i false ν) (by decide : 4 ≠ 0)]
          exact (hrows W hW i hi ν).1
        have hz (ν : Fin 2) (i : ℕ) (hi : i < Nat.log2 M + 1) :
            vertexNormPow 4 P r.source.rate (retainedMask R.source (side P ks) B.padding ss)
              (actualNoiseMax R.source R.terminal (side P ks) (side P ka) (side P ku)
                B.padding ss st ka B.base Δ 0 ν i) ≤ b ν i ^ 4 := by
          apply actualNoiseMax_budget _ _ _ _ _ _ _ _ _ B.base hC Δ 0 hNu ν i
          rw [show b ν i ^ 4 = cost i true ν from
            Real.rpow_inv_natCast_pow (hc i true ν) (by decide : 4 ≠ 0)]
          exact (hrows W hW i hi ν).2
        have hb := integrated_fourMax_tail_schedule HP R.source R.terminal
          (Ne.symm R.source_terminal) (side P ks) (side P ku) B.padding hD ss st H hka
          (side_le P ku) B.base hC hfloor hNu
          (fun x => by simpa only [mulVec, dotProduct, Pi.one_apply, mul_one] using hC1 x)
          (Nat.log2 M + 1) (compatibleCapacity HP.K (Nat.log2 M + 1)) (fun _ => HP.K)
          (fun _ _ => by unfold compatibleCapacity; positivity) ζ Δ 0 a b
          (fun ν i _ => Real.rpow_nonneg (hc i false ν) _)
          (fun ν i _ => Real.rpow_nonneg (hc i true ν) _) hm hz
        simp only [mul_one] at hb
        simp only [mul_add, sum_add_distrib] at hb
        have hpay := B.initialComputedPrecisionMoment_first_tail_le hcharge hrate H M n ks ka
          hka (fun bin hi => by rw [hbins, mem_range] at hi; omega) r hr
          (by simp only [hs, gridChannel]) (by simp only [ht, gridChannel]) htask
          R ss st coefficient ζ Lh Lρ floor hfloor
        have hn : 0 ≤ (∑ j ∈ range (Nat.log2 M + 1),
            (((2 + 256 / dyadicFloor floor (Nat.log2 M + 1) j) /
              (compatibleCapacity HP.K (Nat.log2 M + 1) j : ℝ)) ^ (4⁻¹ : ℝ)) *
              ∑ i ∈ Ico j (Nat.log2 M + 1), (28 : ℝ) ^ (Nat.log2 M + 1 - i) * a 0 i) +
            (∑ j ∈ range (Nat.log2 M + 1),
            (((2 + 256 / dyadicFloor floor (Nat.log2 M + 1) j) /
              (compatibleCapacity HP.K (Nat.log2 M + 1) j : ℝ)) ^ (4⁻¹ : ℝ)) *
              ∑ i ∈ Ico j (Nat.log2 M + 1), (28 : ℝ) ^ (Nat.log2 M + 1 - i) * a 1 i) +
            ((∑ i ∈ range (Nat.log2 M + 1), (28 : ℝ) ^ (Nat.log2 M + 1 - i) * b 0 i) +
             ∑ i ∈ range (Nat.log2 M + 1), (28 : ℝ) ^ (Nat.log2 M + 1 - i) * b 1 i) := by
          have hroot (i : ℕ) (ν : Fin 2) : 0 ≤ a ν i := Real.rpow_nonneg (hc i false ν) _
          have hrootb (i : ℕ) (ν : Fin 2) : 0 ≤ b ν i := Real.rpow_nonneg (hc i true ν) _
          have hms (ν : Fin 2) : 0 ≤ ∑ j ∈ range (Nat.log2 M + 1),
              (((2 + 256 / dyadicFloor floor (Nat.log2 M + 1) j) /
                (compatibleCapacity HP.K (Nat.log2 M + 1) j : ℝ)) ^ (4⁻¹ : ℝ)) *
              ∑ i ∈ Ico j (Nat.log2 M + 1), (28 : ℝ) ^ (Nat.log2 M + 1 - i) * a ν i := by
            apply sum_nonneg
            intro j _
            have hf := dyadicFloor_pos hfloor (Nat.log2 M + 1) j
            exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
              (sum_nonneg fun i _ => mul_nonneg (by positivity) (hroot i ν))
          exact add_nonneg (add_nonneg (hms 0) (hms 1))
            (add_nonneg (sum_nonneg fun i _ => mul_nonneg (by positivity) (hrootb i 0))
              (sum_nonneg fun i _ => mul_nonneg (by positivity) (hrootb i 1)))
        have hnew := hb.trans (pow_le_pow_left₀ hn
          (add_le_add (add_le_add hpay le_rfl) le_rfl) 4)
        simp only [hs, ht, gridChannel, CorrectionRowTask.Channel.retains, channels,
          semanticSide_grid]
        simp_rw [B.requestSignals_eq_genuineTarget bin ka ku r R ks ss st hs ht hu
          (congrFun haux bin) B.base ζ]
        simp only [meanFirstEvent, genuineTarget, Fin.isValue, ↓reduceIte, hs,
          gridChannel, Pi.zero_apply, mul_add, sum_add_distrib] at hnew ⊢
        convert hnew using 1; congr 8
        simp only [heavyCountEvent, retainedMask]
        rfl
    refine ⟨hsep, ?_⟩
    intro hM1 hlo hhi ha hP
    obtain ⟨hp, hf, ht', hraw⟩ := B.initialComputedFirstBudgets_bounded_family hcharge
      M n ks ka hM1 hbins hrate hlo hhi ha hP H hks r
      (by simp only [hs, gridChannel]) (by simp only [ht, gridChannel]) hC R ss st
      coefficient floor ((2 * max cap 16) ^ (4⁻¹ : ℝ)) hfloor
    have hfinal := (B.initialComputedFirstFinalPayment_le M n r R ks ka ss st coefficient).trans hf
    have hcap := B.binCap_nonneg
    have hsum : 0 ≤ ∑' h, LogSpaceEstimation.scaleMajorant h :=
      tsum_nonneg fun h => LogSpaceEstimation.scaleMajorant_nonneg h
    have hapos (j : ℕ) (noise : Bool) (ν : Fin 2) : 0 ≤ a j noise ν :=
      Real.rpow_nonneg (B.initialComputedPrecisionMoment_nonneg M n r hr R ks ka ss st
        coefficient ζ Lh Lρ j noise ν) _
    obtain ⟨hpn, hfn, htn⟩ := B.initialComputedFirstBudgets_nonneg M n ks ka r hr
      R ss st coefficient floor hfloor.le
    have hpayn : 0 ≤ B.initialComputedFirstFinalPayment M n r R ks ka ss st coefficient := by
      unfold initialComputedFirstFinalPayment
      split_ifs
      · exact le_min hfn (by positivity)
      · exact hfn
    dsimp only [a] at hsep
    apply hsep.trans
    apply initialSeparatedReserve_mono HP Cdecoder Cpre
    · apply add_nonneg hpn
      exact sum_nonneg fun j _ => mul_nonneg (dyadicFloor_nonneg hfloor.le _ _)
        (add_nonneg (hapos j false 1) (add_nonneg (hapos j true 0) (hapos j true 1)))
    · exact add_nonneg hpayn (add_nonneg (hapos _ false 1)
        (add_nonneg (hapos _ true 0) (hapos _ true 1)))
    · apply add_nonneg (add_nonneg htn ?_) ?_
      · apply sum_nonneg
        intro j _
        have hfl := (dyadicFloor_pos hfloor (Nat.log2 M + 1) j).le
        apply mul_nonneg (Real.rpow_nonneg (by positivity) _)
        exact sum_nonneg fun i _ => mul_nonneg (by positivity) (hapos i false 1)
      · exact sum_nonneg fun i _ => mul_nonneg (by positivity)
          (add_nonneg (hapos i true 0) (hapos i true 1))
    · exact add_le_add hp le_rfl
    · exact add_le_add hfinal le_rfl
    · exact add_le_add (add_le_add ht' le_rfl) le_rfl
    · exact mul_le_mul_of_nonneg_left (add_le_add hraw le_rfl) (by norm_num : (0 : ℝ) ≤ 64)

end Polynomial

/-- Sharp parent comparison for literal computed approximate histories, using exactly
`compressedBin`'s shared decoder. This honest finite conditional reserve retains all actual
four-max and false-overflow costs. `initial_compressed_preparation` pays the second mean
and noise. The specialized reserve-assembly module pays their joint numerical reserve
on an explicit covered field/depth family; simultaneous recursive accuracy and availability
remain separate. Constants are fixed before width, budget, history and children,
in the shared kernel's order. -/
theorem exists_initial_compressed_fourMax (HP : FourthRootHierarchyParams 16 1 16 32 8)
    {cap ζ scale : ℝ} (hcap : 0 ≤ cap) (hζ : 0 < ζ) (hs : 0 < scale)
    (hmargin : scale ≤ HP.η) (hcapscale : scale ≤ max cap 16 / 10000)
    (hsmall : ζ ≤ scale / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ floor : ℝ, 0 < floor → floor ≤ scale → floor ≤ 1 →
      ∃ Cpre : ℝ, 0 ≤ Cpre ∧ ∀ {P : ℕ} [Fact P.Prime] (B : BudgetData HP P)
      (b : ℕ → ℝ), (∀ i, 0 < b i) → (∀ i, b i = 16 * b (i + 1)) →
      ∀ (M bin k : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)),
      Admissible r → r.terminal.rate = rate k →
      B.cutoff bin = boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1) b cap bin
        (fun _ => 1) → B.auxiliary bin = polynomialPrepCutoff4 HP.θ →
      ∀ (G : Matrix (ZMod P) (ZMod P) ℝ), (∀ x y, 0 ≤ G x y) →
      ∀ (exponent : HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℕ)
        (childζ childFloor : ℝ)
        (groups : List (Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)),
      (List.range (Nat.log2 M + 1)).mapM (fun j =>
        B.completedGroup (fun m q => if m < M then
          B.compressedHistory exponent childζ childFloor m q else none) M
          (dyadicSlack (Nat.log2 M + 1) j) (.pilotInput ⟨0, HP.k_pos⟩)
          { r with usage := r.terminal }) = some groups →
      let F := fun p σ x y => ((groups.take p).map (fun T => T σ x y)).sum
      ∀ W,
      (List.range (Nat.log2 M + 1)).mapM (fun j =>
        B.complete M r (B.binPreparation bin r (F (j + 1)))
          (dyadicSlack (Nat.log2 M + 1) j)) = some W →
      ∀ (R : RoleProfile 3) (ks ku : ℕ) (ss st : List (ZMod P)),
      r.source = gridChannel R.source ks ss →
      r.terminal = gridChannel R.terminal k st →
      r.usage = gridChannel R.terminal ku st →
      rootDistPow 4 P r.source.rate
        (fun σ x => r.source.retains (channels B.padding) σ x)
        (fun σ y => r.terminal.retains (channels B.padding) σ y)
        (B.decodePrefixes M bin k ζ floor r F W)
        (denseChild B.padding id r (B.cutoff bin) (polynomialPrepCutoff4 HP.θ) HP.ρ HP.K G) ≤
        B.initialFourMaxReserve M bin k ζ floor r R ks ku ss st G F W cap C Cpre := by
  obtain ⟨C, hC, hscales⟩ := exists_decodePrefixes_fourMax HP hcap hζ hs hmargin hcapscale hsmall
  refine ⟨C, hC, ?_⟩
  intro floor hf hfs hf1
  obtain ⟨Cp, hCp, hbound⟩ := hscales floor hf hfs hf1
  refine ⟨Cp, hCp, ?_⟩
  intro P _ B b hb hstep M bin k r hr hrate hcut haux G hG exponent childζ childFloor
    groups _
  dsimp only
  intro W hW R ks ku ss st hsource hterminal husage
  exact hbound B b hb hstep M bin k r hr hrate hcut haux G hG _ W hW R ks ku ss st
    hsource hterminal husage

end Matrix.HierarchyParams.H4RankEnvironment.BudgetData
