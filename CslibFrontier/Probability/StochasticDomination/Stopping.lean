/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.StochasticDomination.Adapted
public import CslibFrontier.Probability.StochasticDomination.PoissonBinomial
public import Mathlib.Probability.Process.HittingTime
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Infinite-horizon stopping-time mean bounds

Stopping-time finiteness, integrability, tail-sum expectation identity, and the infinite-horizon
mean bound `∫ ω, ((σ ω).untopD 0 : ℝ) ∂P ≤ r / p` for stopping times bounded by `r` successes
of an adapted Bernoulli sequence with conditional success probability at least `p > 0` while active.

## Main definitions

* `Cslib.Probability.withTopToENNReal`: embedding `WithTop ℕ → ℝ≥0∞` sending `⊤ ↦ ⊤`.
* `Cslib.Probability.countHittingTime`: first time `n : ℕ` at which `adaptedCount A n ω ≥ r`.

## Main results

* `Cslib.Probability.lintegral_withTopToENNReal`:
  `∫⁻ ω, withTopToENNReal (τ ω) ∂P = ∑' n, P {ω | (n : WithTop ℕ) < τ ω}`.
* `Cslib.Probability.integral_untopD_eq_tsum_real_lt`: finite survival-series integrability
  and expectation formula for `((τ ω).untopD 0 : ℝ)`.
* `Cslib.Probability.stoppingTime_mean_le_of_adaptedCount_le`: general `𝔼[σ] ≤ r / p` bound
  over a filtration `ℱ : Filtration ℕ m`.
* `Cslib.Probability.countHittingTime_mean_le`: `𝔼[countHittingTime A r] ≤ r / p`.
* `Cslib.Probability.traj_countHittingTime_mean_le`,
  `Cslib.Probability.trajMeasure_countHittingTime_mean_le`: specializations to
  `ProbabilityTheory.Kernel.traj` and `Kernel.trajMeasure`.
-/

public section

namespace Cslib.Probability

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal unitInterval

section WithTopMean

/-- Embed `WithTop ℕ` into `ℝ≥0∞`, sending `⊤` to `⊤` and `(n : ℕ)` to `(n : ℝ≥0∞)`. -/
@[expose]
noncomputable def withTopToENNReal : WithTop ℕ → ℝ≥0∞
  | ⊤ => ⊤
  | (n : ℕ) => (n : ℝ≥0∞)

@[simp]
theorem withTopToENNReal_top : withTopToENNReal ⊤ = ⊤ :=
  rfl

@[simp]
theorem withTopToENNReal_coe (n : ℕ) : withTopToENNReal (n : WithTop ℕ) = (n : ℝ≥0∞) :=
  rfl

theorem withTopToENNReal_eq_tsum_ite (x : WithTop ℕ) :
    withTopToENNReal x = ∑' n : ℕ, if (n : WithTop ℕ) < x then (1 : ℝ≥0∞) else 0 := by
  cases x with
  | top =>
    have htrue (n : ℕ) : (n : WithTop ℕ) < ⊤ := WithTop.coe_lt_top n
    simp only [htrue, ↓reduceIte, withTopToENNReal_top]
    exact (ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero).symm
  | coe k =>
    have hcoe : (WithTop.some k : WithTop ℕ) = (k : WithTop ℕ) := by simp
    change withTopToENNReal (WithTop.some k) = _
    rw [hcoe, withTopToENNReal_coe]
    symm
    calc
      (∑' n : ℕ, if (n : WithTop ℕ) < (k : WithTop ℕ) then (1 : ℝ≥0∞) else 0)
        = ∑ n ∈ Finset.range k, if n < k then (1 : ℝ≥0∞) else 0 := by
            simp only [Nat.cast_lt]
            refine tsum_eq_sum fun n hn => ?_
            simp only [Finset.mem_range, not_lt] at hn
            simp [not_lt.mpr hn]
      _ = ∑ _ ∈ Finset.range k, (1 : ℝ≥0∞) := by
            refine Finset.sum_congr rfl fun n hn => ?_
            rw [Finset.mem_range] at hn
            simp [hn]
      _ = k := by simp

/-- Tail-sum identity for `WithTop ℕ`-valued measurable random variables:
`∫⁻ ω, withTopToENNReal (τ ω) ∂P = ∑' n, P {ω | (n : WithTop ℕ) < τ ω}`. -/
theorem lintegral_withTopToENNReal {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {τ : Ω → WithTop ℕ} (hτ : Measurable τ) :
    ∫⁻ ω, withTopToENNReal (τ ω) ∂P = ∑' n : ℕ, P {ω | (n : WithTop ℕ) < τ ω} := by
  have hfun :
      (fun ω => withTopToENNReal (τ ω)) =
        fun ω => ∑' n : ℕ, {ω' | (n : WithTop ℕ) < τ ω'}.indicator (fun _ => (1 : ℝ≥0∞)) ω := by
    ext ω
    rw [withTopToENNReal_eq_tsum_ite]
    refine tsum_congr fun n => ?_
    by_cases h : (n : WithTop ℕ) < τ ω <;> simp [h]
  have hs (n : ℕ) : MeasurableSet {ω' | (n : WithTop ℕ) < τ ω'} := hτ measurableSet_Ioi
  have hm (n : ℕ) :
      Measurable ({ω' | (n : WithTop ℕ) < τ ω'}.indicator (fun _ => (1 : ℝ≥0∞))) :=
    measurable_const.indicator (hs n)
  rw [hfun, lintegral_tsum fun n => (hm n).aemeasurable]
  refine tsum_congr fun n => ?_
  rw [lintegral_indicator (hs n), lintegral_const, one_mul, Measure.restrict_apply_univ]

/-- If the real survival series `∑' n, P.real {n < τ}` converges under a finite measure `P`,
then `τ ≠ ⊤` a.e., `(τ ·).untopD 0` is integrable, and
`∫ ω, (τ ω).untopD 0 ∂P = ∑' n, P.real {n < τ}`. -/
theorem integral_untopD_eq_tsum_real_lt {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsFiniteMeasure P] {τ : Ω → WithTop ℕ} (hτ : Measurable τ)
    (hs : Summable fun n : ℕ => P.real {ω | (n : WithTop ℕ) < τ ω}) :
    (∀ᵐ ω ∂P, τ ω ≠ ⊤) ∧
      Integrable (fun ω => (((τ ω).untopD 0 : ℕ) : ℝ)) P ∧
      ∫ ω, (((τ ω).untopD 0 : ℕ) : ℝ) ∂P = ∑' n : ℕ, P.real {ω | (n : WithTop ℕ) < τ ω} := by
  have heq : (fun n : ℕ => P {ω | (n : WithTop ℕ) < τ ω}) =
      fun n : ℕ => (Real.toNNReal (P.real {ω | (n : WithTop ℕ) < τ ω}) : ℝ≥0∞) := by
    ext n
    change P {ω | (n : WithTop ℕ) < τ ω} = ENNReal.ofReal (P.real {ω | (n : WithTop ℕ) < τ ω})
    rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top P _)]
  have hlt_top : ∫⁻ ω, withTopToENNReal (τ ω) ∂P < ⊤ := by
    rw [lintegral_withTopToENNReal P hτ]
    rw [heq, ← ENNReal.coe_tsum hs.toNNReal]
    exact ENNReal.coe_lt_top
  have hmw : Measurable withTopToENNReal := fun s _ => (Set.to_countable _).measurableSet
  have hm_enn : AEMeasurable (fun ω => withTopToENNReal (τ ω)) P := (hmw.comp hτ).aemeasurable
  have hae_lt : ∀ᵐ ω ∂P, withTopToENNReal (τ ω) < ⊤ := ae_lt_top' hm_enn hlt_top.ne
  have hae_ne : ∀ᵐ ω ∂P, τ ω ≠ ⊤ := by
    filter_upwards [hae_lt] with ω hω htop
    rw [htop, withTopToENNReal_top] at hω
    exact lt_irrefl ⊤ hω
  have hmu : Measurable (fun x : WithTop ℕ => ((x.untopD 0 : ℕ) : ℝ)) :=
    fun s _ => (Set.to_countable _).measurableSet
  have hm_real : Measurable (fun ω => (((τ ω).untopD 0 : ℕ) : ℝ)) := hmu.comp hτ
  have hle_enn (ω : Ω) : ‖(((τ ω).untopD 0 : ℕ) : ℝ)‖ₑ ≤ withTopToENNReal (τ ω) := by
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    cases hω : τ ω with
    | top => simp
    | coe k =>
      rw [WithTop.untopD_coe]
      exact (ENNReal.ofReal_natCast k).le.trans_eq rfl
  have hint : Integrable (fun ω => (((τ ω).untopD 0 : ℕ) : ℝ)) P :=
    ⟨hm_real.aestronglyMeasurable, (lintegral_mono hle_enn).trans_lt hlt_top⟩
  have hpos_ae : (fun ω => ENNReal.ofReal (((τ ω).untopD 0 : ℕ) : ℝ)) =ᵐ[P]
      fun ω => withTopToENNReal (τ ω) := by
    filter_upwards [hae_ne] with ω hω
    cases hτw : τ ω with
    | top => exact absurd hτw hω
    | coe k =>
      rw [WithTop.untopD_coe]
      exact ENNReal.ofReal_natCast k
  have hint_eq : ∫ ω, (((τ ω).untopD 0 : ℕ) : ℝ) ∂P =
      ∑' n : ℕ, P.real {ω | (n : WithTop ℕ) < τ ω} := by
    rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hint]
    have hneg : ∫⁻ ω, ENNReal.ofReal (-(((τ ω).untopD 0 : ℕ) : ℝ)) ∂P = 0 := by
      have h0 : (fun ω => ENNReal.ofReal (-(((τ ω).untopD 0 : ℕ) : ℝ))) = 0 := by
        ext ω
        exact ENNReal.ofReal_of_nonpos (neg_nonpos.mpr (Nat.cast_nonneg _))
      rw [h0]
      exact lintegral_zero
    rw [hneg, ENNReal.toReal_zero, sub_zero, lintegral_congr_ae hpos_ae,
      lintegral_withTopToENNReal P hτ]
    rw [heq, ← ENNReal.coe_tsum hs.toNNReal, ENNReal.coe_toReal, NNReal.coe_tsum]
    exact tsum_congr fun n => Real.coe_toNNReal _ measureReal_nonneg
  exact ⟨hae_ne, hint, hint_eq⟩

end WithTopMean

section StoppingBounds

private theorem mean_le_of_real_lt_le_binomial {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {τ : Ω → WithTop ℕ} (hτ : Measurable τ) {r : ℕ} {p : I}
    (hp_pos : 0 < (p : ℝ))
    (htail : ∀ n : ℕ, P.real {ω | (n : WithTop ℕ) < τ ω} ≤
      (ProbabilityTheory.binomial n p).real (Set.Iio r)) :
    (∀ᵐ ω ∂P, τ ω ≠ ⊤) ∧
      Integrable (fun ω => (((τ ω).untopD 0 : ℕ) : ℝ)) P ∧
      ∫ ω, (((τ ω).untopD 0 : ℕ) : ℝ) ∂P ≤ (r : ℝ) / p := by
  have hs : Summable fun n : ℕ => P.real {ω | (n : WithTop ℕ) < τ ω} :=
    Summable.of_nonneg_of_le (fun _ => measureReal_nonneg) htail
      (summable_binomial_real_Iio r hp_pos)
  obtain ⟨hae, hint, hint_eq⟩ := integral_untopD_eq_tsum_real_lt P hτ hs
  refine ⟨hae, hint, ?_⟩
  rw [hint_eq]
  exact (hs.tsum_le_tsum htail (summable_binomial_real_Iio r hp_pos)).trans_eq
    (tsum_binomial_real_Iio r hp_pos)

private theorem real_lt_le_binomial_of_dom_replicate {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {A' : ℕ → Set Ω} {τ : Ω → WithTop ℕ} {r n : ℕ}
    {p : I} (hm : Measurable (adaptedCount A' (List.replicate n p).length))
    (hdom : StochasticallyDominates (P.map (adaptedCount A' (List.replicate n p).length))
      (PMF.poissonBinomial (List.replicate n p)).toMeasure)
    (hsub : {ω | (n : WithTop ℕ) < τ ω} ⊆ {ω | adaptedCount A' n ω < r}) :
    P.real {ω | (n : WithTop ℕ) < τ ω} ≤
      (ProbabilityTheory.binomial n p).real (Set.Iio r) := by
  have hle1 : P.real {ω | (n : WithTop ℕ) < τ ω} ≤ P.real {ω | adaptedCount A' n ω < r} :=
    measureReal_mono hsub
  have hle2 := hdom.le_real_Iio r
  have hmapL : (P.map (adaptedCount A' (List.replicate n p).length)).real (Set.Iio r) =
      P.real {ω | adaptedCount A' n ω < r} := by
    rw [measureReal_def, Measure.map_apply hm measurableSet_Iio, ← measureReal_def]
    simp only [List.length_replicate]
    rfl
  have hmapR : (PMF.poissonBinomial (List.replicate n p)).toMeasure.real (Set.Iio r) =
      (ProbabilityTheory.binomial n p).real (Set.Iio r) := by
    rw [PMF.toMeasure_poissonBinomial_replicate]
  rw [hmapL, hmapR] at hle2
  exact hle1.trans hle2

/-- **General stopping-time mean bound**: if `τ` is a stopping time for `ℱ` that triggers whenever
`adaptedCount A n ω ≥ r`, and `P[A t | ℱ t] ≥ p` (`p > 0`) a.e. on `{t < τ}`, then `τ < ∞` a.e.,
`((τ ·).untopD 0 : ℝ)` is integrable, and `𝔼[(τ ·).untopD 0] ≤ r / p`. -/
theorem stoppingTime_mean_le_of_adaptedCount_le {Ω : Type*} [m : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (ℱ : Filtration ℕ m) {A : ℕ → Set Ω}
    (hA : ∀ t, MeasurableSet[ℱ (t + 1)] (A t)) {r : ℕ} {p : I} (hp_pos : 0 < (p : ℝ))
    {τ : Ω → WithTop ℕ} (hτ : IsStoppingTime ℱ τ)
    (hle : ∀ n ω, r ≤ adaptedCount A n ω → τ ω ≤ (n : WithTop ℕ))
    (hp : ∀ t : ℕ, (fun _ => (p : ℝ)) ≤ᵐ[P.restrict {ω | (t : WithTop ℕ) < τ ω}]
      P[(A t).indicator (fun _ => (1 : ℝ)) | ℱ t]) :
    (∀ᵐ ω ∂P, τ ω ≠ ⊤) ∧
      Integrable (fun ω => (((τ ω).untopD 0 : ℕ) : ℝ)) P ∧
      ∫ ω, (((τ ω).untopD 0 : ℕ) : ℝ) ∂P ≤ (r : ℝ) / p := by
  let A' : ℕ → Set Ω := fun t => A t ∪ ({ω | (t : WithTop ℕ) < τ ω})ᶜ
  have hA' : ∀ t, MeasurableSet[ℱ (t + 1)] (A' t) := fun t =>
    (hA t).union (ℱ.mono t.le_succ _ (hτ.measurableSet_gt t).compl)
  have hp' : ∀ t : ℕ, (fun _ => (p : ℝ)) ≤ᵐ[P] P[(A' t).indicator (fun _ => (1 : ℝ)) | ℱ t] :=
    fun t => ae_le_condExp_union_compl ℱ (hA t) (hτ.measurableSet_gt t) (hp t)
  refine mean_le_of_real_lt_le_binomial P hτ.measurable' hp_pos
    fun n => ?_
  let ps := List.replicate n p
  have hdom := adaptedCount_stochasticallyDominates_poissonBinomial ℱ hA' ps fun t ht => by
    simpa [ps] using hp' t
  have hsub : {ω | (n : WithTop ℕ) < τ ω} ⊆ {ω | adaptedCount A' n ω < r} := by
    intro ω hω
    have hnot_le : ¬ τ ω ≤ (n : WithTop ℕ) := not_le.mpr hω
    have heq : adaptedCount A' n ω = adaptedCount A n ω := by
      refine Finset.sum_congr rfl fun t ht => ?_
      rw [Finset.mem_range] at ht
      have ht_lt : (t : WithTop ℕ) < τ ω :=
        lt_trans (WithTop.coe_lt_coe.mpr ht) hω
      by_cases hAt : ω ∈ A t <;> simp [A', hAt, ht_lt]
    change adaptedCount A' n ω < r
    rw [heq]
    exact not_le.mp fun hr => hnot_le (hle n ω hr)
  exact real_lt_le_binomial_of_dom_replicate
    ((measurable_adaptedCount ℱ hA' ps.length).mono (ℱ.le _) le_rfl) hdom hsub

/-- First time `n : ℕ` at which `adaptedCount A n ω ≥ r`. -/
@[expose]
noncomputable def countHittingTime {Ω : Type*} (A : ℕ → Set Ω) (r : ℕ) : Ω → WithTop ℕ :=
  hittingAfter (adaptedCount A) (Set.Ici r) 0

theorem isStoppingTime_countHittingTime {Ω : Type*} [m : MeasurableSpace Ω]
    (ℱ : Filtration ℕ m) {A : ℕ → Set Ω} (hA : ∀ t, MeasurableSet[ℱ (t + 1)] (A t))
    (r : ℕ) :
    IsStoppingTime ℱ (countHittingTime A r) :=
  (adapted_adaptedCount ℱ hA).isStoppingTime_hittingAfter measurableSet_Ici

theorem countHittingTime_le_iff {Ω : Type*} (A : ℕ → Set Ω) (r n : ℕ) (ω : Ω) :
    countHittingTime A r ω ≤ (n : WithTop ℕ) ↔ r ≤ adaptedCount A n ω := by
  rw [countHittingTime, show (n : WithTop ℕ) = WithTop.some n from by simp, hittingAfter_le_iff]
  refine ⟨fun ⟨j, hj, hjr⟩ => hjr.trans (adaptedCount_mono A ω hj.2), fun hr =>
    ⟨n, ⟨Nat.zero_le n, le_rfl⟩, hr⟩⟩

theorem lt_countHittingTime_iff {Ω : Type*} (A : ℕ → Set Ω) (r n : ℕ) (ω : Ω) :
    (n : WithTop ℕ) < countHittingTime A r ω ↔ adaptedCount A n ω < r := by
  rw [← not_le, countHittingTime_le_iff, not_le]

/-- **Mean hitting-time bound**: if `P[A t | ℱ t] ≥ p` (`p > 0`) a.e. on `{adaptedCount A t < r}`,
then `countHittingTime A r` is a.s. finite, integrable, and has expectation at most `r / p`. -/
theorem countHittingTime_mean_le {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ m) {A : ℕ → Set Ω}
    (hA : ∀ t, MeasurableSet[ℱ (t + 1)] (A t)) {r : ℕ} {p : I} (hp_pos : 0 < (p : ℝ))
    (hp : ∀ t : ℕ, (fun _ => (p : ℝ)) ≤ᵐ[P.restrict {ω | adaptedCount A t ω < r}]
      P[(A t).indicator (fun _ => (1 : ℝ)) | ℱ t]) :
    (∀ᵐ ω ∂P, countHittingTime A r ω ≠ ⊤) ∧
      Integrable (fun ω => (((countHittingTime A r ω).untopD 0 : ℕ) : ℝ)) P ∧
      ∫ ω, (((countHittingTime A r ω).untopD 0 : ℕ) : ℝ) ∂P ≤ (r : ℝ) / p := by
  refine stoppingTime_mean_le_of_adaptedCount_le ℱ hA hp_pos
    (isStoppingTime_countHittingTime ℱ hA r)
    (fun n ω hr => (countHittingTime_le_iff A r n ω).mpr hr) ?_
  intro t
  have hset : {ω | (t : WithTop ℕ) < countHittingTime A r ω} = {ω | adaptedCount A t ω < r} := by
    ext ω
    exact lt_countHittingTime_iff A r t ω
  rw [hset]
  exact hp t

end StoppingBounds

section KernelTrajStopping

/-- Infinite-horizon mean hitting-time bound under `ProbabilityTheory.Kernel.traj κ a x₀`. -/
theorem traj_countHittingTime_mean_le {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    (κ : (n : ℕ) → Kernel (Π i : Finset.Iic n, X i) (X (n + 1)))
    [∀ n, IsMarkovKernel (κ n)] {a : ℕ} (x₀ : Π i : Finset.Iic a, X i)
    {A : ℕ → Set (Π n, X n)}
    (hA : ∀ t, MeasurableSet[Filtration.piLE (a + t + 1)] (A t))
    {r : ℕ} {p : I} (hp_pos : 0 < (p : ℝ))
    (hp : ∀ t : ℕ, ∀ᵐ x ∂(Kernel.traj κ a x₀).restrict {x | adaptedCount A t x < r},
      (p : ℝ) ≤ (Kernel.traj κ (a + t) (Preorder.frestrictLe (a + t) x)).real (A t)) :
    (∀ᵐ x ∂Kernel.traj κ a x₀, countHittingTime A r x ≠ ⊤) ∧
      Integrable (fun x => (((countHittingTime A r x).untopD 0 : ℕ) : ℝ))
        (Kernel.traj κ a x₀) ∧
      ∫ x, (((countHittingTime A r x).untopD 0 : ℕ) : ℝ) ∂Kernel.traj κ a x₀ ≤ (r : ℝ) / p := by
  refine countHittingTime_mean_le (shiftFiltration Filtration.piLE a)
    (fun t => by
      change MeasurableSet[Filtration.piLE (a + (t + 1))] (A t)
      rw [← add_assoc]
      exact hA t)
    hp_pos ?_
  intro t
  have hce_rest := ae_restrict_of_ae (s := {x | adaptedCount A t x < r})
    (traj_condExp_indicator_eq κ (Nat.le_add_right a t) x₀
      (Filtration.piLE.le (a + t + 1) _ (hA t)))
  filter_upwards [hce_rest, hp t] with x hx hpx
  exact hpx.trans_eq hx.symm

/-- Infinite-horizon mean hitting-time bound under `ProbabilityTheory.Kernel.trajMeasure μ₀ κ`
for events `A t` measurable at step `t + 1`. -/
theorem trajMeasure_countHittingTime_mean_le {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    (μ₀ : Measure (X 0)) [IsProbabilityMeasure μ₀]
    (κ : (n : ℕ) → Kernel (Π i : Finset.Iic n, X i) (X (n + 1)))
    [∀ n, IsMarkovKernel (κ n)]
    {A : ℕ → Set (Π n, X n)} (hA : ∀ t, MeasurableSet[Filtration.piLE (t + 1)] (A t))
    {r : ℕ} {p : I} (hp_pos : 0 < (p : ℝ))
    (hp : ∀ t : ℕ, ∀ᵐ x ∂Kernel.trajMeasure μ₀ κ,
      adaptedCount A t x < r →
        (p : ℝ) ≤ (Kernel.traj κ t (Preorder.frestrictLe t x)).real (A t)) :
    (∀ᵐ x ∂Kernel.trajMeasure μ₀ κ, countHittingTime A r x ≠ ⊤) ∧
      Integrable (fun x => (((countHittingTime A r x).untopD 0 : ℕ) : ℝ))
        (Kernel.trajMeasure μ₀ κ) ∧
      ∫ x, (((countHittingTime A r x).untopD 0 : ℕ) : ℝ) ∂Kernel.trajMeasure μ₀ κ ≤
        (r : ℝ) / p := by
  let A' : ℕ → Set (Π n, X n) := fun t => A t ∪ {x | r ≤ adaptedCount A t x}
  have hA' : ∀ t, MeasurableSet[Filtration.piLE (t + 1)] (A' t) := fun t =>
    (hA t).union ((measurable_adaptedCount Filtration.piLE hA t).mono
      (Filtration.piLE.mono t.le_succ) le_rfl measurableSet_Ici)
  refine mean_le_of_real_lt_le_binomial (Kernel.trajMeasure μ₀ κ)
    (isStoppingTime_countHittingTime Filtration.piLE hA r).measurable'
    hp_pos fun n => ?_
  let ps := List.replicate n p
  have hp' : ∀ t (ht : t < ps.length), ∀ᵐ x ∂Kernel.trajMeasure μ₀ κ,
      (ps[t] : ℝ) ≤ (Kernel.traj κ t (Preorder.frestrictLe t x)).real (A' t) := by
    intro t ht
    filter_upwards [hp t] with x hx
    have hsub : A t ⊆ A' t := Set.subset_union_left
    by_cases hlt : adaptedCount A t x < r
    · calc
        (ps[t] : ℝ) = p := by simp [ps]
        _ ≤ (Kernel.traj κ t (Preorder.frestrictLe t x)).real (A t) := hx hlt
        _ ≤ (Kernel.traj κ t (Preorder.frestrictLe t x)).real (A' t) :=
            measureReal_mono hsub
    · have hge : r ≤ adaptedCount A t x := not_lt.mp hlt
      have hx_le : x ∈ {y | r ≤ adaptedCount A t y} := hge
      have htr : {y : Π n, X n | r ≤ adaptedCount A t y} ⊆ A' t := Set.subset_union_right
      have hfre :
          (Kernel.traj κ t (Preorder.frestrictLe t x)).real (A' t) = 1 := by
        have hprob :
            (Kernel.traj κ t (Preorder.frestrictLe t x)) (A' t) = 1 := by
          have hS : MeasurableSet[Filtration.piLE t] {y | r ≤ adaptedCount A t y} :=
            (measurable_adaptedCount Filtration.piLE hA t) measurableSet_Ici
          have hAe : ∀ᵐ y ∂Kernel.traj κ t (Preorder.frestrictLe t x),
              y ∈ {y | r ≤ adaptedCount A t y} := by
            rw [Filtration.piLE_eq_comap_frestrictLe] at hS
            rcases hS with ⟨B, hBm, hBeq⟩
            have hB_mem : Preorder.frestrictLe t x ∈ B := by
              change x ∈ Preorder.frestrictLe t ⁻¹' B
              rw [hBeq]
              exact hx_le
            have hdirac :
                ((Kernel.traj κ t (Preorder.frestrictLe t x)).map
                    (Preorder.frestrictLe t)) B = 1 := by
              rw [← Kernel.map_apply _ (Preorder.measurable_frestrictLe t),
                Kernel.traj_map_frestrictLe, Kernel.partialTraj_self, Kernel.id_apply,
                Measure.dirac_apply' _ hBm, Set.indicator_of_mem hB_mem, Pi.one_apply]
            rw [Measure.map_apply (Preorder.measurable_frestrictLe t) hBm] at hdirac
            have hpre : Preorder.frestrictLe t ⁻¹' B = adaptedCount A t ⁻¹' Set.Ici r := hBeq
            rw [hpre] at hdirac
            change (Kernel.traj κ t (Preorder.frestrictLe t x))
              (adaptedCount A t ⁻¹' Set.Ici r)ᶜ = 0
            rw [prob_compl_eq_one_sub (Filtration.piLE.le t _
              ((measurable_adaptedCount Filtration.piLE hA t) measurableSet_Ici)),
              hdirac, tsub_self]
          have hcompl : (Kernel.traj κ t (Preorder.frestrictLe t x)) (A' t)ᶜ = 0 :=
            measure_mono_null (Set.compl_subset_compl.mpr htr) hAe
          rw [← compl_compl (A' t),
            prob_compl_eq_one_sub (Filtration.piLE.le (t + 1) _ (hA' t)).compl, hcompl,
            tsub_zero]
        simp [measureReal_def, hprob]
      simpa [ps, hfre] using p.2.2
  have hdom := trajMeasure_adaptedCount_stochasticallyDominates_poissonBinomial μ₀ κ hA' ps hp'
  have hsub : {x | (n : WithTop ℕ) < countHittingTime A r x} ⊆
      {x | adaptedCount A' n x < r} := by
    intro x hx
    change (n : WithTop ℕ) < countHittingTime A r x at hx
    rw [lt_countHittingTime_iff] at hx
    have heq : adaptedCount A' n x = adaptedCount A n x :=
      adaptedCount_congr_of_lt hx fun t _ ht => by simp [A', not_le.mpr ht]
    change adaptedCount A' n x < r
    rwa [heq]
  exact real_lt_le_binomial_of_dom_replicate
    ((measurable_adaptedCount Filtration.piLE hA' ps.length).mono (Filtration.piLE.le _)
      le_rfl)
    hdom hsub

end KernelTrajStopping

end Cslib.Probability
