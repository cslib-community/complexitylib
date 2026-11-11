/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Probability.Cauchy
public import CslibFrontier.Foundations.Probability.Gaussian.Multivariate
public import CslibFrontier.Probability.LocalitySensitiveHash.Measure
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Probability.ConditionalProbability
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Locality-sensitive hashing from `p`-stable distributions

Datar, Immorlica, Indyk, and Mirrokni ([DatarImmorlicaIndykMirrokni2004]) construct
locality-sensitive hash families for `\ell_p` distances (`p ∈ (0, 2]`) by projecting onto a
vector `a` with i.i.d. `p`-stable coordinates, shifting by `b ~ Uniform[0, r)`, and quantizing
into buckets of width `r`: `h_{a,b}(v) = ⌊(⟨a, v⟩ + b) / r⌋`.

Conditioned on `a`, two real projections `x, y` collide under `b ~ Uniform[0, r)` with
probability `max 0 (1 - |x - y| / r)` (`measureReal_uniformInterval_floor_eq`). Integrating over
the random projection gives `stableCollisionProb μ r c = ∫ z, max 0 (1 - c * |z| / r) ∂μ`
when `⟨a, u - v⟩` has the law of `c * Z` for `Z ~ μ`
(`measureCollisionProb_intervalFloorHash_of_map`).

Specializing to the two standard stable laws:

* **`p = 2` (Gaussian / Euclidean norm):** under `a ~ stdGaussian E` (`p2StableHash`),
  `Pr[p2StableHash r (a, b) u = p2StableHash r (a, b) v] = p2StableProb r ‖u - v‖`
  (`measureCollisionProb_p2StableHash`), matching the integral of
  [DatarImmorlicaIndykMirrokni2004] (`p2StableProb_eq_integral`) and evaluating explicitly in terms
  of `(gaussianReal 0 1).real (Icc (-r / c) (r / c))` and `exp` (`p2StableProb_eq_sub`).
* **`p = 1` (Cauchy / `\ell_1` norm):** under i.i.d. Cauchy coordinates `a_i ~ cauchyMeasure 0 1`
  (`p1StableHash`), 1-stability (`ProbabilityTheory.pi_cauchyMeasure_map_dotProduct`) yields
  `Pr[p1StableHash r (a, b) u = p1StableHash r (a, b) v] = p1StableProb r (∑ i, |u i - v i|)`
  (`measureCollisionProb_p1StableHash`), with closed form
  `(2 / π) arctan (r / c) - (c / (π r)) log (1 + (r / c) ^ 2)` (`p1StableProb_eq`).

For both families, the collision probability is strictly positive and strictly decreasing in the
distance `c ≥ 0`, giving `(d₁, d₂)` sensitivity (`isLocalitySensitive_p2StableHash`,
`isLocalitySensitive_p1StableHash`).

## Main definitions

* `Cslib.Probability.uniformInterval`: Lebesgue measure conditioned on `Set.Ico 0 r`.
* `Cslib.Probability.intervalFloorHash`: quantized bucket hash `⌊(proj a x + b) / r⌋`.
* `Cslib.Probability.stableCollisionProb`: `∫ z, max 0 (1 - c * |z| / r) ∂μ`.
* `Cslib.Probability.p2StableHash`, `Cslib.Probability.p2StableProb`: Gaussian `p = 2` family.
* `Cslib.Probability.p1StableHash`, `Cslib.Probability.p1StableProb`: Cauchy `p = 1` family.

## Main results

* `Cslib.Probability.measureReal_uniformInterval_floor_eq`: exact interval collision probability
  `max 0 (1 - |x - y| / r)`.
* `Cslib.Probability.measureCollisionProb_intervalFloorHash`: general Fubini bucket collision law.
* `Cslib.Probability.measureCollisionProb_p2StableHash`,
  `Cslib.Probability.p2StableProb_eq_integral`, `Cslib.Probability.p2StableProb_eq_sub`,
  `Cslib.Probability.p2StableProb_strictAnti`, `Cslib.Probability.isLocalitySensitive_p2StableHash`:
  Gaussian `p = 2` collision law, formulas, strict monotonicity, and LSH sensitivity.
* `Cslib.Probability.measureCollisionProb_p1StableHash`,
  `Cslib.Probability.p1StableProb_eq`, `Cslib.Probability.p1StableProb_strictAnti`,
  `Cslib.Probability.isLocalitySensitive_p1StableHash`: Cauchy `p = 1` collision law, closed form,
  strict monotonicity, and LSH sensitivity.

## References

* [M. Datar, N. Immorlica, P. Indyk, V. S. Mirrokni, *Locality-sensitive hashing scheme based on
  p-stable distributions*][DatarImmorlicaIndykMirrokni2004]
-/

public section

namespace Cslib.Probability

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal RealInnerProductSpace

/-! ### Uniform shift on `[0, r)` and quantized bucket collisions -/

/-- The uniform probability measure on `[0, r)`, defined by conditioning Lebesgue measure on
`Set.Ico 0 r`. -/
@[expose] noncomputable def uniformInterval (r : ℝ) : Measure ℝ :=
  (volume : Measure ℝ)[|Set.Ico 0 r]

/-- For `r > 0`, `uniformInterval r` is a probability measure. -/
theorem isProbabilityMeasure_uniformInterval {r : ℝ} (hr : 0 < r) :
    IsProbabilityMeasure (uniformInterval r) :=
  cond_isProbabilityMeasure_of_finite (by simp [Real.volume_Ico, hr])
    (by simp [Real.volume_Ico])

/-- Application of `uniformInterval r` to a set `s`. -/
theorem uniformInterval_real_apply {r : ℝ} (hr : 0 < r) (s : Set ℝ) :
    (uniformInterval r).real s = r⁻¹ * volume.real (Set.Ico 0 r ∩ s) := by
  rw [uniformInterval, measureReal_def, cond_apply measurableSet_Ico, Real.volume_Ico, sub_zero,
    ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal hr.le, ← measureReal_def]

/-- Bucket hash obtained by projecting `x` via `proj a x`, adding shift `b`, and taking the
integer floor of the quotient by `r`. -/
@[expose] noncomputable def intervalFloorHash {α X : Type*} (r : ℝ) (proj : α → X → ℝ)
    (seed : α × ℝ) (x : X) : ℤ :=
  ⌊(proj seed.1 x + seed.2) / r⌋

/-- The collision set of `intervalFloorHash` is measurable whenever `proj · x` is measurable. -/
theorem measurableSet_intervalFloorHash_eq {α X : Type*} [MeasurableSpace α] (r : ℝ)
    {proj : α → X → ℝ} (hproj : ∀ x, Measurable (fun a => proj a x)) (u v : X) :
    MeasurableSet {p : α × ℝ | intervalFloorHash r proj p u = intervalFloorHash r proj p v} := by
  have hm : ∀ x, Measurable (fun p : α × ℝ => intervalFloorHash r proj p x) := fun x =>
    Int.measurable_floor.comp ((((hproj x).comp measurable_fst).add measurable_snd).div_const r)
  have heq : {p : α × ℝ | intervalFloorHash r proj p u = intervalFloorHash r proj p v} =
      (fun p : α × ℝ => intervalFloorHash r proj p u - intervalFloorHash r proj p v) ⁻¹' {0} := by
    ext p
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq, sub_eq_zero]
  rw [heq]
  exact ((hm u).sub (hm v)) (measurableSet_singleton (0 : ℤ))

/-- Helper: `volume.real (Ico 0 r ∩ S)` equals the interval integral of `S.indicator 1` on `0..r`
when `S` is measurable and `0 ≤ r`. -/
private theorem volume_real_Ico_inter_eq_intervalIntegral {r : ℝ} (hr : 0 ≤ r) {S : Set ℝ}
    (hS : MeasurableSet S) :
    volume.real (Set.Ico 0 r ∩ S) = ∫ b in (0 : ℝ)..r, S.indicator (fun _ => (1 : ℝ)) b := by
  have hcongr : volume (Set.Ico 0 r ∩ S) = volume (Set.Ioc 0 r ∩ S) :=
    measure_congr (Ico_ae_eq_Ioc.inter Filter.EventuallyEq.rfl)
  rw [measureReal_def, hcongr, ← measureReal_def, intervalIntegral.integral_of_le hr,
    setIntegral_indicator hS, setIntegral_const, smul_eq_mul, mul_one, Set.inter_comm]

/-- Indicator of a measurable set is interval integrable on `[0, 1]`. -/
private theorem intervalIntegrable_indicator_one {S : Set ℝ} (hS : MeasurableSet S) :
    IntervalIntegrable (fun t : ℝ => S.indicator (fun _ => (1 : ℝ)) t) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  refine IntegrableOn.of_bound (by simp [Real.volume_Ioc])
    ((measurable_one.indicator hS).aestronglyMeasurable) 1 (ae_of_all _ fun t => ?_)
  rw [Real.norm_of_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) t)]
  exact Set.indicator_le' (fun _ _ => le_rfl) (fun _ _ => zero_le_one) t

/-- `Int.fract` is interval integrable on `[0, 1]`. -/
private theorem intervalIntegrable_fract_add (u : ℝ) :
    IntervalIntegrable (fun b : ℝ => Int.fract (u + b)) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  refine IntegrableOn.of_bound (by simp [Real.volume_Ioc])
    ((measurable_fract.comp (measurable_const.add measurable_id)).aestronglyMeasurable) 1
    (ae_of_all _ fun b => ?_)
  rw [Real.norm_of_nonneg (Int.fract_nonneg _)]
  exact (Int.fract_lt_one _).le

/-- Lebesgue measure of `{b ∈ [0, 1) | ⌊x + b⌋ ≠ ⌊y + b⌋}` when `0 ≤ y - x ≤ 1`. -/
private theorem volume_Ico_floor_ne_of_le {x y : ℝ} (hxy : x ≤ y) (hgap : y - x ≤ 1) :
    volume.real (Set.Ico 0 1 ∩ {b : ℝ | ⌊x + b⌋ ≠ ⌊y + b⌋}) = y - x := by
  have hind : ∀ b : ℝ,
      {b : ℝ | ⌊x + b⌋ ≠ ⌊y + b⌋}.indicator (fun _ => (1 : ℝ)) b =
        (⌊y + b⌋ : ℝ) - ⌊x + b⌋ := fun b => by
    have hle : ⌊x + b⌋ ≤ ⌊y + b⌋ := Int.floor_mono (by linarith)
    have hlt : ⌊y + b⌋ ≤ ⌊x + b⌋ + 1 := by
      rw [← Int.floor_add_one]
      exact Int.floor_mono (by linarith)
    rw [Set.indicator_apply]
    split_ifs with h
    · have hne : ⌊x + b⌋ ≠ ⌊y + b⌋ := h
      have hlt' : ⌊x + b⌋ < ⌊y + b⌋ := lt_of_le_of_ne hle hne
      have : ⌊y + b⌋ = ⌊x + b⌋ + 1 := by omega
      simp [this]
    · have hne : ¬⌊x + b⌋ ≠ ⌊y + b⌋ := h
      have : ⌊y + b⌋ = ⌊x + b⌋ := (not_ne_iff.1 hne).symm
      simp [this]
  have hmeas : MeasurableSet {b : ℝ | ⌊x + b⌋ ≠ ⌊y + b⌋} := by
    have heq : {b : ℝ | ⌊x + b⌋ ≠ ⌊y + b⌋} =
        ((fun b => ⌊x + b⌋ - ⌊y + b⌋) ⁻¹' {0})ᶜ := by
      ext b; simp [sub_eq_zero]
    rw [heq]
    exact (((Int.measurable_floor.comp (measurable_const.add measurable_id)).sub
      (Int.measurable_floor.comp (measurable_const.add measurable_id)))
        (measurableSet_singleton (0 : ℤ))).compl
  have hdiff : ∀ b : ℝ, (⌊y + b⌋ : ℝ) - ⌊x + b⌋ =
      (y - x) + Int.fract (x + b) - Int.fract (y + b) := fun b => by
    simp only [Int.fract]
    ring
  have hper : Function.Periodic (Int.fract : ℝ → ℝ) 1 := fun z => by
    simpa only [add_comm] using Int.fract_add_one z
  have hf_eq (u : ℝ) : ∫ b in (0 : ℝ)..1, Int.fract (u + b) = ∫ b in (0 : ℝ)..1, Int.fract b := by
    have h1 := intervalIntegral.integral_comp_add_left (Int.fract : ℝ → ℝ) u (a := 0) (b := 1)
    simp only [add_zero] at h1
    rw [h1, hper.intervalIntegral_add_eq u 0, zero_add]
  have hix := intervalIntegrable_fract_add x
  have hiy := intervalIntegrable_fract_add y
  have hic : IntervalIntegrable (fun _ : ℝ => y - x) volume 0 1 := intervalIntegrable_const
  rw [volume_real_Ico_inter_eq_intervalIntegral zero_le_one hmeas]
  simp only [hind, hdiff]
  rw [intervalIntegral.integral_sub (hic.add hix) hiy,
    intervalIntegral.integral_add hic hix, intervalIntegral.integral_const, sub_zero,
    smul_eq_mul, one_mul, hf_eq x, hf_eq y, add_sub_cancel_right]

/-- Measure of `{b ∈ [0, r) | ⌊(x + b) / r⌋ = ⌊(y + b) / r⌋}` under `uniformInterval r`. -/
theorem measureReal_uniformInterval_floor_eq {r : ℝ} (hr : 0 < r) (x y : ℝ) :
    (uniformInterval r).real {b : ℝ | ⌊(x + b) / r⌋ = ⌊(y + b) / r⌋} =
      max 0 (1 - |x - y| / r) := by
  wlog hxy : x ≤ y generalizing x y
  · simpa only [eq_comm, abs_sub_comm] using this y x (le_of_not_ge hxy)
  have hm : ∀ z : ℝ, Measurable (fun b : ℝ => ⌊(z + b) / r⌋) := fun z =>
    Int.measurable_floor.comp ((measurable_const.add measurable_id).div_const r)
  have hmeas : MeasurableSet {b : ℝ | ⌊(x + b) / r⌋ = ⌊(y + b) / r⌋} := by
    have heq : {b : ℝ | ⌊(x + b) / r⌋ = ⌊(y + b) / r⌋} =
        (fun b : ℝ => ⌊(x + b) / r⌋ - ⌊(y + b) / r⌋) ⁻¹' {0} := by
      ext b; simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq, sub_eq_zero]
    rw [heq]
    exact ((hm x).sub (hm y)) (measurableSet_singleton (0 : ℤ))
  have habs : |x - y| = y - x := abs_sub_comm x y ▸ abs_of_nonneg (sub_nonneg.2 hxy)
  rcases le_or_gt r (y - x) with hfar | hnear
  · have hemp : {b : ℝ | ⌊(x + b) / r⌋ = ⌊(y + b) / r⌋} = ∅ := by
      ext b
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      have h1 : (x + b) / r + 1 ≤ (y + b) / r := by
        rw [div_add_one hr.ne', div_le_div_iff_of_pos_right hr]
        linarith
      have h2 : ⌊(x + b) / r⌋ + 1 ≤ ⌊(y + b) / r⌋ := by
        rw [← Int.floor_add_one]
        exact Int.floor_mono h1
      omega
    rw [hemp, measureReal_empty, eq_comm, max_eq_left]
    rw [habs, sub_nonpos, le_div_iff₀ hr, one_mul]
    exact hfar
  · have hscale : volume.real (Set.Ico 0 r ∩ {b : ℝ | ⌊(x + b) / r⌋ = ⌊(y + b) / r⌋}) =
        r - (y - x) := by
      have hcomp := intervalIntegral.integral_comp_mul_left
        (fun b : ℝ => {b : ℝ | ⌊(x + b) / r⌋ = ⌊(y + b) / r⌋}.indicator (fun _ => (1 : ℝ)) b)
        (a := 0) (b := 1) hr.ne'
      simp only [mul_zero, mul_one, smul_eq_mul] at hcomp
      have hind_sc : (fun t : ℝ =>
            {b : ℝ | ⌊(x + b) / r⌋ = ⌊(y + b) / r⌋}.indicator (fun _ => (1 : ℝ)) (r * t)) =
          fun t => {t : ℝ | ⌊x / r + t⌋ = ⌊y / r + t⌋}.indicator (fun _ => (1 : ℝ)) t := by
        funext t
        have harg (z : ℝ) : (z + r * t) / r = z / r + t := by field_simp [hr.ne']
        simp only [Set.indicator_apply, Set.mem_ofPred_eq, harg]
      have hcompl : ∀ t : ℝ,
          {t : ℝ | ⌊x / r + t⌋ = ⌊y / r + t⌋}.indicator (fun _ => (1 : ℝ)) t =
            1 - {t : ℝ | ⌊x / r + t⌋ ≠ ⌊y / r + t⌋}.indicator (fun _ => (1 : ℝ)) t := fun t => by
        by_cases ht : ⌊x / r + t⌋ = ⌊y / r + t⌋
        · simp [ht]
        · simp [ht]
      have hm1 : MeasurableSet {t : ℝ | ⌊x / r + t⌋ ≠ ⌊y / r + t⌋} := by
        have heq : {t : ℝ | ⌊x / r + t⌋ ≠ ⌊y / r + t⌋} =
            ((fun t => ⌊x / r + t⌋ - ⌊y / r + t⌋) ⁻¹' {0})ᶜ := by
          ext t; simp [sub_eq_zero]
        rw [heq]
        exact (((Int.measurable_floor.comp (measurable_const.add measurable_id)).sub
          (Int.measurable_floor.comp (measurable_const.add measurable_id)))
            (measurableSet_singleton (0 : ℤ))).compl
      have hne_vol := volume_Ico_floor_ne_of_le (div_le_div_of_nonneg_right hxy hr.le)
        (by rw [← sub_div, div_le_one hr]; exact hnear.le)
      have hne_int : ∫ t in (0 : ℝ)..1,
          {t : ℝ | ⌊x / r + t⌋ ≠ ⌊y / r + t⌋}.indicator (fun _ => (1 : ℝ)) t = (y - x) / r := by
        rw [← volume_real_Ico_inter_eq_intervalIntegral zero_le_one hm1, hne_vol, sub_div]
      have hi1 : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 1 := intervalIntegrable_const
      have hi2 := intervalIntegrable_indicator_one hm1
      have hr_int : ∫ b in (0 : ℝ)..r,
          {b : ℝ | ⌊(x + b) / r⌋ = ⌊(y + b) / r⌋}.indicator (fun _ => (1 : ℝ)) b =
          r * ∫ t in (0 : ℝ)..1,
            {b : ℝ | ⌊(x + b) / r⌋ = ⌊(y + b) / r⌋}.indicator (fun _ => (1 : ℝ)) (r * t) := by
        rw [hcomp, ← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul]
      rw [volume_real_Ico_inter_eq_intervalIntegral hr.le hmeas, hr_int]
      simp_rw [hind_sc, hcompl]
      rw [intervalIntegral.integral_sub hi1 hi2, intervalIntegral.integral_const, sub_zero,
        smul_eq_mul, mul_one, hne_int]
      field_simp [hr.ne']
    rw [uniformInterval_real_apply hr _, hscale, habs, eq_comm, max_eq_right]
    · field_simp [hr.ne']
    · rw [sub_nonneg, div_le_one hr]
      exact hnear.le

/-- **General Fubini collision formula for `intervalFloorHash`**: under any probability measure
`μ` on the projection space paired with `uniformInterval r`, `u` and `v` collide with probability
`∫ a, max 0 (1 - |proj a u - proj a v| / r) ∂μ`. -/
theorem measureCollisionProb_intervalFloorHash {α X : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < r) (proj : α → X → ℝ)
    (hproj : ∀ x, Measurable (fun a => proj a x)) (u v : X) :
    measureCollisionProb (μ.prod (uniformInterval r)) (intervalFloorHash r proj) u v =
      ∫ a, max (0 : ℝ) (1 - |proj a u - proj a v| / r) ∂μ := by
  have : IsProbabilityMeasure (uniformInterval r) := isProbabilityMeasure_uniformInterval hr
  have hmeas := measurableSet_intervalFloorHash_eq r hproj u v
  have hprod : (μ.prod (uniformInterval r))
      {p : α × ℝ | intervalFloorHash r proj p u = intervalFloorHash r proj p v} =
      ∫⁻ a, ENNReal.ofReal (max (0 : ℝ) (1 - |proj a u - proj a v| / r)) ∂μ := by
    rw [Measure.prod_apply hmeas]
    refine lintegral_congr fun a => ?_
    have hsect : Prod.mk a ⁻¹'
        {p : α × ℝ | intervalFloorHash r proj p u = intervalFloorHash r proj p v} =
        {b : ℝ | ⌊(proj a u + b) / r⌋ = ⌊(proj a v + b) / r⌋} := rfl
    rw [hsect, ← ENNReal.ofReal_toReal (measure_ne_top (uniformInterval r) _),
      ← measureReal_def, measureReal_uniformInterval_floor_eq hr]
  have hf_meas : Continuous fun t : ℝ => max (0 : ℝ) (1 - |t| / r) :=
    continuous_const.max (continuous_const.sub (continuous_abs.div_const r))
  have hf_int : Integrable (fun a => max (0 : ℝ) (1 - |proj a u - proj a v| / r)) μ := by
    refine Integrable.of_bound
      ((hf_meas.measurable.comp ((hproj u).sub (hproj v))).aestronglyMeasurable) 1
      (ae_of_all _ fun a => ?_)
    rw [Real.norm_of_nonneg (le_max_left _ _)]
    exact max_le zero_le_one (sub_le_self 1 (div_nonneg (abs_nonneg _) hr.le))
  rw [measureCollisionProb, measureReal_def, hprod,
    ← ofReal_integral_eq_lintegral_ofReal hf_int (ae_of_all _ fun a => le_max_left _ _),
    ENNReal.toReal_ofReal (integral_nonneg fun a => le_max_left (0 : ℝ) _)]

/-! ### Abstract collision integral and symmetric-density properties -/

/-- The expected collision probability `∫ z, max 0 (1 - c * |z| / r) ∂μ` for a scalar `1`-D
distribution `μ` at distance `c` and bucket width `r`. -/
@[expose] noncomputable def stableCollisionProb (μ : Measure ℝ) (r c : ℝ) : ℝ :=
  ∫ z : ℝ, max (0 : ℝ) (1 - c * |z| / r) ∂μ

/-- Reduction of `measureCollisionProb_intervalFloorHash` when `proj a u - proj a v` is the
law of `c * Z` under `ν`. -/
theorem measureCollisionProb_intervalFloorHash_of_map {α X : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (ν : Measure ℝ) {r : ℝ} (hr : 0 < r)
    (proj : α → X → ℝ) (hproj : ∀ x, Measurable (fun a => proj a x)) (u v : X) {c : ℝ}
    (hc : 0 ≤ c) (hmap : μ.map (fun a => proj a u - proj a v) = ν.map (c * ·)) :
    measureCollisionProb (μ.prod (uniformInterval r)) (intervalFloorHash r proj) u v =
      stableCollisionProb ν r c := by
  rw [measureCollisionProb_intervalFloorHash μ hr proj hproj u v]
  have hcont : Continuous fun y : ℝ => max (0 : ℝ) (1 - |y| / r) :=
    continuous_const.max (continuous_const.sub (continuous_abs.div_const r))
  have h1 : ∫ a, max (0 : ℝ) (1 - |proj a u - proj a v| / r) ∂μ =
      ∫ y, max (0 : ℝ) (1 - |y| / r) ∂(μ.map fun a => proj a u - proj a v) :=
    (integral_map ((hproj u).sub (hproj v)).aemeasurable hcont.aestronglyMeasurable).symm
  have h2 : ∫ y, max (0 : ℝ) (1 - |y| / r) ∂(ν.map (c * ·)) =
      ∫ z, max (0 : ℝ) (1 - |c * z| / r) ∂ν :=
    integral_map (measurable_const.mul measurable_id).aemeasurable hcont.aestronglyMeasurable
  rw [h1, hmap, h2]
  simp only [abs_mul, abs_of_nonneg hc, stableCollisionProb]

/-- Integrability of `z ↦ f z * max 0 (1 - c * |z| / r)` when `f ≥ 0` is integrable,
continuous, `r > 0`, and `c ≥ 0`. -/
private theorem integrable_mul_stableKernel' {f : ℝ → ℝ} (hf_cont : Continuous f)
    (hf_nonneg : ∀ z, 0 ≤ f z) (hf_int : Integrable f) {r c : ℝ} (hr : 0 < r) (hc : 0 ≤ c) :
    Integrable (fun z : ℝ => f z * max (0 : ℝ) (1 - c * |z| / r)) := by
  have hm : Continuous fun z : ℝ => f z * max (0 : ℝ) (1 - c * |z| / r) :=
    hf_cont.mul (continuous_const.max
      (continuous_const.sub ((continuous_const.mul continuous_abs).div_const r)))
  refine Integrable.mono' hf_int hm.aestronglyMeasurable (ae_of_all _ fun z => ?_)
  rw [Real.norm_of_nonneg (mul_nonneg (hf_nonneg z) (le_max_left _ _))]
  exact mul_le_of_le_one_right (hf_nonneg z)
    (max_le zero_le_one (sub_le_self 1 (div_nonneg (mul_nonneg hc (abs_nonneg z)) hr.le)))

theorem stableCollisionProb_zero (μ : Measure ℝ) [IsProbabilityMeasure μ] (r : ℝ) :
    stableCollisionProb μ r 0 = 1 := by
  simp [stableCollisionProb]

theorem stableCollisionProb_nonneg (μ : Measure ℝ) (r c : ℝ) :
    0 ≤ stableCollisionProb μ r c :=
  integral_nonneg fun _ => le_max_left _ _

private theorem integrable_stableKernel (μ : Measure ℝ) [IsFiniteMeasure μ]
    {r c : ℝ} (hr : 0 < r) (hc : 0 ≤ c) :
    Integrable (fun z : ℝ => max (0 : ℝ) (1 - c * |z| / r)) μ := by
  have hcont : Continuous fun z : ℝ => max (0 : ℝ) (1 - c * |z| / r) :=
    continuous_const.max
      (continuous_const.sub ((continuous_const.mul continuous_abs).div_const r))
  refine Integrable.of_bound hcont.aestronglyMeasurable 1 (ae_of_all _ fun z => ?_)
  rw [Real.norm_of_nonneg (le_max_left _ _)]
  exact max_le zero_le_one (sub_le_self 1 (div_nonneg (mul_nonneg hc (abs_nonneg z)) hr.le))

private theorem mul_abs_div_le_half {r c z : ℝ} (hr : 0 < r) (hc : 0 ≤ c) (hz0 : 0 ≤ z)
    (hz : z ≤ r / (2 * (c + 1))) : c * |z| / r ≤ 1 / 2 := by
  rw [abs_of_nonneg hz0, div_le_iff₀ hr]
  calc c * z ≤ c * (r / (2 * (c + 1))) := mul_le_mul_of_nonneg_left hz hc
    _ = (c / (c + 1)) * ((1 / 2) * r) := by
        have : c + 1 ≠ 0 := by positivity
        field_simp
    _ ≤ 1 * ((1 / 2) * r) := by
        gcongr
        exact (div_le_one (by positivity)).2 (by linarith)
    _ = 1 / 2 * r := one_mul _

theorem stableCollisionProb_le_one (μ : Measure ℝ) [IsProbabilityMeasure μ] {r c : ℝ}
    (hr : 0 < r) (hc : 0 ≤ c) : stableCollisionProb μ r c ≤ 1 := by
  have h := integral_mono (integrable_stableKernel μ hr hc) (integrable_const (1 : ℝ)) fun z =>
    max_le zero_le_one (sub_le_self 1 (div_nonneg (mul_nonneg hc (abs_nonneg z)) hr.le))
  rw [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul,
    mul_one] at h
  exact h

theorem stableCollisionProb_anti (μ : Measure ℝ) [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < r)
    {c₁ c₂ : ℝ} (hc₁ : 0 ≤ c₁) (hle : c₁ ≤ c₂) :
    stableCollisionProb μ r c₂ ≤ stableCollisionProb μ r c₁ := by
  refine integral_mono (integrable_stableKernel μ hr (hc₁.trans hle))
    (integrable_stableKernel μ hr hc₁) fun z => max_le_max le_rfl ?_
  gcongr

/-- An integrable nonnegative function bounded away from zero on `[a, b]` (`a < b`) has strictly
positive integral on `ℝ`. -/
private theorem pos_integral_of_bound_Icc {g : ℝ → ℝ} (hg_int : Integrable g)
    (hg_nonneg : ∀ z, 0 ≤ g z) {a b m : ℝ} (hab : a < b) (hm : 0 < m)
    (hmin : ∀ z ∈ Set.Icc a b, m ≤ g z) : 0 < ∫ z : ℝ, g z := by
  have hsub : (b - a) * m ≤ ∫ z in Set.Ioc a b, g z := by
    have hconst : ∫ _ in Set.Ioc a b, m = (b - a) * m := by
      rw [setIntegral_const, Real.volume_real_Ioc, smul_eq_mul, max_eq_left (sub_nonneg.2 hab.le)]
    rw [← hconst]
    exact setIntegral_mono_on (integrableOn_const (hs := by simp [Real.volume_Ioc]))
      hg_int.integrableOn measurableSet_Ioc fun z hz => hmin z ⟨hz.1.le, hz.2⟩
  have hle : ∫ z in Set.Ioc a b, g z ≤ ∫ z : ℝ, g z :=
    setIntegral_le_integral hg_int (ae_of_all _ hg_nonneg)
  exact lt_of_lt_of_le (mul_pos (sub_pos.2 hab) hm) (hsub.trans hle)

/-- `stableCollisionProb` against a strictly positive continuous integrable density `f` is
strictly positive. -/
private theorem stableCollisionProb_withDensity_pos {f : ℝ → ℝ}
    (hf_cont : Continuous f) (hf_pos : ∀ z, 0 < f z) (hf_int : Integrable f)
    {r c : ℝ} (hr : 0 < r) (hc : 0 ≤ c) :
    0 < stableCollisionProb (volume.withDensity fun z => ENNReal.ofReal (f z)) r c := by
  have hm : Measurable (fun z => ENNReal.ofReal (f z)) := by fun_prop
  rw [stableCollisionProb, integral_withDensity_eq_integral_toReal_smul hm
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (hf_pos _).le, smul_eq_mul]
  set δ : ℝ := r / (2 * (c + 1))
  have hδ : 0 < δ := by positivity
  obtain ⟨z₀, -, hz₀⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := δ)).exists_isMinOn
    ⟨0, left_mem_Icc.2 hδ.le⟩ hf_cont.continuousOn
  have hg_int := integrable_mul_stableKernel' hf_cont (fun z => (hf_pos z).le) hf_int hr hc
  refine pos_integral_of_bound_Icc hg_int (fun z => mul_nonneg (hf_pos z).le (le_max_left _ _))
    hδ (mul_pos (hf_pos z₀) (by norm_num : (0 : ℝ) < 1 / 2)) fun z hz => ?_
  have hcδ : c * |z| / r ≤ 1 / 2 := mul_abs_div_le_half hr hc hz.1 hz.2
  exact mul_le_mul (hz₀ hz) (le_max_of_le_right (by linarith)) (by norm_num) (hf_pos z).le

/-- `stableCollisionProb` against a strictly positive continuous integrable density `f` is
strictly decreasing in `c ≥ 0`. -/
private theorem stableCollisionProb_withDensity_strictAnti {f : ℝ → ℝ}
    (hf_cont : Continuous f) (hf_pos : ∀ z, 0 < f z) (hf_int : Integrable f)
    {r c₁ c₂ : ℝ} (hr : 0 < r) (hc₁ : 0 ≤ c₁) (hlt : c₁ < c₂) :
    stableCollisionProb (volume.withDensity fun z => ENNReal.ofReal (f z)) r c₂ <
      stableCollisionProb (volume.withDensity fun z => ENNReal.ofReal (f z)) r c₁ := by
  have hc₂ : 0 ≤ c₂ := hc₁.trans hlt.le
  have hdiff_c : 0 < c₂ - c₁ := sub_pos.2 hlt
  have hm : Measurable (fun z => ENNReal.ofReal (f z)) := by fun_prop
  rw [stableCollisionProb, stableCollisionProb,
    integral_withDensity_eq_integral_toReal_smul hm (ae_of_all _ fun _ => ENNReal.ofReal_lt_top),
    integral_withDensity_eq_integral_toReal_smul hm (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (hf_pos _).le, smul_eq_mul]
  have hi1 := integrable_mul_stableKernel' hf_cont (fun z => (hf_pos z).le) hf_int hr hc₁
  have hi2 := integrable_mul_stableKernel' hf_cont (fun z => (hf_pos z).le) hf_int hr hc₂
  rw [← sub_pos, ← integral_sub hi1 hi2]
  set δ : ℝ := r / (2 * (c₂ + 1))
  have hδ : 0 < δ := by positivity
  obtain ⟨z₀, -, hz₀⟩ := (isCompact_Icc (a := δ / 2) (b := δ)).exists_isMinOn
    ⟨δ / 2, left_mem_Icc.2 (by linarith)⟩ hf_cont.continuousOn
  have hdiff_nonneg : ∀ z, 0 ≤ f z * max (0 : ℝ) (1 - c₁ * |z| / r) -
      f z * max (0 : ℝ) (1 - c₂ * |z| / r) := fun z => by
    rw [← mul_sub]
    refine mul_nonneg (hf_pos z).le (sub_nonneg.2 (max_le_max le_rfl ?_))
    gcongr
  refine pos_integral_of_bound_Icc (hi1.sub hi2) hdiff_nonneg (show δ / 2 < δ by linarith)
    (mul_pos (hf_pos z₀) (div_pos (mul_pos hdiff_c (half_pos hδ)) hr)) fun z hz => ?_
  have hz0 : 0 ≤ z := by linarith [hz.1]
  have hc2δ : c₂ * |z| / r ≤ 1 / 2 := mul_abs_div_le_half hr hc₂ hz0 hz.2
  have hc1δ : c₁ * |z| / r ≤ 1 / 2 :=
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hlt.le (abs_nonneg z)) hr.le).trans hc2δ
  rw [← mul_sub, max_eq_right (by linarith : 0 ≤ 1 - c₁ * |z| / r),
    max_eq_right (by linarith : 0 ≤ 1 - c₂ * |z| / r)]
  have hgap : (c₂ - c₁) * (δ / 2) / r ≤ (1 - c₁ * |z| / r) - (1 - c₂ * |z| / r) := by
    rw [abs_of_nonneg hz0]
    have heq : (1 - c₁ * z / r) - (1 - c₂ * z / r) = (c₂ - c₁) * z / r := by ring
    rw [heq]
    gcongr
    exact hz.1
  exact mul_le_mul (hz₀ hz) hgap (by positivity) (hf_pos z).le

/-- For an even, continuous, integrable density `f`, `stableCollisionProb` reduces to
`2 * ∫ z in 0..(r / c), (1 - c * z / r) * f z`. -/
private theorem stableCollisionProb_withDensity_eq_two_mul {f : ℝ → ℝ}
    (hf_cont : Continuous f) (hf_nonneg : ∀ z, 0 ≤ f z) (hf_int : Integrable f)
    (hf_even : ∀ z, f (-z) = f z) {r c : ℝ} (hr : 0 < r) (hc : 0 < c) :
    stableCollisionProb (volume.withDensity fun z => ENNReal.ofReal (f z)) r c =
      2 * ∫ z in (0 : ℝ)..(r / c), (1 - c * z / r) * f z := by
  have hrc : 0 < r / c := div_pos hr hc
  have hm : Measurable (fun z => ENNReal.ofReal (f z)) := by fun_prop
  rw [stableCollisionProb, integral_withDensity_eq_integral_toReal_smul hm
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (hf_nonneg _), smul_eq_mul]
  have hsupp : ∀ z ∉ Set.Icc (-(r / c)) (r / c),
      f z * max (0 : ℝ) (1 - c * |z| / r) = 0 := fun z hz => by
    have habs : r / c < |z| := by
      by_contra hle
      rw [not_lt] at hle
      have := abs_le.1 hle
      exact hz ⟨this.1, this.2⟩
    have h1 : 1 - c * |z| / r ≤ 0 := by
      rw [sub_nonpos, one_le_div hr, mul_comm]
      exact ((div_lt_iff₀ hc).1 habs).le
    rw [max_eq_left h1, mul_zero]
  have hint_full := integrable_mul_stableKernel' hf_cont hf_nonneg hf_int hr hc.le
  have hzero : ∫ z in (Set.Icc (-(r / c)) (r / c))ᶜ, f z * max (0 : ℝ) (1 - c * |z| / r) = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero hsupp
  rw [← integral_add_compl measurableSet_Icc hint_full, hzero, add_zero,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (a := -(r / c)) (b := 0) (c := r / c)
    hint_full.intervalIntegrable hint_full.intervalIntegrable
  have hneg : ∫ z in (-(r / c))..0, f z * max (0 : ℝ) (1 - c * |z| / r) =
      ∫ z in (0 : ℝ)..(r / c), f z * max (0 : ℝ) (1 - c * |z| / r) := by
    have hcomp := intervalIntegral.integral_comp_neg
      (fun z : ℝ => f z * max (0 : ℝ) (1 - c * |z| / r)) (a := -(r / c)) (b := 0)
    simp only [neg_zero, neg_neg] at hcomp
    rw [← hcomp]
    refine intervalIntegral.integral_congr fun z _ => ?_
    simp only [abs_neg, hf_even z]
  rw [← hsplit, hneg, ← two_mul]
  congr 1
  refine intervalIntegral.integral_congr fun z hz => ?_
  rw [Set.uIcc_of_le hrc.le] at hz
  rw [abs_of_nonneg hz.1, max_eq_right, mul_comm]
  rw [sub_nonneg, div_le_one hr, mul_comm c z]
  exact (le_div_iff₀ hc).1 hz.2

/-! ### `p = 2`: Gaussian `2`-stable LSH -/

/-- The `p = 2` (Gaussian) LSH function of width `r` on an inner product space `E`:
`⌊(⟪a, x⟫ + b) / r⌋`. -/
@[expose] noncomputable def p2StableHash {E : Type*} [SeminormedAddCommGroup E]
    [InnerProductSpace ℝ E] (r : ℝ) (seed : E × ℝ) (x : E) : ℤ :=
  intervalFloorHash r (fun a v => ⟪a, v⟫) seed x

/-- Exact collision probability for Gaussian `p = 2` LSH at distance `c` and bucket width `r`. -/
@[expose] noncomputable def p2StableProb (r c : ℝ) : ℝ :=
  stableCollisionProb (gaussianReal 0 1) r c

/-- The `p = 2` collision event is measurable. -/
theorem measurableSet_p2StableHash_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] (r : ℝ) (u v : E) :
    MeasurableSet {p : E × ℝ | p2StableHash r p u = p2StableHash r p v} :=
  measurableSet_intervalFloorHash_eq r (fun x => by fun_prop) u v

theorem p2StableProb_zero (r : ℝ) : p2StableProb r 0 = 1 :=
  stableCollisionProb_zero (gaussianReal 0 1) r

theorem p2StableProb_nonneg (r c : ℝ) : 0 ≤ p2StableProb r c :=
  stableCollisionProb_nonneg (gaussianReal 0 1) r c

theorem p2StableProb_le_one {r c : ℝ} (hr : 0 < r) (hc : 0 ≤ c) : p2StableProb r c ≤ 1 :=
  stableCollisionProb_le_one (gaussianReal 0 1) hr hc

theorem p2StableProb_anti {r : ℝ} (hr : 0 < r) {c₁ c₂ : ℝ} (hc₁ : 0 ≤ c₁) (hle : c₁ ≤ c₂) :
    p2StableProb r c₂ ≤ p2StableProb r c₁ :=
  stableCollisionProb_anti (gaussianReal 0 1) hr hc₁ hle

theorem p2StableProb_pos {r c : ℝ} (hr : 0 < r) (hc : 0 ≤ c) : 0 < p2StableProb r c := by
  rw [p2StableProb, gaussianReal_of_var_ne_zero 0 one_ne_zero]
  exact stableCollisionProb_withDensity_pos (by unfold gaussianPDFReal; fun_prop)
    (fun z => gaussianPDFReal_pos 0 1 z one_ne_zero) (integrable_gaussianPDFReal 0 1) hr hc

theorem p2StableProb_strictAnti {r c₁ c₂ : ℝ} (hr : 0 < r) (hc₁ : 0 ≤ c₁) (hlt : c₁ < c₂) :
    p2StableProb r c₂ < p2StableProb r c₁ := by
  rw [p2StableProb, p2StableProb, gaussianReal_of_var_ne_zero 0 one_ne_zero]
  exact stableCollisionProb_withDensity_strictAnti (by unfold gaussianPDFReal; fun_prop)
    (fun z => gaussianPDFReal_pos 0 1 z one_ne_zero) (integrable_gaussianPDFReal 0 1) hr hc₁ hlt

/-- Shared reduction of `p2StableProb r c` to twice the half-line integral on `0..(r / c)`. -/
private theorem p2StableProb_eq_two_mul {r c : ℝ} (hr : 0 < r) (hc : 0 < c) :
    p2StableProb r c =
      2 * ∫ z in (0 : ℝ)..(r / c), (1 - c * z / r) * gaussianPDFReal 0 1 z := by
  have heven : ∀ z, gaussianPDFReal 0 1 (-z) = gaussianPDFReal 0 1 z := fun z => by
    simp [gaussianPDFReal_def]
  have h2 := stableCollisionProb_withDensity_eq_two_mul (by unfold gaussianPDFReal; fun_prop)
    (fun z => (gaussianPDFReal_pos 0 1 z one_ne_zero).le) (integrable_gaussianPDFReal 0 1)
    heven hr hc
  rw [p2StableProb, gaussianReal_of_var_ne_zero 0 one_ne_zero]
  change stableCollisionProb
    (volume.withDensity fun z => ENNReal.ofReal (gaussianPDFReal 0 1 z)) r c = _
  exact h2

/-- **Exact integral representation for `p = 2`** ([DatarImmorlicaIndykMirrokni2004]): for `r > 0`
and `c > 0`, `p2StableProb r c = ∫ t in 0..r, (2 / c) * gaussianPDFReal 0 1 (t / c) * (1 - t / r)`.
-/
theorem p2StableProb_eq_integral {r c : ℝ} (hr : 0 < r) (hc : 0 < c) :
    p2StableProb r c =
      ∫ t in (0 : ℝ)..r, (2 / c) * gaussianPDFReal 0 1 (t / c) * (1 - t / r) := by
  rw [p2StableProb_eq_two_mul hr hc]
  have hcomp := intervalIntegral.integral_comp_mul_left
    (fun t : ℝ => (2 / c) * gaussianPDFReal 0 1 (t / c) * (1 - t / r)) (a := 0) (b := r / c) hc.ne'
  simp only [mul_zero, smul_eq_mul] at hcomp
  rw [mul_div_cancel₀ _ hc.ne'] at hcomp
  have hcongr : ∫ z in (0 : ℝ)..(r / c),
        (2 / c) * gaussianPDFReal 0 1 (c * z / c) * (1 - c * z / r) =
      (2 / c) * ∫ z in (0 : ℝ)..(r / c), (1 - c * z / r) * gaussianPDFReal 0 1 z := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun z _ => ?_
    rw [mul_div_cancel_left₀ z hc.ne']
    ring
  rw [hcongr] at hcomp
  calc 2 * ∫ z in (0 : ℝ)..(r / c), (1 - c * z / r) * gaussianPDFReal 0 1 z
      = c * ((2 / c) * ∫ z in (0 : ℝ)..(r / c), (1 - c * z / r) * gaussianPDFReal 0 1 z) := by
          field_simp [hc.ne']
    _ = ∫ t in (0 : ℝ)..r, (2 / c) * gaussianPDFReal 0 1 (t / c) * (1 - t / r) := by
          rw [hcomp, ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]

/-- **Closed-form evaluation for `p = 2`**: for `r > 0` and `c > 0`, `p2StableProb r c` equals
`(gaussianReal 0 1).real (Icc (-r / c) (r / c)) -`
`√(2 / π) * (c / r) * (1 - exp (-(r / c) ^ 2 / 2))`. -/
theorem p2StableProb_eq_sub {r c : ℝ} (hr : 0 < r) (hc : 0 < c) :
    p2StableProb r c =
      (gaussianReal 0 1).real (Set.Icc (-r / c) (r / c)) -
        √(2 / π) * (c / r) * (1 - Real.exp (-((r / c) ^ 2) / 2)) := by
  rw [p2StableProb_eq_two_mul hr hc]
  have hi1 : IntervalIntegrable (gaussianPDFReal 0 1) volume 0 (r / c) :=
    (integrable_gaussianPDFReal 0 1).intervalIntegrable
  have hi2 : IntervalIntegrable (fun z : ℝ => (c * z / r) * gaussianPDFReal 0 1 z) volume 0
      (r / c) :=
    Continuous.intervalIntegrable (by unfold gaussianPDFReal; fun_prop) _ _
  have hsplit : (fun z : ℝ => (1 - c * z / r) * gaussianPDFReal 0 1 z) =
      fun z => gaussianPDFReal 0 1 z - (c * z / r) * gaussianPDFReal 0 1 z := funext fun z => by
    ring
  rw [hsplit, intervalIntegral.integral_sub hi1 hi2, mul_sub]
  have hnorm : 2 * ∫ z in (0 : ℝ)..(r / c), gaussianPDFReal 0 1 z =
      (gaussianReal 0 1).real (Set.Icc (-r / c) (r / c)) := by
    have heven : ∀ z, gaussianPDFReal 0 1 (-z) = gaussianPDFReal 0 1 z := fun z => by
      simp only [gaussianPDFReal_def, sub_zero, neg_sq]
    have hcomp := intervalIntegral.integral_comp_neg (gaussianPDFReal 0 1) (a := -(r / c)) (b := 0)
    simp only [neg_zero, neg_neg, heven] at hcomp
    have hrc : 0 < r / c := div_pos hr hc
    have hadj := intervalIntegral.integral_add_adjacent_intervals (a := -(r / c)) (b := 0)
      (c := r / c) (integrable_gaussianPDFReal 0 1).intervalIntegrable hi1
    rw [two_mul]
    nth_rw 1 [← hcomp]
    rw [hadj, intervalIntegral.integral_of_le (neg_le_self hrc.le), ← integral_Icc_eq_integral_Ioc,
      ← neg_div, measureReal_def,
      gaussianReal_apply_eq_integral 0 one_ne_zero (Set.Icc (-r / c) (r / c)),
      ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Icc fun z _ =>
        (gaussianPDFReal_pos 0 1 z one_ne_zero).le)]
  have htail : 2 * ∫ z in (0 : ℝ)..(r / c), (c * z / r) * gaussianPDFReal 0 1 z =
      √(2 / π) * (c / r) * (1 - Real.exp (-((r / c) ^ 2) / 2)) := by
    have hcongr : (fun z : ℝ => (c * z / r) * gaussianPDFReal 0 1 z) =
        fun z => ((c / r) * (√(2 * π))⁻¹) * (z * Real.exp (-(z ^ 2) / 2)) := by
      funext z
      simp only [gaussianPDFReal_def, sub_zero, NNReal.coe_one, mul_one]
      ring
    have hderiv : ∀ z ∈ uIcc 0 (r / c),
        HasDerivAt (fun s : ℝ => -Real.exp (-(s ^ 2) / 2)) (z * Real.exp (-(z ^ 2) / 2)) z := by
      intro z _
      have hd := (hasDerivAt_pow 2 z).neg.div_const 2
      have hd' : HasDerivAt (fun s : ℝ => -(s ^ 2) / 2) (-z) z := by
        simpa [two_mul] using hd
      exact hd'.exp.neg.congr_deriv (by ring)
    have hie : IntervalIntegrable (fun z : ℝ => z * Real.exp (-(z ^ 2) / 2)) volume 0 (r / c) :=
      Continuous.intervalIntegrable (by fun_prop) _ _
    rw [hcongr, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hie]
    simp only [zero_pow (by decide : 2 ≠ 0), neg_zero, zero_div, Real.exp_zero]
    have hsqrt : 2 * (√(2 * π))⁻¹ = √(2 / π) := by
      have h2ne : √(2 : ℝ) ≠ 0 := Real.sqrt_ne_zero'.2 zero_lt_two
      have hpne : √π ≠ 0 := Real.sqrt_ne_zero'.2 pi_pos
      rw [Real.sqrt_div zero_le_two, Real.sqrt_mul zero_le_two]
      field_simp
      rw [Real.sq_sqrt zero_le_two]
    calc 2 * ((c / r) * (√(2 * π))⁻¹ * (-Real.exp (-((r / c) ^ 2) / 2) - -1))
        = (2 * (√(2 * π))⁻¹) * (c / r) * (1 - Real.exp (-((r / c) ^ 2) / 2)) := by ring
      _ = √(2 / π) * (c / r) * (1 - Real.exp (-((r / c) ^ 2) / 2)) := by rw [hsqrt]
  rw [hnorm, htail, gaussianReal_of_var_ne_zero 0 one_ne_zero]

/-- **Gaussian `p = 2` LSH collision probability** ([DatarImmorlicaIndykMirrokni2004]):
under `(stdGaussian E).prod (uniformInterval r)`, `p2StableHash r` collides on `u` and `v`
with probability `p2StableProb r ‖u - v‖`. -/
theorem measureCollisionProb_p2StableHash {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {r : ℝ} (hr : 0 < r) (u v : E) :
    measureCollisionProb ((stdGaussian E).prod (uniformInterval r)) (p2StableHash r) u v =
      p2StableProb r ‖u - v‖ := by
  refine measureCollisionProb_intervalFloorHash_of_map (stdGaussian E) (gaussianReal 0 1) hr
    (fun a x => ⟪a, x⟫) (fun x => by fun_prop) u v (norm_nonneg (u - v)) ?_
  have hsub : (fun a : E => ⟪a, u⟫ - ⟪a, v⟫) = fun a : E => ⟪u - v, a⟫ := by
    funext a
    rw [← inner_sub_right a u v, real_inner_comm]
  rw [hsub, stdGaussian_map_inner, gaussianReal_map_const_mul, mul_zero, mul_one]
  congr 2

/-- Gaussian `p = 2` LSH is `(d₁, d₂, p2StableProb r d₁, p2StableProb r d₂)`-sensitive for the
Euclidean distance when `0 < r` and `0 ≤ d₂`. -/
theorem isLocalitySensitive_p2StableHash {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {r : ℝ} (hr : 0 < r) (d₁ : ℝ) {d₂ : ℝ} (hd₂ : 0 ≤ d₂) :
    IsLocalitySensitive
      (measureCollisionProb ((stdGaussian E).prod (uniformInterval r)) (p2StableHash r))
      (fun u v => ‖u - v‖ ≤ d₁) (fun u v => d₂ ≤ ‖u - v‖)
      (p2StableProb r d₁) (p2StableProb r d₂) where
  le_of_near u v h := by
    rw [measureCollisionProb_p2StableHash hr]
    exact p2StableProb_anti hr (norm_nonneg _) h
  le_of_far u v h := by
    rw [measureCollisionProb_p2StableHash hr]
    exact p2StableProb_anti hr hd₂ h

/-! ### `p = 1`: Cauchy `1`-stable LSH -/

/-- The `p = 1` (Cauchy) LSH function of width `r` on coordinate vectors `ι → ℝ`:
`⌊(a ⬝ᵥ x + b) / r⌋`. -/
@[expose] noncomputable def p1StableHash {ι : Type*} [Fintype ι] (r : ℝ)
    (seed : (ι → ℝ) × ℝ) (x : ι → ℝ) : ℤ :=
  intervalFloorHash r (fun a v => a ⬝ᵥ v) seed x

/-- Exact collision probability for Cauchy `p = 1` LSH at `\ell_1` distance `c` and width `r`. -/
@[expose] noncomputable def p1StableProb (r c : ℝ) : ℝ :=
  stableCollisionProb (cauchyMeasure 0 1) r c

/-- The `p = 1` collision event is measurable. -/
theorem measurableSet_p1StableHash_eq {ι : Type*} [Fintype ι] (r : ℝ) (u v : ι → ℝ) :
    MeasurableSet {p : (ι → ℝ) × ℝ | p1StableHash r p u = p1StableHash r p v} :=
  measurableSet_intervalFloorHash_eq r (fun x => by fun_prop) u v

private theorem continuous_cauchyPDFReal : Continuous (cauchyPDFReal 0 1) := by
  unfold cauchyPDFReal
  exact continuous_const.mul (Continuous.inv₀ (by fun_prop) fun x => by positivity)

theorem p1StableProb_zero (r : ℝ) : p1StableProb r 0 = 1 :=
  stableCollisionProb_zero (cauchyMeasure 0 1) r

theorem p1StableProb_nonneg (r c : ℝ) : 0 ≤ p1StableProb r c :=
  stableCollisionProb_nonneg (cauchyMeasure 0 1) r c

theorem p1StableProb_le_one {r c : ℝ} (hr : 0 < r) (hc : 0 ≤ c) : p1StableProb r c ≤ 1 :=
  stableCollisionProb_le_one (cauchyMeasure 0 1) hr hc

theorem p1StableProb_anti {r : ℝ} (hr : 0 < r) {c₁ c₂ : ℝ} (hc₁ : 0 ≤ c₁) (hle : c₁ ≤ c₂) :
    p1StableProb r c₂ ≤ p1StableProb r c₁ :=
  stableCollisionProb_anti (cauchyMeasure 0 1) hr hc₁ hle

theorem p1StableProb_pos {r c : ℝ} (hr : 0 < r) (hc : 0 ≤ c) : 0 < p1StableProb r c := by
  rw [p1StableProb, cauchyMeasure_of_scale_ne_zero 0 one_ne_zero]
  exact stableCollisionProb_withDensity_pos continuous_cauchyPDFReal
    (fun z => cauchyPDF_pos 0 one_ne_zero z) (integrable_cauchyPDFReal 0) hr hc

theorem p1StableProb_strictAnti {r c₁ c₂ : ℝ} (hr : 0 < r) (hc₁ : 0 ≤ c₁) (hlt : c₁ < c₂) :
    p1StableProb r c₂ < p1StableProb r c₁ := by
  rw [p1StableProb, p1StableProb, cauchyMeasure_of_scale_ne_zero 0 one_ne_zero]
  exact stableCollisionProb_withDensity_strictAnti continuous_cauchyPDFReal
    (fun z => cauchyPDF_pos 0 one_ne_zero z) (integrable_cauchyPDFReal 0) hr hc₁ hlt

/-- **Closed-form evaluation for `p = 1`**: for `r > 0` and `c > 0`,
`p1StableProb r c = (2 / π) arctan (r / c) - (c / (π r)) log (1 + (r / c) ^ 2)`. -/
theorem p1StableProb_eq {r c : ℝ} (hr : 0 < r) (hc : 0 < c) :
    p1StableProb r c = 2 / π * Real.arctan (r / c) - c / (π * r) * Real.log (1 + (r / c) ^ 2) := by
  have heven : ∀ z, cauchyPDFReal 0 1 (-z) = cauchyPDFReal 0 1 z := fun z => by
    simp [cauchyPDFReal_def]
  have h2 := stableCollisionProb_withDensity_eq_two_mul continuous_cauchyPDFReal
    (fun z => (cauchyPDF_pos 0 one_ne_zero z).le) (integrable_cauchyPDFReal 0) heven hr hc
  rw [p1StableProb, cauchyMeasure_of_scale_ne_zero 0 one_ne_zero]
  change stableCollisionProb
    (volume.withDensity fun z => ENNReal.ofReal (cauchyPDFReal 0 1 z)) r c = _
  rw [h2]
  have hcongr : (fun z : ℝ => (1 - c * z / r) * cauchyPDFReal 0 1 z) =
      fun z => π⁻¹ * (1 + z ^ 2)⁻¹ - (c / (π * r)) * (z * (1 + z ^ 2)⁻¹) := by
    funext z
    simp only [cauchyPDFReal_def, sub_zero, NNReal.coe_one, mul_one]
    ring
  have hi1 : IntervalIntegrable (fun z : ℝ => π⁻¹ * (1 + z ^ 2)⁻¹) volume 0 (r / c) :=
    Continuous.intervalIntegrable
      (continuous_const.mul (Continuous.inv₀ (by fun_prop) fun z => by positivity)) _ _
  have hi2 : IntervalIntegrable (fun z : ℝ => (c / (π * r)) * (z * (1 + z ^ 2)⁻¹))
      volume 0 (r / c) :=
    Continuous.intervalIntegrable (continuous_const.mul (continuous_id.mul
      (Continuous.inv₀ (by fun_prop) fun z => by positivity))) _ _
  have hd1 : ∀ z ∈ uIcc 0 (r / c),
      HasDerivAt Real.arctan (1 + z ^ 2)⁻¹ z := fun z _ => Real.hasDerivAt_arctan' z
  have hd2 : ∀ z ∈ uIcc 0 (r / c),
      HasDerivAt (fun s : ℝ => (2 : ℝ)⁻¹ * Real.log (1 + s ^ 2)) (z * (1 + z ^ 2)⁻¹) z := by
    intro z _
    have hpos : 1 + z ^ 2 ≠ 0 := by positivity
    have hsq : HasDerivAt (fun s : ℝ => 1 + s ^ 2) (2 * z) z := by
      simpa using (hasDerivAt_pow 2 z).const_add 1
    exact ((hsq.log hpos).const_mul (2 : ℝ)⁻¹).congr_deriv (by field_simp)
  have hie1 : IntervalIntegrable (fun z : ℝ => (1 + z ^ 2)⁻¹) volume 0 (r / c) :=
    Continuous.intervalIntegrable (Continuous.inv₀ (by fun_prop) fun z => by positivity) _ _
  have hie2 : IntervalIntegrable (fun z : ℝ => z * (1 + z ^ 2)⁻¹) volume 0 (r / c) :=
    Continuous.intervalIntegrable (continuous_id.mul
      (Continuous.inv₀ (by fun_prop) fun z => by positivity)) _ _
  rw [hcongr, intervalIntegral.integral_sub hi1 hi2, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_eq_sub_of_hasDerivAt hd1 hie1,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hd2 hie2]
  simp only [Real.arctan_zero, sub_zero, zero_pow (by decide : 2 ≠ 0), add_zero, Real.log_one,
    mul_zero]
  ring

/-- **Cauchy `p = 1` LSH collision probability** ([DatarImmorlicaIndykMirrokni2004]): under
`Measure.pi (fun _ : ι => cauchyMeasure 0 1)` paired with `uniformInterval r`, `p1StableHash r`
collides on `u` and `v` with probability `p1StableProb r (∑ i, |u i - v i|)`. -/
theorem measureCollisionProb_p1StableHash {ι : Type*} [Fintype ι] {r : ℝ} (hr : 0 < r)
    (u v : ι → ℝ) :
    measureCollisionProb
        ((Measure.pi fun _ : ι => cauchyMeasure 0 1).prod (uniformInterval r))
        (p1StableHash r) u v =
      p1StableProb r (∑ i, |u i - v i|) := by
  refine measureCollisionProb_intervalFloorHash_of_map (Measure.pi fun _ : ι => cauchyMeasure 0 1)
    (cauchyMeasure 0 1) hr (fun a x => a ⬝ᵥ x) (fun x => by fun_prop) u v
    (Finset.sum_nonneg fun _ _ => abs_nonneg _) ?_
  have hsub : (fun a : ι → ℝ => a ⬝ᵥ u - a ⬝ᵥ v) = fun a : ι → ℝ => (u - v) ⬝ᵥ a := by
    funext a
    simp only [dotProduct, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
    congr 1 <;> exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [hsub, pi_cauchyMeasure_map_dotProduct, cauchyMeasure_map_const_mul, mul_zero, mul_one]
  congr 1
  apply NNReal.coe_injective
  simp only [NNReal.coe_sum, coe_nnnorm, Real.norm_eq_abs, Pi.sub_apply]
  exact (abs_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)).symm

/-- Cauchy `p = 1` LSH is `(d₁, d₂, p1StableProb r d₁, p1StableProb r d₂)`-sensitive for the
`\ell_1` distance `∑ i, |u i - v i|` when `0 < r` and `0 ≤ d₂`. -/
theorem isLocalitySensitive_p1StableHash {ι : Type*} [Fintype ι] {r : ℝ} (hr : 0 < r)
    (d₁ : ℝ) {d₂ : ℝ} (hd₂ : 0 ≤ d₂) :
    IsLocalitySensitive
      (measureCollisionProb
        ((Measure.pi fun _ : ι => cauchyMeasure 0 1).prod (uniformInterval r))
        (p1StableHash r))
      (fun u v => ∑ i, |u i - v i| ≤ d₁) (fun u v => d₂ ≤ ∑ i, |u i - v i|)
      (p1StableProb r d₁) (p1StableProb r d₂) where
  le_of_near u v h := by
    rw [measureCollisionProb_p1StableHash hr]
    exact p1StableProb_anti hr (Finset.sum_nonneg fun _ _ => abs_nonneg _) h
  le_of_far u v h := by
    rw [measureCollisionProb_p1StableHash hr]
    exact p1StableProb_anti hr hd₂ h

end Cslib.Probability
