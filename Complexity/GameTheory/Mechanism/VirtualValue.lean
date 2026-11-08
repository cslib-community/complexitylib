/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.WithDensity
import Complexity.Foundations.MeasureTheory.Integral.IntervalPrimitive
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Value distributions and virtual valuations

This file sets up the Bayesian side of single-parameter mechanism design
([Roughgarden2013CS364A], Lecture 5; [Myerson1981]). A bidder's private valuation is drawn from a
distribution `μ` on `[0, h]` with density `f` (`HasValueDensity μ f h`). Its *virtual valuation*
is `φ(v) = v − (1 − F(v)) / f(v)` (Lecture 5, §2, Step 4). Here `1 − F(v)` is written
`μ.real (Ioi v)`, so the definition needs no separate cumulative distribution function. The
distribution is *regular* when `φ` is strictly increasing on `[0, h]` (Lecture 5,
Definition 3.1).

The main result is the one-dimensional revenue identity (Lecture 5, §2, Steps 1–4, eq. (4)). For
an allocation curve `g` that is measurable and bounded on `[0, h]`,
`E_v[v g(v) − ∫₀ᵛ g] = E_v[φ(v) g(v)]`.
The left side is the expected Myerson payment (Lecture 3, Theorem 4.3 (c)) of a bidder facing
allocation curve `g`. Roughgarden proves it by reversing the order of integration (Step 2) and then
integrating by parts (Step 3). We reverse the order of integration only
(`integral_intervalIntegral_eq_integral_measureReal_Ici_mul`): the tail `μ([z, ∞))` then cancels
the density in `φ`. No differentiability or monotonicity of `g` is needed.

The density is assumed positive on the open interval `(0, h)`. Without this, the identity can fail
on a set of positive measure where `f = 0` but `μ((v, ∞)) > 0`, because `φ` uses Lean's
`x / 0 = 0`. Even with positivity, `φ` depends on the chosen version of `f`, which `μ` determines
only almost everywhere. The identity is insensitive to this, but the pointwise predicate `IsRegular`
is not: at `v = 0` it evaluates `φ(0) = −1/f(0)`. See the endpoint convention in `IsRegular`, which
makes it stronger than Lecture 5, Definition 3.1 for densities with `(1 − F)/f → ∞` at `0`.

## Main definitions

* `SingleParameter.HasValueDensity μ f h`: `μ` is the distribution on `[0, h]` with density `f`,
  positive on `(0, h)`.
* `SingleParameter.virtualValue μ f v`: the virtual valuation `v − μ((v, ∞)) / f(v)`.
* `SingleParameter.IsRegular μ f h`: the virtual valuation is strictly increasing on `[0, h]`,
  including the endpoint `0` (which requires `f(0) > 0` and `φ` bounded below near `0`).

## Main results

* `SingleParameter.HasValueDensity.integral_payment_eq_integral_virtualValue_mul`: the
  one-dimensional revenue identity.
* `SingleParameter.HasValueDensity.integrable_virtualValue`: virtual valuations are integrable.
* `SingleParameter.IsRegular.strictMonoOn_Ici`: a regular virtual valuation is strictly increasing
  on all of `[0, ∞)`, because `φ(v) = v` above the support.
* `SingleParameter.virtualValue_uniform`, `SingleParameter.isRegular_uniform`: the uniform
  distribution on `[0, 1]` has `φ(v) = 2v − 1` and is regular (Lecture 5, §2).

## References

* [T. Roughgarden, *CS364A: Algorithmic Game Theory*, lecture notes][Roughgarden2013CS364A]
* [R. B. Myerson, *Optimal auction design*][Myerson1981]
-/

open MeasureTheory Set

public section

namespace Cslib.GameTheory.SingleParameter

/-- `μ` is a valuation distribution on `[0, h]` with density `f`, and `f` is positive on the
interior `(0, h)`. -/
structure HasValueDensity (μ : Measure ℝ) (f : ℝ → NNReal) (h : ℝ) : Prop where
  /-- The density is measurable. -/
  measurable : Measurable f
  /-- `μ` is Lebesgue measure on `[0, h]` weighted by `f`. -/
  eq_withDensity : μ = (volume.restrict (Icc 0 h)).withDensity fun v => (f v : ENNReal)
  /-- The density is positive on the interior of the support. -/
  pos : ∀ v ∈ Ioo 0 h, 0 < f v

/-- The **virtual valuation** `φ(v) = v − (1 − F(v)) / f(v)` ([Roughgarden2013CS364A], Lecture 5,
§2, Step 4), with `1 − F(v) = μ((v, ∞))`. -/
@[expose] noncomputable def virtualValue (μ : Measure ℝ) (f : ℝ → NNReal) (v : ℝ) : ℝ :=
  v - μ.real (Ioi v) / f v

/-- A valuation distribution on `[0, h]` is **regular** if its virtual valuation is strictly
increasing on `[0, h]` ([Roughgarden2013CS364A], Lecture 5, Definition 3.1).

**Endpoint convention.** The predicate includes `v = 0`, where `φ(0) = −1/f(0)` depends on the
chosen value `f(0)`, which does not affect `μ`. It therefore requires `f(0) > 0` and
`−1/f(0) < φ(v)` for all `v ∈ (0, h]`; in particular `φ` must be bounded below near `0`. The choice
`f(0) = 0` never works, because then `φ(0) = 0`. This is strictly stronger than Definition 3.1 for
densities with `(1 − F(v))/f(v) → ∞` as `v → 0⁺`. For example, `f(v) = 2v` on `[0, 1]` has
`φ(v) = (3v² − 1)/(2v)` on `(0, 1]`, which is strictly increasing there but tends to `−∞`, so it is
regular in the textbook sense but satisfies `IsRegular` for no choice of `f(0)`. -/
@[expose] def IsRegular (μ : Measure ℝ) (f : ℝ → NNReal) (h : ℝ) : Prop :=
  StrictMonoOn (virtualValue μ f) (Icc 0 h)

/-- The tail `v ↦ μ((v, ∞))` of a finite measure is measurable (it is antitone). -/
theorem measurable_measureReal_Ioi (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Measurable fun v => μ.real (Ioi v) :=
  Antitone.measurable fun _ _ hab => measureReal_mono (Ioi_subset_Ioi hab)

/-- The virtual valuation never exceeds the valuation. -/
theorem virtualValue_le (μ : Measure ℝ) (f : ℝ → NNReal) (v : ℝ) : virtualValue μ f v ≤ v :=
  sub_le_self _ (div_nonneg measureReal_nonneg (NNReal.coe_nonneg _))

namespace HasValueDensity

variable {μ : Measure ℝ} {f : ℝ → NNReal} {h : ℝ}

theorem absolutelyContinuous (hμ : HasValueDensity μ f h) : μ ≪ volume := by
  rw [hμ.eq_withDensity]
  exact (withDensity_absolutelyContinuous _ _).trans
    (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)

/-- Almost every valuation lies in `[0, h]`. -/
theorem ae_mem (hμ : HasValueDensity μ f h) : ∀ᵐ v ∂μ, v ∈ Icc 0 h := by
  rw [hμ.eq_withDensity]
  exact (withDensity_absolutelyContinuous _ _) (ae_restrict_mem measurableSet_Icc)

/-- A distribution with a density has no atoms. -/
theorem nullSingletonClass (hμ : HasValueDensity μ f h) : NullSingletonClass μ :=
  ⟨fun x => hμ.absolutelyContinuous (measure_singleton x)⟩

/-- No mass lies above `h`. -/
theorem measure_Ioi_eq_zero (hμ : HasValueDensity μ f h) {v : ℝ} (hv : h ≤ v) :
    μ (Ioi v) = 0 :=
  measure_mono_null (t := {w | w ∉ Icc 0 h})
    (fun w (hw : v < w) (hw' : w ∈ Icc 0 h) => absurd (hw'.2.trans hv) (not_le.2 hw))
    (ae_iff.1 hμ.ae_mem)

/-- Above the support, the virtual valuation is the valuation. -/
theorem virtualValue_eq_self (hμ : HasValueDensity μ f h) {v : ℝ} (hv : h ≤ v) :
    virtualValue μ f v = v := by
  rw [virtualValue, measureReal_def, hμ.measure_Ioi_eq_zero hv, ENNReal.toReal_zero, zero_div,
    sub_zero]

/-- Integrals against `μ` are integrals of `f · g` over `[0, h]`. -/
theorem integral_eq (hμ : HasValueDensity μ f h) (g : ℝ → ℝ) :
    ∫ v, g v ∂μ = ∫ v in Icc 0 h, (f v : ℝ) * g v := by
  rw [hμ.eq_withDensity, integral_withDensity_eq_integral_smul hμ.measurable]
  rfl

/-- Dividing by the density cancels it: `∫ (t / f) · g dμ = ∫_{(0, h]} t · g`. -/
theorem integral_div_mul (hμ : HasValueDensity μ f h) (t g : ℝ → ℝ) :
    ∫ v, t v / f v * g v ∂μ = ∫ v in Ioc 0 h, t v * g v := by
  rw [hμ.integral_eq, integral_Icc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  refine setIntegral_congr_fun measurableSet_Ioo fun v hv => ?_
  have : (f v : ℝ) ≠ 0 := by exact_mod_cast (hμ.pos v hv).ne'
  field_simp

theorem integrable_div_mul (hμ : HasValueDensity μ f h) {t g : ℝ → ℝ} (ht : Measurable t)
    (hg : Measurable g) {C : ℝ} (hC : ∀ v ∈ Icc 0 h, |t v * g v| ≤ C) :
    Integrable (fun v => t v / f v * g v) μ := by
  rw [hμ.eq_withDensity, integrable_withDensity_iff_integrable_smul hμ.measurable]
  refine Integrable.of_bound ?_ C ?_
  · exact ((hμ.measurable.coe_nnreal_real).smul
      ((ht.div hμ.measurable.coe_nnreal_real).mul hg)).aestronglyMeasurable
  · refine (ae_restrict_mem measurableSet_Icc).mono fun v hv => ?_
    rw [NNReal.smul_def, smul_eq_mul, Real.norm_eq_abs]
    by_cases hf : (f v : ℝ) = 0
    · rw [hf, zero_mul, abs_zero]
      exact (abs_nonneg _).trans (hC v hv)
    · have : (f v : ℝ) * (t v / f v * g v) = t v * g v := by field_simp
      rw [this]
      exact hC v hv

theorem measurable_virtualValue [IsFiniteMeasure μ] (hμ : HasValueDensity μ f h) :
    Measurable (virtualValue μ f) :=
  measurable_id.sub ((measurable_measureReal_Ioi μ).div hμ.measurable.coe_nnreal_real)

/-- Virtual valuations are integrable. -/
theorem integrable_virtualValue [IsFiniteMeasure μ] (hμ : HasValueDensity μ f h) :
    Integrable (virtualValue μ f) μ := by
  have h1 : Integrable (fun v : ℝ => v) μ := by
    refine Integrable.of_bound measurable_id.aestronglyMeasurable h ?_
    filter_upwards [hμ.ae_mem] with v hv
    rw [Real.norm_eq_abs, abs_of_nonneg hv.1]
    exact hv.2
  have h3 := hμ.integrable_div_mul (measurable_measureReal_Ioi μ)
    (measurable_const (a := (1 : ℝ))) (C := μ.real univ) fun v _ => by
      rw [mul_one, abs_of_nonneg measureReal_nonneg]
      exact measureReal_mono (subset_univ _)
  simp only [mul_one] at h3
  exact h1.sub h3

/-- **One-dimensional revenue identity** ([Roughgarden2013CS364A], Lecture 5, §2, Steps 1–4,
eq. (4)). For an allocation curve `g` that is measurable and bounded on `[0, h]`, the expected
Myerson payment `v g(v) − ∫₀ᵛ g` equals the expected virtual surplus `φ(v) g(v)`. -/
theorem integral_payment_eq_integral_virtualValue_mul [IsFiniteMeasure μ]
    (hμ : HasValueDensity μ f h) {g : ℝ → ℝ} (hg : Measurable g) {B : ℝ}
    (hB : ∀ v ∈ Icc 0 h, |g v| ≤ B) :
    ∫ v, (v * g v - ∫ z in (0 : ℝ)..v, g z) ∂μ = ∫ v, virtualValue μ f v * g v ∂μ := by
  have := hμ.nullSingletonClass
  have hae := hμ.ae_mem
  have hB0 : ∀ v ∈ Icc 0 h, 0 ≤ B := fun v hv => (abs_nonneg _).trans (hB v hv)
  have hgI : IntegrableOn g (Ioc 0 h) := by
    refine Integrable.of_bound hg.aestronglyMeasurable B ?_
    exact (ae_restrict_mem measurableSet_Ioc).mono fun v hv => hB v (Ioc_subset_Icc_self hv)
  have h1 : Integrable (fun v => v * g v) μ := by
    refine Integrable.of_bound (measurable_id.mul hg).aestronglyMeasurable (h * B) ?_
    filter_upwards [hae] with v hv
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hv.1]
    exact mul_le_mul hv.2 (hB v hv) (abs_nonneg _) (hv.1.trans hv.2)
  have h2 : Integrable (fun v => ∫ z in (0 : ℝ)..v, g z) μ := by
    refine Integrable.of_bound
      (measurable_intervalIntegral (G := fun _ z => g z) (hg.comp measurable_snd)
        measurable_const measurable_id).aestronglyMeasurable (h * B) ?_
    filter_upwards [hae] with v hv
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := B) fun z hz => ?_).trans ?_
    · rw [uIoc_of_le hv.1] at hz
      exact hB z ⟨hz.1.le, hz.2.trans hv.2⟩
    · rw [sub_zero, abs_of_nonneg hv.1, mul_comm]
      exact mul_le_mul_of_nonneg_right hv.2 (hB0 v hv)
  have h3 : Integrable (fun v => μ.real (Ioi v) / f v * g v) μ := by
    refine hμ.integrable_div_mul (measurable_measureReal_Ioi μ) hg (C := μ.real univ * B)
      fun v hv => ?_
    rw [abs_mul, abs_of_nonneg measureReal_nonneg]
    exact mul_le_mul (measureReal_mono (subset_univ _)) (hB v hv) (abs_nonneg _)
      measureReal_nonneg
  have hφ : (fun v => virtualValue μ f v * g v) =
      fun v => v * g v - μ.real (Ioi v) / f v * g v := by
    funext v
    rw [virtualValue]
    ring
  rw [integral_sub h1 h2, hφ, integral_sub h1 h3,
    integral_intervalIntegral_eq_integral_measureReal_Ici_mul hae hg hgI, hμ.integral_div_mul]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioc fun z _ => ?_
  rw [measureReal_congr (Ioi_ae_eq_Ici (μ := μ) (a := z))]

end HasValueDensity

/-- A regular virtual valuation is strictly increasing on all of `[0, ∞)`: above the support it is
the identity, and below it never exceeds the valuation. -/
theorem IsRegular.strictMonoOn_Ici {μ : Measure ℝ} {f : ℝ → NNReal} {h : ℝ}
    (hreg : IsRegular μ f h) (hμ : HasValueDensity μ f h) :
    StrictMonoOn (virtualValue μ f) (Ici 0) := by
  intro a ha b hb hab
  by_cases hbh : b ≤ h
  · exact hreg ⟨ha, hab.le.trans hbh⟩ ⟨hb, hbh⟩ hab
  · rw [hμ.virtualValue_eq_self (le_of_not_ge hbh)]
    exact (virtualValue_le μ f a).trans_lt hab

/-! ### The uniform distribution -/

/-- The uniform distribution on `[0, 1]` has density `1`. -/
theorem hasValueDensity_uniform : HasValueDensity (volume.restrict (Icc 0 1)) (fun _ => 1) 1 where
  measurable := measurable_const
  eq_withDensity := by
    simp only [ENNReal.coe_one]
    exact (withDensity_one (μ := volume.restrict (Icc (0 : ℝ) 1))).symm
  pos := fun _ _ => one_pos

/-- The uniform distribution on `[0, 1]` has virtual valuation `φ(v) = 2v − 1` on `[0, 1]`
([Roughgarden2013CS364A], Lecture 5, §2). -/
theorem virtualValue_uniform {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) :
    virtualValue (volume.restrict (Icc 0 1)) (fun _ => 1) v = 2 * v - 1 := by
  have hset : Ioi v ∩ Icc (0 : ℝ) 1 = Ioc v 1 := by
    ext w
    simp only [mem_inter_iff, mem_Ioi, mem_Icc, mem_Ioc]
    constructor
    · rintro ⟨h1, -, h3⟩
      exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩
      exact ⟨h1, hv.1.trans h1.le, h3⟩
  rw [virtualValue, measureReal_def, Measure.restrict_apply measurableSet_Ioi, hset,
    Real.volume_Ioc, ENNReal.toReal_ofReal (sub_nonneg.2 hv.2), NNReal.coe_one, div_one]
  ring

/-- The uniform distribution on `[0, 1]` is regular. -/
theorem isRegular_uniform : IsRegular (volume.restrict (Icc 0 1)) (fun _ => 1) 1 := by
  intro a ha b hb hab
  rw [virtualValue_uniform ha, virtualValue_uniform hb]
  linarith

end Cslib.GameTheory.SingleParameter
