/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, a new file `Mathlib/Probability/Distributions/Gaussian/`
-- `Sheppard.lean`)

public import Complexity.Init
public import Complexity.Foundations.Geometry.Euclidean.Angle.Unoriented.Basic
public import Complexity.Foundations.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Complexity.Foundations.Probability.Gaussian.Multivariate
import Complexity.Foundations.Probability.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.PolarCoord

/-!
# Sheppard's bound for threshold crossings of correlated Gaussians

Let `X` be a standard Gaussian vector of a finite-dimensional real inner product space, and let
`u`, `v` be vectors of equal norm at angle `θ`. When the common norm is positive, `⟪u, X⟫` and
`⟪v, X⟫` are Gaussians of equal variance with correlation `cos θ`. **Sheppard's bound**
(`measureReal_stdGaussian_mem_uIoc_le_angle`): a threshold `t` lies between `⟪u, X⟫` and
`⟪v, X⟫` with probability at most `θ / π`. For vectors of positive norm the bound is attained at
`t = 0`: that is Sheppard's formula [Sheppard1899] for the probability that two correlated
Gaussians differ in sign. For `u = v = 0` the crossing event is empty while Mathlib's
`angle 0 0` is `π / 2`, so the bound is then strict. Only the bound is proved here.

The proof has four steps.

1. *Change of variables.* The vectors `u + v` and `v - u` are orthogonal, so `U = ⟪u + v, X⟫` and
   `V = ⟪v - u, X⟫` are independent centered Gaussians, and a crossing at `t` forces
   `|U - 2 t| ≤ |V|`.
2. *Anderson's inequality on the line* (`ProbabilityTheory.gaussianReal_Icc_le`). Conditioning on
   `V`, the shift `2 t` only decreases the probability.
3. *The planar angle law* (`gaussianReal_prod_setOf_abs_le_mul_abs`). For independent standard
   Gaussians `Z₁`, `Z₂`, the event `|Z₁| ≤ k |Z₂|` constrains only the angle of `(Z₁, Z₂)` in
   polar coordinates, to two arcs of total length `4 arctan k`, so it has probability
   `(2 / π) arctan k`. Rescaling, `|U| ≤ |V|` has probability `(2 / π) arctan (‖v - u‖ / ‖u + v‖)`
   (`measureReal_stdGaussian_mem_uIoc_le_arctan`).
4. *The half-angle formula* (`InnerProductGeometry.angle_eq_two_mul_arctan`). For vectors of equal
   norm at angle `θ < π`, the ratio `‖v - u‖ / ‖u + v‖` is `tan (θ / 2)`.

The event that `t` lies between `x` and `y`, the lower one strictly below `t`, is
`t ∈ Set.uIoc x y`.

## Main results

* `ProbabilityTheory.gaussianReal_prod_setOf_abs_le_mul_abs`: the planar angle law.
* `ProbabilityTheory.gaussianReal_prod_setOf_abs_le_mul_abs_of_ne_zero`: the planar angle law for
  centered Gaussians of any variances.
* `ProbabilityTheory.measureReal_stdGaussian_mem_uIoc_le_arctan`,
  `ProbabilityTheory.measureReal_stdGaussian_mem_uIoc_le_angle`: Sheppard's bound.

## References

* [W. F. Sheppard, *On the application of the theory of error to cases of normal distribution
  and normal correlation*][Sheppard1899]
-/

@[expose] public section

open MeasureTheory Real Set
open scoped NNReal ENNReal RealInnerProductSpace Interval

namespace ProbabilityTheory

/-! ### The planar angle law -/

/-- The half-line integral `∫_{x > 0} x exp (-b x ^ 2) = 1 / (2b)`. -/
private theorem integral_Ioi_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) :
    ∫ x in Ioi (0 : ℝ), x * exp (-b * x ^ 2) = (2 * b)⁻¹ := by
  have h := integral_mul_cexp_neg_mul_sq (b := (b : ℂ)) (by simpa using hb)
  have h' : ((∫ x in Ioi (0 : ℝ), x * exp (-b * x ^ 2) : ℝ) : ℂ) = ((2 * b)⁻¹ : ℝ) := by
    rw [← integral_complex_ofReal]
    push_cast
    exact h
  exact_mod_cast h'

/-- The standard planar Gaussian density in polar coordinates is `exp (-r ^ 2 / 2) / (2π)`. -/
private theorem gaussianPDFReal_mul_polar (r θ : ℝ) :
    gaussianPDFReal 0 1 (r * cos θ) * gaussianPDFReal 0 1 (r * sin θ) =
      (2 * π)⁻¹ * exp (-2⁻¹ * r ^ 2) := by
  simp only [gaussianPDFReal_def, sub_zero, NNReal.coe_one, mul_one]
  rw [mul_mul_mul_comm, ← mul_inv, mul_self_sqrt (by positivity), ← exp_add]
  congr 2
  linear_combination (-2⁻¹ * r ^ 2) * sin_sq_add_cos_sq θ

/-- The angles with `|cos θ| ≤ k |sin θ|` are those with `|cos θ| ≤ sin (arctan k)`. -/
private theorem abs_cos_le_mul_abs_sin_iff {k : ℝ} (hk : 0 ≤ k) (θ : ℝ) :
    |cos θ| ≤ k * |sin θ| ↔ |cos θ| ≤ sin (arctan k) := by
  have hs : 0 ≤ sin (arctan k) := sin_arctan_nonneg.2 hk
  rw [← sq_le_sq₀ (abs_nonneg _) (by positivity), ← sq_le_sq₀ (abs_nonneg _) hs, mul_pow,
    sq_abs, sq_abs, sin_arctan, div_pow, sq_sqrt (by positivity), sin_sq,
    le_div_iff₀ (by positivity)]
  constructor <;> intro h <;> nlinarith

/-- The angles in `(-π, π)` with `|cos θ| ≤ k |sin θ|` form two arcs of half-width `arctan k`,
centered at `±π / 2`. -/
private theorem angle_set_eq {k : ℝ} (hk : 0 ≤ k) :
    {θ : ℝ | |cos θ| ≤ k * |sin θ|} ∩ Ioo (-π) π =
      Icc (π / 2 - arctan k) (π / 2 + arctan k) ∪
        Icc (-(π / 2 + arctan k)) (-(π / 2 - arctan k)) := by
  set a := arctan k with ha
  have ha0 : 0 ≤ a := arctan_nonneg.2 hk
  have ha1 : a < π / 2 := arctan_lt_pi_div_two k
  have hmem : ∀ ψ ∈ Icc (0 : ℝ) π, |cos ψ| ≤ sin a ↔ π / 2 - a ≤ ψ ∧ ψ ≤ π / 2 + a := by
    intro ψ hψ
    have h1 : π / 2 - a ∈ Icc (0 : ℝ) π := ⟨by linarith, by linarith⟩
    have h2 : π / 2 + a ∈ Icc (0 : ℝ) π := ⟨by linarith, by linarith⟩
    have e1 : -sin a = cos (π / 2 + a) := by rw [add_comm, cos_add_pi_div_two]
    rw [abs_le, e1, ← cos_pi_div_two_sub, strictAntiOn_cos.le_iff_ge h2 hψ,
      strictAntiOn_cos.le_iff_ge hψ h1, and_comm]
  ext θ
  simp only [mem_inter_iff, mem_ofPred_eq, mem_Ioo, mem_union, mem_Icc]
  rw [abs_cos_le_mul_abs_sin_iff hk, ← ha]
  constructor
  · rintro ⟨h, h1, h2⟩
    rw [← cos_abs] at h
    have := (hmem |θ| ⟨abs_nonneg _, abs_le.2 ⟨by linarith, by linarith⟩⟩).1 h
    rcases abs_cases θ with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] at this
    · exact Or.inl this
    · exact Or.inr ⟨by linarith, by linarith⟩
  · intro h
    have hθ : π / 2 - a ≤ |θ| ∧ |θ| ≤ π / 2 + a := by
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [abs_of_nonneg (by linarith)]
        exact ⟨h1, h2⟩
      · rw [abs_of_neg (by linarith)]
        exact ⟨by linarith, by linarith⟩
    have hb := abs_lt.1 (show |θ| < π by linarith)
    refine ⟨?_, by linarith, by linarith⟩
    rw [← cos_abs]
    exact (hmem |θ| ⟨abs_nonneg _, by linarith⟩).2 hθ

/-- The angles in `(-π, π)` with `|cos θ| ≤ k |sin θ|` have total length `4 arctan k`. -/
private theorem volume_angle_set {k : ℝ} (hk : 0 ≤ k) :
    volume ({θ : ℝ | |cos θ| ≤ k * |sin θ|} ∩ Ioo (-π) π) = ENNReal.ofReal (4 * arctan k) := by
  have ha0 : 0 ≤ arctan k := arctan_nonneg.2 hk
  have ha1 : arctan k < π / 2 := arctan_lt_pi_div_two k
  rw [angle_set_eq hk, measure_union _ measurableSet_Icc, Real.volume_Icc, Real.volume_Icc,
    ← ENNReal.ofReal_add (by linarith) (by linarith)]
  · congr 1
    ring
  · refine Set.disjoint_left.2 fun θ h1 h2 => ?_
    linarith [h1.1, h2.2]

/-- The radial factor `r exp (-r ^ 2 / 2) / (2π)` of the planar Gaussian density integrates to
`1 / (2π)`. -/
private theorem lintegral_radial :
    ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal ((2 * π)⁻¹ * (r * exp (-2⁻¹ * r ^ 2))) =
      ENNReal.ofReal (2 * π)⁻¹ := by
  rw [← ofReal_integral_eq_lintegral_ofReal, integral_const_mul,
    integral_Ioi_mul_exp_neg_mul_sq (by norm_num)]
  · norm_num
  · exact ((integrable_mul_exp_neg_mul_sq (by norm_num)).const_mul _).integrableOn
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun r hr => ?_)
    have : 0 < r := hr
    positivity

/-- **The planar angle law.** For independent standard Gaussians `Z₁` and `Z₂`, the event
`|Z₁| ≤ k |Z₂|` has probability `(2 / π) arctan k`. -/
theorem gaussianReal_prod_setOf_abs_le_mul_abs {k : ℝ} (hk : 0 ≤ k) :
    ((gaussianReal 0 1).prod (gaussianReal 0 1)) {p : ℝ × ℝ | |p.1| ≤ k * |p.2|} =
      ENNReal.ofReal (2 / π * arctan k) := by
  set A : Set (ℝ × ℝ) := {p | |p.1| ≤ k * |p.2|} with hA
  have hAm : MeasurableSet A := measurableSet_le (by fun_prop) (by fun_prop)
  set B : Set ℝ := {θ | |cos θ| ≤ k * |sin θ|} with hB
  have hBm : MeasurableSet B := measurableSet_le (by fun_prop) (by fun_prop)
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
    prod_withDensity (measurable_gaussianPDF 0 1) (measurable_gaussianPDF 0 1),
    withDensity_apply _ hAm, ← Measure.volume_eq_prod, ← lintegral_indicator hAm,
    ← lintegral_comp_polarCoord_symm]
  have hint : ∀ p ∈ polarCoord.target,
      ENNReal.ofReal p.1 • A.indicator
          (fun z => gaussianPDF 0 1 z.1 * gaussianPDF 0 1 z.2) (polarCoord.symm p) =
        ENNReal.ofReal ((2 * π)⁻¹ * (p.1 * exp (-2⁻¹ * p.1 ^ 2))) * B.indicator 1 p.2 := by
    rintro ⟨r, θ⟩ ⟨hr, -⟩
    have hr : 0 < r := hr
    have hiff : (r * cos θ, r * sin θ) ∈ A ↔ θ ∈ B := by
      simp only [hA, hB, mem_ofPred_eq, abs_mul, abs_of_pos hr]
      rw [mul_left_comm, mul_le_mul_iff_right₀ hr]
    simp only [polarCoord_symm_apply, smul_eq_mul]
    by_cases hθ : θ ∈ B
    · rw [indicator_of_mem (hiff.2 hθ), indicator_of_mem hθ, Pi.one_apply, mul_one,
        gaussianPDF, gaussianPDF, ← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _),
        gaussianPDFReal_mul_polar, ← ENNReal.ofReal_mul hr.le]
      congr 1
      ring
    · rw [indicator_of_notMem (mt hiff.1 hθ), indicator_of_notMem hθ, mul_zero, mul_zero]
  rw [setLIntegral_congr_fun polarCoord.open_target.measurableSet hint,
    polarCoord_target, Measure.volume_eq_prod, ← Measure.prod_restrict,
    lintegral_prod_mul (f := fun r => ENNReal.ofReal ((2 * π)⁻¹ * (r * exp (-2⁻¹ * r ^ 2))))
      (g := B.indicator 1) (by fun_prop) ((measurable_one.indicator hBm).aemeasurable),
    lintegral_radial, lintegral_indicator_one hBm, Measure.restrict_apply hBm,
    volume_angle_set hk, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp
  ring

/-- `gaussianReal 0 s` is the image of the standard Gaussian under `x ↦ √s x`. -/
private theorem gaussianReal_map_sqrt_mul (s : ℝ≥0) :
    (gaussianReal 0 1).map (fun x => √(s : ℝ) * x) = gaussianReal 0 s := by
  rw [gaussianReal_map_const_mul, mul_zero]
  congr 1
  ext
  simp

/-- **The planar angle law for any variances.** For independent centered Gaussians `X` and `Y`
of variances `s ≠ 0` and `r`, the event `|X| ≤ k |Y|` has probability
`(2 / π) arctan (k √r / √s)`. -/
theorem gaussianReal_prod_setOf_abs_le_mul_abs_of_ne_zero {s r : ℝ≥0} (hs : s ≠ 0) {k : ℝ}
    (hk : 0 ≤ k) :
    ((gaussianReal 0 s).prod (gaussianReal 0 r)) {p : ℝ × ℝ | |p.1| ≤ k * |p.2|} =
      ENNReal.ofReal (2 / π * arctan (k * √(r : ℝ) / √(s : ℝ))) := by
  have hs' : 0 < √(s : ℝ) := sqrt_pos.2 (by positivity)
  rw [← gaussianReal_map_sqrt_mul s, ← gaussianReal_map_sqrt_mul r,
    Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    Measure.map_apply (by fun_prop) (measurableSet_le (by fun_prop) (by fun_prop))]
  have hpre : Prod.map (fun x => √(s : ℝ) * x) (fun x => √(r : ℝ) * x) ⁻¹'
      {p : ℝ × ℝ | |p.1| ≤ k * |p.2|} =
        {p : ℝ × ℝ | |p.1| ≤ k * √(r : ℝ) / √(s : ℝ) * |p.2|} := by
    ext p
    simp only [mem_preimage, Prod.map_fst, Prod.map_snd, mem_ofPred_eq, abs_mul,
      abs_of_nonneg (sqrt_nonneg _)]
    rw [div_mul_eq_mul_div, le_div_iff₀ hs']
    constructor <;> intro h <;> linarith
  rw [hpre, gaussianReal_prod_setOf_abs_le_mul_abs (by positivity)]

/-! ### Sheppard's bound -/

/-- A threshold between two values lies within half their gap of their midpoint. -/
private theorem abs_add_sub_two_mul_le_of_mem_uIoc {t x y : ℝ} (h : t ∈ Ι x y) :
    |x + y - 2 * t| ≤ |y - x| := by
  rw [mem_uIoc] at h
  refine abs_le.2 ⟨?_, ?_⟩ <;> rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rcases abs_cases (y - x) with ⟨h3, _⟩ | ⟨h3, _⟩ <;> rw [h3] <;> linarith

/-- **Anderson's inequality, conditioned.** If `X` is a centered Gaussian independent of `Y`,
shifting `X` by `c` does not increase the probability of `|X| ≤ |Y|`. -/
private theorem gaussianReal_prod_setOf_abs_sub_le_abs_le (s : ℝ≥0) (ν : Measure ℝ) [SFinite ν]
    (c : ℝ) :
    ((gaussianReal 0 s).prod ν) {p : ℝ × ℝ | |p.1 - c| ≤ |p.2|} ≤
      ((gaussianReal 0 s).prod ν) {p : ℝ × ℝ | |p.1| ≤ |p.2|} := by
  rw [Measure.prod_apply_symm (measurableSet_le (by fun_prop) (by fun_prop)),
    Measure.prod_apply_symm (measurableSet_le (by fun_prop) (by fun_prop))]
  refine lintegral_mono fun y => ?_
  have e1 : (fun x => (x, y)) ⁻¹' {p : ℝ × ℝ | |p.1 - c| ≤ |p.2|} =
      Icc (c - |y|) (c + |y|) := by
    ext x
    simp only [mem_preimage, mem_ofPred_eq, mem_Icc, abs_le]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  have e2 : (fun x => (x, y)) ⁻¹' {p : ℝ × ℝ | |p.1| ≤ |p.2|} = Icc (0 - |y|) (0 + |y|) := by
    ext x
    simp only [mem_preimage, mem_ofPred_eq, mem_Icc, zero_sub, zero_add]
    exact abs_le
  rw [e1, e2]
  exact gaussianReal_Icc_le 0 s c |y|

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Sheppard's bound, `arctan` form.** If `u` and `v` have equal norms and nonzero sum, a
threshold lies between `⟪u, X⟫` and `⟪v, X⟫`, for a standard Gaussian vector `X`, with
probability at most `(2 / π) arctan (‖v - u‖ / ‖u + v‖)`. -/
theorem measureReal_stdGaussian_mem_uIoc_le_arctan {u v : E} (huv : ‖u‖ = ‖v‖)
    (hne : u + v ≠ 0) (t : ℝ) :
    (stdGaussian E).real {x | t ∈ Ι ⟪u, x⟫ ⟪v, x⟫} ≤ 2 / π * arctan (‖v - u‖ / ‖u + v‖) := by
  have hba : ⟪u + v, v - u⟫ = 0 := by
    rw [inner_add_left, inner_sub_right, inner_sub_right, real_inner_self_eq_norm_sq,
      real_inner_self_eq_norm_sq, real_inner_comm u v, huv]
    ring
  set S : Set (ℝ × ℝ) := {p | |p.1 - 2 * t| ≤ |p.2|} with hS
  have hSm : MeasurableSet S := measurableSet_le (by fun_prop) (by fun_prop)
  have hsub : {x | t ∈ Ι ⟪u, x⟫ ⟪v, x⟫} ⊆ (fun x => (⟪u + v, x⟫, ⟪v - u, x⟫)) ⁻¹' S := by
    intro x hx
    simpa only [mem_preimage, hS, mem_ofPred_eq, inner_add_left, inner_sub_left] using
      abs_add_sub_two_mul_le_of_mem_uIoc hx
  have hpair : Measurable fun x : E => (⟪u + v, x⟫, ⟪v - u, x⟫) := by fun_prop
  have hs0 : ‖u + v‖₊ ^ 2 ≠ 0 := pow_ne_zero 2 (nnnorm_ne_zero_iff.2 hne)
  have hsqrt : ∀ w : E, √((‖w‖₊ ^ 2 : ℝ≥0) : ℝ) = ‖w‖ := fun w => by
    rw [NNReal.coe_pow, coe_nnnorm, sqrt_sq (norm_nonneg w)]
  calc (stdGaussian E).real {x | t ∈ Ι ⟪u, x⟫ ⟪v, x⟫}
      ≤ (stdGaussian E).real ((fun x => (⟪u + v, x⟫, ⟪v - u, x⟫)) ⁻¹' S) := measureReal_mono hsub
    _ = ((gaussianReal 0 (‖u + v‖₊ ^ 2)).prod (gaussianReal 0 (‖v - u‖₊ ^ 2))).real S := by
        rw [← map_measureReal_apply hpair hSm, stdGaussian_map_inner_prod hba]
    _ ≤ ((gaussianReal 0 (‖u + v‖₊ ^ 2)).prod (gaussianReal 0 (‖v - u‖₊ ^ 2))).real
          {p : ℝ × ℝ | |p.1| ≤ 1 * |p.2|} := by
        simp only [one_mul]
        exact ENNReal.toReal_mono (measure_ne_top _ _)
          (gaussianReal_prod_setOf_abs_sub_le_abs_le _ _ _)
    _ = 2 / π * arctan (‖v - u‖ / ‖u + v‖) := by
        rw [measureReal_def, gaussianReal_prod_setOf_abs_le_mul_abs_of_ne_zero hs0 zero_le_one,
          hsqrt, hsqrt, one_mul, ENNReal.toReal_ofReal]
        have := arctan_nonneg.2 (by positivity : 0 ≤ ‖v - u‖ / ‖u + v‖)
        positivity

/-- **Sheppard's bound.** If `u` and `v` have equal norms, a threshold lies between `⟪u, X⟫` and
`⟪v, X⟫`, for a standard Gaussian vector `X`, with probability at most `angle u v / π`. -/
theorem measureReal_stdGaussian_mem_uIoc_le_angle {u v : E} (huv : ‖u‖ = ‖v‖) (t : ℝ) :
    (stdGaussian E).real {x | t ∈ Ι ⟪u, x⟫ ⟪v, x⟫} ≤ InnerProductGeometry.angle u v / π := by
  by_cases hne : u + v = 0
  · by_cases hu : u = 0
    · have hv : v = 0 := by rw [← norm_eq_zero, ← huv, hu, norm_zero]
      simp only [hu, hv, inner_zero_left, uIoc_of_le le_rfl, Ioc_self, mem_empty_iff_false,
        ofPred_false, measureReal_empty]
      exact div_nonneg (InnerProductGeometry.angle_nonneg _ _) pi_pos.le
    · rw [eq_neg_of_add_eq_zero_right hne, InnerProductGeometry.angle_self_neg_of_ne_zero hu,
        div_self pi_ne_zero]
      exact measureReal_le_one
  · rw [InnerProductGeometry.angle_eq_two_mul_arctan huv hne]
    refine (measureReal_stdGaussian_mem_uIoc_le_arctan huv hne t).trans_eq ?_
    ring

end ProbabilityTheory
