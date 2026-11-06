/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Algebra.Module.ZLattice.CoefficientPairing
public import Complexity.Foundations.Probability.Gaussian.CoefficientBounds
public import Complexity.Foundations.Probability.Gaussian.Projection
public import Complexity.Foundations.MeasureTheory.Measure.TotalVariation.Mixture
public import Complexity.Probability.PMF

/-!
# Regev's actual single-sample lattice experiment

## Main definitions

* `Cslib.Crypto.Regev.latticeSample`: draw the actual lattice discrete Gaussian and independent
  scalar Gaussian noise, then return coefficients modulo `p` and the noisy inner product modulo one.
* `Cslib.Crypto.Regev.lweSample`: the comparison sample with uniform coefficients and scalar
  Gaussian noise modulo one, for a fixed secret.

## Main results

* `Cslib.Crypto.Regev.latticeSample_spec_of_dual_mass_le`: the actual dual mass and residual
  bounds give the source variance bound and full-L1 error `4ε + 2ε / (1 - ε)`.
* `Cslib.Crypto.Regev.latticeSample_spec_of_gap`: a quantitative dual gap discharges the mass bound.
* `Cslib.Crypto.Regev.latticeSample_dual_eq`: zero residual retains the actual coefficient marginal.

## References

[Regev2009], Lemma 3.11 and equation (12), printed pages 23–24 of the May 2, 2009 author version.
These are analytic probability measures. No efficient sampler, closest-vector oracle, finite
precision implementation, or quantum reduction is provided. The scalar input noise has variance
`α² / (4π)`, as in the source's standard deviation `α / (2√π)`. The comparison variance is
`β² / (2π)`, where `β² = (r‖x-w‖/p)² + α²/2 ≤ α²`. The explicit error accounting uses the
source's full-L1 convention (equation (5), printed page 13); it is at most `8ε` for `ε < 1/2`.
The existing binary decision-LWE
experiment has a different carrier and is not substituted for this real-mod-one experiment.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Module ZLattice
open scoped ENNReal NNReal Pointwise RealInnerProductSpace

namespace Cslib.Crypto.Regev

private theorem toMeasure_bind_fintype {A B : Type*} [Fintype A] [MeasurableSpace B]
    (q : PMF A) (k : A → PMF B) :
    (q.bind k).toMeasure = ∑ a, (q a).toNNReal • (k a).toMeasure := by
  ext s hs
  rw [PMF.toMeasure_bind_apply q k s hs]
  simp [Measure.finsetSum_apply, tsum_fintype, ENNReal.coe_toNNReal (q.apply_ne_top _)]

private theorem toMeasure_eq_sum {A : Type*} [Fintype A] [MeasurableSpace A]
    (q : PMF A) : q.toMeasure = ∑ a, (q a).toNNReal • Measure.dirac a := by
  have h := toMeasure_bind_fintype q (fun a ↦ PMF.pure a)
  simpa only [PMF.bind_pure, PMF.toMeasure_pure] using h

private theorem map_prod_sum {A X Y Z : Type*} [Fintype A]
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (q : A → ℝ≥0) (μ : A → Measure X) (ν : Measure Y) [SFinite ν]
    (f : X × Y → Z) (hf : Measurable f) :
    ((∑ a, q a • μ a).prod ν).map f =
      ∑ a, q a • ((μ a).prod ν).map f := by
  rw [← Measure.sum_fintype, Measure.prod_sum_left, Measure.map_sum hf.aemeasurable,
    Measure.sum_fintype]
  congr 1
  ext a
  rw [Measure.prod_smul_left, Measure.map_smul _ hf.aemeasurable]

private theorem sample_parameters {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r α q : ℝ) (hr : 0 < r) (hα : 0 < α) (hq : 0 < q) (d : E)
    (hd : ‖d‖ ≤ α * q / (Real.sqrt 2 * r)) :
    Real.sqrt (1 / r ^ 2 + (‖q⁻¹ • d‖ / (α / Real.sqrt 2)) ^ 2) ≤
        1 / (r / Real.sqrt 2) ∧
      (r * ‖q⁻¹ • d‖) ^ 2 + α ^ 2 / 2 ≤ α ^ 2 := by
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hn : ‖q⁻¹ • d‖ = ‖d‖ / q := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hq)]
    ring
  have hnle : ‖q⁻¹ • d‖ ≤ α / (Real.sqrt 2 * r) := by
    rw [hn]
    apply (div_le_iff₀ hq).mpr
    convert hd using 1; ring
  have hratio : ‖q⁻¹ • d‖ / (α / Real.sqrt 2) ≤ 1 / r := by
    apply (div_le_iff₀ (div_pos hα hs)).mpr
    convert hnle using 1; ring
  have hratio2 : (‖q⁻¹ • d‖ / (α / Real.sqrt 2)) ^ 2 ≤ (1 / r) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).mpr hratio
  constructor
  · apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [Real.sq_sqrt (by positivity)]
    have ht : (1 / (r / Real.sqrt 2)) ^ 2 = 2 / r ^ 2 := by
      rw [one_div_div, div_pow, hs2]
    rw [ht]
    simp only [one_div_pow] at hratio2
    rw [show 2 / r ^ 2 = 1 / r ^ 2 + 1 / r ^ 2 by ring]
    linarith [hratio2]
  · have hz : r * ‖q⁻¹ • d‖ ≤ α / Real.sqrt 2 := by
      have h := (le_div_iff₀ (mul_pos hs hr)).mp hnle
      apply (le_div_iff₀ hs).mpr
      nlinarith
    have hz2 := (sq_le_sq₀ (by positivity) (div_pos hα hs).le).mpr hz
    rw [div_pow, hs2] at hz2
    linarith

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι] [DecidableEq ι]
variable (L : Submodule ℤ E) [DiscreteTopology L]
variable (b : Module.Basis ι ℤ L) (p : ℕ) [NeZero p]

/-- The source experiment takes `x`, not the dual-lattice witness used to specify its secret. -/
@[expose] def latticeSample (r α : ℝ) (hr : 0 < r) (x : E) :
    Measure ((ι → ZMod p) × UnitAddCircle) :=
  ((discreteGaussian L r hr 0).toMeasure.prod
    (gaussianReal 0 ((α ^ 2 / (4 * Real.pi)).toNNReal))).map
      (fun ve ↦ (coefficientMod L b p ve.1,
        ((⟪x, (ve.1 : E)⟫ / p + ve.2 : ℝ) : UnitAddCircle)))

/-- A real-mod-one LWE sample with a fixed secret and the stated scalar Gaussian variance. -/
@[expose] def lweSample (secret : ι → ZMod p) (variance : ℝ≥0) :
    Measure ((ι → ZMod p) × UnitAddCircle) :=
  ((Cslib.Probability.PMF.uniformOfFintype (ι → ZMod p)).toMeasure.prod
    (gaussianReal 0 variance)).map
    (fun ae ↦ (ae.1, ZMod.toAddCircle (∑ i, ae.1 i * secret i) +
      (ae.2 : UnitAddCircle)))

variable [IsZLattice ℝ L]

local instance : DiscreteTopology ↥((p : ℝ) • L) :=
  DiscreteTopology.of_subset inferInstance (natCast_smul_le L p)

local instance : IsZLattice ℝ ((p : ℝ) • L) where
  span_top := by
    rw [Submodule.coe_pointwise_smul, ← Submodule.smul_span, IsZLattice.span_top]
    ext x
    refine ⟨fun _ ↦ trivial, fun _ ↦ ?_⟩
    have hp : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)
    rw [show x = (p : ℝ) • ((p : ℝ)⁻¹ • x) by simp [hp]]
    exact Submodule.smul_mem_pointwise_smul _ _ _ (by trivial)

omit [MeasurableSpace E] [BorelSpace E] [DecidableEq ι] [IsZLattice ℝ L] in
private theorem discreteGaussian_eq_bind (r : ℝ) (hr : 0 < r) :
    discreteGaussian L r hr 0 =
      ((discreteGaussian L r hr 0).map (coefficientMod L b p)).bind (fun a ↦
        (discreteGaussian ((p : ℝ) • L) r hr (-(coefficientLift L b p a : E))).map
          (fun w ↦ Submodule.inclusion (natCast_smul_le L p) w +
            coefficientLift L b p a)) := by
  have h := congrArg (PMF.map Prod.snd)
    (map_coefficientMod_pair_discreteGaussian L b p r hr 0)
  simp only [PMF.map_comp, PMF.map_bind, Function.comp_def, zero_sub] at h
  change (discreteGaussian L r hr 0).map id = _ at h
  rw [PMF.map_id] at h
  exact h

/-- Both random draws in the actual sample are normalized probability measures. -/
instance isProbabilityMeasure_latticeSample (r α : ℝ) (hr : 0 < r) (x : E) :
    IsProbabilityMeasure (latticeSample L b p r α hr x) := by
  unfold latticeSample
  infer_instance

/-- The uniform coefficient and Gaussian comparison experiment is a probability measure. -/
instance isProbabilityMeasure_lweSample (secret : ι → ZMod p) (variance : ℝ≥0) :
    IsProbabilityMeasure (lweSample p secret variance) := by
  unfold lweSample
  infer_instance

private theorem latticeSample_eq_sum (r α : ℝ) (hr : 0 < r) (x : E) :
    latticeSample L b p r α hr x =
      ∑ a : ι → ZMod p,
        (((discreteGaussian L r hr 0).map (coefficientMod L b p)) a).toNNReal •
          (((discreteGaussian ((p : ℝ) • L) r hr
            (-(coefficientLift L b p a : E))).toMeasure.prod
              (gaussianReal 0 ((α ^ 2 / (4 * Real.pi)).toNNReal))).map
                (fun we ↦ (a, ((⟪x, (we.1 : E) + coefficientLift L b p a⟫ / p +
                  we.2 : ℝ) : UnitAddCircle)))) := by
  have hc : Measurable (coefficientMod L b p) := measurable_of_countable _
  unfold latticeSample
  conv_lhs => rw [discreteGaussian_eq_bind L b p r hr, toMeasure_bind_fintype,
    map_prod_sum _ _ _ _ (by fun_prop)]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  rw [← PMF.toMeasure_map _ _ (measurable_of_countable _)]
  have hprod := Measure.map_prod_map
    (discreteGaussian ((p : ℝ) • L) r hr (-(coefficientLift L b p a : E))).toMeasure
    (gaussianReal 0 ((α ^ 2 / (4 * Real.pi)).toNNReal))
    (measurable_of_countable (fun w ↦ Submodule.inclusion (natCast_smul_le L p) w +
      coefficientLift L b p a)) measurable_id
  rw [Measure.map_id] at hprod
  rw [hprod, Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext we
  have hcoeff : coefficientMod L b p
      (Submodule.inclusion (natCast_smul_le L p) we.1 + coefficientLift L b p a) = a :=
    (coefficientFiberEquiv L b p a we.1).property
  exact Prod.ext hcoeff rfl

private theorem lweSample_eq_sum (secret : ι → ZMod p) (variance : ℝ≥0) :
    lweSample p secret variance =
      ∑ a : ι → ZMod p,
        (Cslib.Probability.PMF.uniformOfFintype (ι → ZMod p) a).toNNReal •
          (gaussianReal 0 variance).map
            (fun e : ℝ ↦ (a, ZMod.toAddCircle (∑ i, a i * secret i) + (e : UnitAddCircle))) := by
  unfold lweSample
  rw [toMeasure_eq_sum, map_prod_sum _ _ _ _ (by fun_prop)]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  rw [Measure.dirac_prod, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [DecidableEq ι]
  [DiscreteTopology L] [IsZLattice ℝ L] in
private theorem phase_eq (x : E)
    (w : LinearMap.BilinForm.dualSubmodule (innerₗ E) L) (v : L) (e : ℝ) :
    ZMod.toAddCircle (∑ i, coefficientMod L b p v i *
      ((LinearMap.BilinForm.dualSubmodulePairing (innerₗ E) w (b i) : ℤ) : ZMod p)) +
        ((⟪(p : ℝ)⁻¹ • (x - (w : E)), (v : E)⟫ + e : ℝ) : UnitAddCircle) =
      ((⟪x, (v : E)⟫ / p + e : ℝ) : UnitAddCircle) := by
  rw [toAddCircle_coefficientMod_pairing]
  change ((⟪(w : E), (v : E)⟫ / p : ℝ) : UnitAddCircle) + _ = _
  rw [← AddCircle.coe_add]
  congr 1
  simp only [real_inner_smul_left, inner_sub_left]
  ring

omit [MeasurableSpace E] [BorelSpace E] in
private theorem gaussianMass_mono (D : Submodule ℤ E) [DiscreteTopology D]
    {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) : gaussianMass D s 0 ≤ gaussianMass D t 0 :=
  (summable_gaussianWeight D s hs 0).tsum_le_tsum
    (fun _ ↦ gaussianWeight_le_of_le hs hst _) (summable_gaussianWeight D t (hs.trans_le hst) 0)

omit [DecidableEq ι] in
private theorem component_bound (r σ : ℝ) (hr : 0 < r) (hσ : 0 < σ) (x : E)
    (w : LinearMap.BilinForm.dualSubmodule (innerₗ E) L) (a : ι → ZMod p)
    (ε : ℝ) (hε : 0 ≤ ε) (hεhalf : ε < 1 / 2)
    (hdual : gaussianMass (LinearMap.BilinForm.dualSubmodule (innerₗ E) ((p : ℝ) • L))
      (Real.sqrt (1 / r ^ 2 + (‖(p : ℝ)⁻¹ • (x - (w : E))‖ / σ) ^ 2)) 0 - 1 ≤ ε) :
    tvDist
      (((discreteGaussian ((p : ℝ) • L) r hr
        (-(coefficientLift L b p a : E))).toMeasure.prod
          (gaussianReal 0 ((σ ^ 2 / (2 * Real.pi)).toNNReal))).map
            (fun ve ↦ (a, ((⟪x, (ve.1 : E) + coefficientLift L b p a⟫ / p +
              ve.2 : ℝ) : UnitAddCircle))))
      ((gaussianReal 0 ((((r * ‖(p : ℝ)⁻¹ • (x - (w : E))‖) ^ 2 + σ ^ 2) /
        (2 * Real.pi)).toNNReal)).map (fun e : ℝ ↦ (a,
          ZMod.toAddCircle (∑ i, a i *
            ((LinearMap.BilinForm.dualSubmodulePairing (innerₗ E) w (b i) : ℤ) : ZMod p)) +
              (e : UnitAddCircle)))) ≤ 4 * ε := by
  let u : E := coefficientLift L b p a
  let z := (p : ℝ)⁻¹ • (x - (w : E))
  let μ := (discreteGaussian ((p : ℝ) • L) r hr (-u)).toMeasure
  let ν := gaussianReal 0 ((σ ^ 2 / (2 * Real.pi)).toNNReal)
  let F : ℝ → (ι → ZMod p) × UnitAddCircle := fun e ↦ (a,
    ZMod.toAddCircle (∑ i, a i *
      ((LinearMap.BilinForm.dualSubmodulePairing (innerₗ E) w (b i) : ℤ) : ZMod p)) +
        (e : UnitAddCircle))
  have hF : Measurable F := by fun_prop
  have hbound := tvDist_conv_map_inner_discreteGaussian_le_of_dual_mass_le
    ((p : ℝ) • L) r σ hr hσ u z ε hε hεhalf hdual
  have hmap := tvDist_map_le
    (Measure.conv ((μ.map (fun v : ↥((p : ℝ) • L) ↦ (v : E) + u)).map
      (fun y ↦ ⟪z, y⟫)) ν)
    (gaussianReal 0 ((((r * ‖z‖) ^ 2 + σ ^ 2) / (2 * Real.pi)).toNNReal)) hF
  have hi : (Measure.conv ((μ.map (fun v : ↥((p : ℝ) • L) ↦ (v : E) + u)).map
      (fun y ↦ ⟪z, y⟫)) ν).map F =
      (μ.prod ν).map (fun ve ↦ (a, ((⟪x, (ve.1 : E) + u⟫ / p + ve.2 : ℝ) :
        UnitAddCircle))) := by
    rw [Measure.conv, Measure.map_map hF (by fun_prop),
      Measure.map_map (by fun_prop) (by fun_prop)]
    have hp := Measure.map_prod_map μ ν
      (show Measurable (fun v : ↥((p : ℝ) • L) ↦ ⟪z, (v : E) + u⟫) by fun_prop)
      measurable_id
    rw [Measure.map_id] at hp
    simp only [Function.comp_def]
    rw [hp, Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
    funext ve
    apply Prod.ext
    · rfl
    change _ + _ = _
    let v : L := Submodule.inclusion (natCast_smul_le L p) ve.1 + coefficientLift L b p a
    have hv : coefficientMod L b p v = a := (coefficientFiberEquiv L b p a ve.1).property
    have hh := phase_eq L b p x w v ve.2
    rw [hv] at hh
    exact hh
  rw [hi] at hmap
  exact hmap.trans hbound

private theorem joint_bound (r α : ℝ) (hr : 0 < r) (hα : 0 < α) (x : E)
    (w : LinearMap.BilinForm.dualSubmodule (innerₗ E) L)
    (ε : ℝ) (hε : 0 ≤ ε) (hεhalf : ε < 1 / 2)
    (hdual : gaussianMass (LinearMap.BilinForm.dualSubmodule (innerₗ E) ((p : ℝ) • L))
      (Real.sqrt (1 / r ^ 2 + (‖(p : ℝ)⁻¹ • (x - (w : E))‖ / (α / Real.sqrt 2)) ^ 2))
        0 - 1 ≤ ε) :
    tvDist (latticeSample L b p r α hr x)
      (lweSample p (fun i ↦
        ((LinearMap.BilinForm.dualSubmodulePairing (innerₗ E) w (b i) : ℤ) : ZMod p))
        ((((r * ‖(p : ℝ)⁻¹ • (x - (w : E))‖) ^ 2 + α ^ 2 / 2) /
          (2 * Real.pi)).toNNReal)) ≤ 4 * ε + 2 * ε / (1 - ε) := by
  let D := LinearMap.BilinForm.dualSubmodule (innerₗ E) ((p : ℝ) • L)
  have : DiscreteTopology D := discreteTopology_dualSubmodule ((p : ℝ) • L)
  have hσ : 0 < α / Real.sqrt 2 := div_pos hα (Real.sqrt_pos.mpr (by norm_num))
  have hσ2 : (α / Real.sqrt 2) ^ 2 = α ^ 2 / 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hnoise : (α / Real.sqrt 2) ^ 2 / (2 * Real.pi) = α ^ 2 / (4 * Real.pi) := by
    rw [hσ2]
    ring
  have hw : 1 / r ≤ Real.sqrt (1 / r ^ 2 +
      (‖(p : ℝ)⁻¹ • (x - (w : E))‖ / (α / Real.sqrt 2)) ^ 2) := by
    apply (sq_le_sq₀ (one_div_pos.mpr hr).le (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt (by positivity), div_pow, one_pow]
    exact le_add_of_nonneg_right (sq_nonneg _)
  have hm : gaussianMass D (1 / r) 0 - 1 ≤ ε :=
    (sub_le_sub_right (gaussianMass_mono D (one_div_pos.mpr hr) hw) 1).trans hdual
  have hweights := sum_abs_map_coefficientMod_discreteGaussian_sub_uniform_le
    L b p r hr 0 ε hε (by linarith) hm
  rw [latticeSample_eq_sum, lweSample_eq_sum]
  apply (tvDist_finsetSum_smul_le Finset.univ
    (fun a ↦ (((discreteGaussian L r hr 0).map (coefficientMod L b p)) a).toNNReal)
    (fun a ↦ (Cslib.Probability.PMF.uniformOfFintype (ι → ZMod p) a).toNNReal) _ _).trans
  simp only [probReal_univ, mul_one, ENNReal.coe_toNNReal_eq_toReal, Finset.sum_add_distrib]
  apply add_le_add
  · calc
      _ ≤ ∑ a : ι → ZMod p,
          (((discreteGaussian L r hr 0).map (coefficientMod L b p)) a).toReal * (4 * ε) := by
        apply Finset.sum_le_sum
        intro a _
        apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
        have hc := component_bound L b p r (α / Real.sqrt 2) hr hσ x w a ε hε hεhalf hdual
        rw [hnoise, hσ2] at hc
        exact hc
      _ = 4 * ε := by
        rw [← Finset.sum_mul, Cslib.Probability.PMF.sum_toReal, one_mul]
  · simpa only [Cslib.Probability.PMF.uniformOfFintype_apply, ENNReal.toReal_inv,
      ENNReal.toReal_natCast, one_div] using hweights

omit [DecidableEq ι] in
/-- At a dual-lattice input the phase is exact, but the coefficient marginal is still the
actual discrete-Gaussian marginal. Zero residual alone does not make that marginal uniform. -/
theorem latticeSample_dual_eq (r α : ℝ) (hr : 0 < r)
    (w : LinearMap.BilinForm.dualSubmodule (innerₗ E) L) :
    latticeSample L b p r α hr (w : E) =
      ((((discreteGaussian L r hr 0).map (coefficientMod L b p)).toMeasure).prod
        (gaussianReal 0 ((α ^ 2 / (4 * Real.pi)).toNNReal))).map
          (fun ae ↦ (ae.1, ZMod.toAddCircle (∑ i, ae.1 i *
            ((LinearMap.BilinForm.dualSubmodulePairing (innerₗ E) w (b i) : ℤ) : ZMod p)) +
              (ae.2 : UnitAddCircle))) := by
  have hc : Measurable (coefficientMod L b p) := measurable_of_countable _
  rw [← PMF.toMeasure_map _ _ hc]
  have hp := Measure.map_prod_map (discreteGaussian L r hr 0).toMeasure
    (gaussianReal 0 ((α ^ 2 / (4 * Real.pi)).toNNReal)) hc measurable_id
  rw [Measure.map_id] at hp
  rw [hp, Measure.map_map (by fun_prop) (by fun_prop)]
  unfold latticeSample
  congr 1
  funext ve
  apply Prod.ext
  · rfl
  · have hh := phase_eq L b p (w : E) w ve.1 ve.2
    simpa only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq,
      sub_self, smul_zero, inner_zero_left, zero_add] using hh.symm

/-- The source residual bound gives the stated Gaussian width and an explicit full-L1 bound
for the actual joint sample. The dual witness specifies the secret but is not sampled or passed
into `latticeSample`. Every positive modulus is allowed, in particular arbitrary `p ≥ 2`. -/
theorem latticeSample_spec_of_dual_mass_le (r α : ℝ) (hr : 0 < r) (hα : 0 < α) (x : E)
    (w : LinearMap.BilinForm.dualSubmodule (innerₗ E) L)
    (hres : ‖x - (w : E)‖ ≤ α * p / (Real.sqrt 2 * r))
    (ε : ℝ) (hε : 0 ≤ ε) (hεhalf : ε < 1 / 2)
    (hdual : gaussianMass (LinearMap.BilinForm.dualSubmodule (innerₗ E) ((p : ℝ) • L))
      (1 / (r / Real.sqrt 2)) 0 - 1 ≤ ε) :
    (r * ‖x - (w : E)‖ / p) ^ 2 + α ^ 2 / 2 ≤ α ^ 2 ∧
      tvDist (latticeSample L b p r α hr x)
        (lweSample p (fun i ↦
          ((LinearMap.BilinForm.dualSubmodulePairing (innerₗ E) w (b i) : ℤ) : ZMod p))
          ((((r * ‖x - (w : E)‖ / p) ^ 2 + α ^ 2 / 2) /
            (2 * Real.pi)).toNNReal)) ≤ 4 * ε + 2 * ε / (1 - ε) := by
  have hp : (0 : ℝ) < p := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne p))
  have hparams := sample_parameters r α p hr hα hp (x - (w : E)) hres
  have hn : r * ‖(p : ℝ)⁻¹ • (x - (w : E))‖ = r * ‖x - (w : E)‖ / p := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp)]
    ring
  constructor
  · simpa only [hn] using hparams.2
  · have : DiscreteTopology (LinearMap.BilinForm.dualSubmodule (innerₗ E) ((p : ℝ) • L)) :=
      discreteTopology_dualSubmodule ((p : ℝ) • L)
    have hh : gaussianMass (LinearMap.BilinForm.dualSubmodule (innerₗ E) ((p : ℝ) • L))
        (Real.sqrt (1 / r ^ 2 + (‖(p : ℝ)⁻¹ • (x - (w : E))‖ / (α / Real.sqrt 2)) ^ 2))
          0 - 1 ≤ ε :=
      (sub_le_sub_right (gaussianMass_mono _ (Real.sqrt_pos.mpr (by positivity)) hparams.1) 1).trans
        hdual
    simpa only [hn] using joint_bound L b p r α hr hα x w ε hε hεhalf hh

/-- The explicit dual-gap criterion supplies the actual dual mass premise in the single-sample
specification. The error remains the separately accounted convolution and marginal errors. -/
theorem latticeSample_spec_of_gap (r α : ℝ) (hr : 0 < r) (hα : 0 < α) (x : E)
    (w : LinearMap.BilinForm.dualSubmodule (innerₗ E) L)
    (hres : ‖x - (w : E)‖ ≤ α * p / (Real.sqrt 2 * r))
    (a : ℝ) (ha : 0 < a)
    (hgap : ∀ v : LinearMap.BilinForm.dualSubmodule (innerₗ E) ((p : ℝ) • L),
      v ≠ 0 → a ≤ ‖(v : E)‖)
    (ε : ℝ) (hε : 0 < ε) (hεhalf : ε < 1 / 2)
    (hnum : 2 ^ finrank ℝ E * Real.exp (-3 * Real.pi * r ^ 2 * a ^ 2 / 8) ≤
      ε / (1 + ε)) :
    (r * ‖x - (w : E)‖ / p) ^ 2 + α ^ 2 / 2 ≤ α ^ 2 ∧
      tvDist (latticeSample L b p r α hr x)
        (lweSample p (fun i ↦
          ((LinearMap.BilinForm.dualSubmodulePairing (innerₗ E) w (b i) : ℤ) : ZMod p))
          ((((r * ‖x - (w : E)‖ / p) ^ 2 + α ^ 2 / 2) /
            (2 * Real.pi)).toNNReal)) ≤ 4 * ε + 2 * ε / (1 - ε) := by
  apply latticeSample_spec_of_dual_mass_le L b p r α hr hα x w hres ε hε.le hεhalf
  apply gaussianMass_dual_sub_one_le_of_gap ((p : ℝ) • L)
    (r / Real.sqrt 2) (by positivity) a ha hgap ε hε
  convert hnum using 1
  congr 2
  rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

/-- With the source range `0 ≤ ε < 1/2`, the two separately proved errors total at most `8ε`. -/
theorem sample_error_le (ε : ℝ) (hε : 0 ≤ ε) (hεhalf : ε < 1 / 2) :
    4 * ε + 2 * ε / (1 - ε) ≤ 8 * ε := by
  have hd : 0 < 1 - ε := by linarith
  have h : 2 * ε / (1 - ε) ≤ 4 * ε := by
    apply (div_le_iff₀ hd).mpr
    nlinarith
  linarith

end Cslib.Crypto.Regev
