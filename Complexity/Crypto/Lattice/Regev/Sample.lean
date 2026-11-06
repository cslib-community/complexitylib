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

## References

[Regev2009], Lemma 3.11 and equation (12), printed pages 23–24 of the May 2, 2009 author version.
These are analytic probability measures. No efficient sampler, closest-vector oracle, finite
precision implementation, or quantum reduction is provided. The existing binary decision-LWE
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
  ((Cslib.Probability.PMF.uniformOfFintype (ι → ZMod p)).toMeasure.prod (gaussianReal 0 variance)).map
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
  conv_lhs => arg 2; arg 2; rw [← Measure.map_id (μ := gaussianReal 0 ((α ^ 2 / (4 * Real.pi)).toNNReal))]
  rw [Measure.map_prod_map _ _ (measurable_of_countable _) measurable_id,
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext we
  have hcoeff : coefficientMod L b p
      (Submodule.inclusion (natCast_smul_le L p) we.1 + coefficientLift L b p a) = a :=
    (coefficientFiberEquiv L b p a we.1).property
  simp only [Function.comp_apply, Prod.map_apply, id_eq, hcoeff]
  rfl

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

private theorem phase_eq (x : E)
    (w : LinearMap.BilinForm.dualSubmodule (innerₗ E) L) (v : L) (e : ℝ) :
    ZMod.toAddCircle (∑ i, coefficientMod L b p v i *
      (((innerₗ E).dualSubmodulePairing w (b i) : ℤ) : ZMod p)) +
        ((⟪(p : ℝ)⁻¹ • (x - (w : E)), (v : E)⟫ + e : ℝ) : UnitAddCircle) =
      ((⟪x, (v : E)⟫ / p + e : ℝ) : UnitAddCircle) := by
  rw [toAddCircle_coefficientMod_pairing]
  change ((⟪(w : E), (v : E)⟫ / p : ℝ) : UnitAddCircle) + _ = _
  rw [← AddCircle.coe_add]
  congr 1
  simp only [real_inner_smul_left, inner_sub_left]
  ring

private theorem gaussianMass_mono (D : Submodule ℤ E) [DiscreteTopology D]
    {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) : gaussianMass D s 0 ≤ gaussianMass D t 0 :=
  (summable_gaussianWeight D s hs 0).tsum_le_tsum
    (fun v ↦ gaussianWeight_le_of_le hs hst _) (summable_gaussianWeight D t (hs.trans_le hst) 0)

end Cslib.Crypto.Regev
