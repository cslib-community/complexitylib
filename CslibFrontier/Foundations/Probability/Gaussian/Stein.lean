/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate (Mathlib, a new file `Mathlib/Probability/Distributions/Gaussian/`
-- `Stein.lean`)

public import CslibFrontier.Init
public import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Gaussian integration by parts

**Stein's lemma**: for a real Gaussian `x ∼ N(μ, v)` and a differentiable `f` with `f`,
`(x - μ) f` and `f'` integrable, `E[(x - μ) f x] = v E[f' x]` (`integral_sub_mul_gaussianReal`).
For `v ≠ 0` this is integration by parts on the line against the density `φ`, whose derivative is
`φ' x = -((x - μ) / v) φ x` (`hasDerivAt_gaussianPDFReal`); for `v = 0` both sides vanish. Every
polynomial is integrable under a real Gaussian (`integrable_eval_gaussianReal`), so the lemma
applies to all polynomials (`integral_sub_mul_eval_gaussianReal`); this is the computation behind
the Hermite polynomials of [O'Donnell, §11.2][ODonnell2014].

## Main results

* `ProbabilityTheory.integrable_gaussianReal_iff_integrable_mul_gaussianPDFReal`: integrability
  against a nondegenerate real Gaussian is Lebesgue integrability of the product with the density.
* `ProbabilityTheory.hasDerivAt_gaussianPDFReal`: the derivative of the Gaussian density.
* `ProbabilityTheory.integral_sub_mul_gaussianReal`: Stein's lemma.
* `ProbabilityTheory.integrable_eval_gaussianReal`,
  `ProbabilityTheory.integral_sub_mul_eval_gaussianReal`: polynomials are integrable, and Stein's
  lemma for polynomials.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

open MeasureTheory Real Polynomial
open scoped NNReal

namespace ProbabilityTheory

variable {μ : ℝ} {v : ℝ≥0}

/-- A function is integrable against a nondegenerate real Gaussian iff its product with the
density is Lebesgue integrable. -/
theorem integrable_gaussianReal_iff_integrable_mul_gaussianPDFReal {g : ℝ → ℝ} (hv : v ≠ 0) :
    Integrable g (gaussianReal μ v) ↔ Integrable (fun x => gaussianPDFReal μ v x * g x) := by
  rw [gaussianReal_of_var_ne_zero _ hv, integrable_withDensity_iff_integrable_smul'
    (measurable_gaussianPDF _ _) (ae_of_all _ fun _ => gaussianPDF_lt_top)]
  simp only [gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _), smul_eq_mul]

/-- The derivative of the density of `N(μ, v)` is `φ' x = -((x - μ) / v) φ x`. For `v = 0` the
density is `0` and both sides vanish. -/
theorem hasDerivAt_gaussianPDFReal (μ : ℝ) (v : ℝ≥0) (x : ℝ) :
    HasDerivAt (gaussianPDFReal μ v) (-((x - μ) / v) * gaussianPDFReal μ v x) x := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp [gaussianPDFReal_zero_var]
  have hv' : (v : ℝ) ≠ 0 := NNReal.coe_ne_zero.2 hv
  rw [gaussianPDFReal_def]
  refine (((((hasDerivAt_id x).sub_const μ).pow 2).neg.div_const (2 * (v : ℝ))).exp.const_mul
    (√(2 * π * v))⁻¹).congr_deriv ?_
  simp only [id, Pi.neg_apply, Pi.pow_apply]
  field_simp
  ring

/-- **Stein's lemma** (Gaussian integration by parts): for `x ∼ N(μ, v)` and a differentiable
`f` with `f`, `(x - μ) f` and `f'` integrable, `E[(x - μ) f x] = v E[f' x]`. -/
theorem integral_sub_mul_gaussianReal {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hfi : Integrable f (gaussianReal μ v))
    (hxf : Integrable (fun x => (x - μ) * f x) (gaussianReal μ v))
    (hf' : Integrable f' (gaussianReal μ v)) :
    ∫ x, (x - μ) * f x ∂gaussianReal μ v = v * ∫ x, f' x ∂gaussianReal μ v := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp [gaussianReal_zero_var]
  have hiff {g : ℝ → ℝ} :=
    integrable_gaussianReal_iff_integrable_mul_gaussianPDFReal (μ := μ) (g := g) hv
  have h1 := (hiff.1 hxf).const_mul (-(v : ℝ)⁻¹)
  have h2 := hiff.1 hf'
  have e (x : ℝ) : -((x - μ) / v) * gaussianPDFReal μ v x * f x + gaussianPDFReal μ v x * f' x =
      -(v : ℝ)⁻¹ * (gaussianPDFReal μ v x * ((x - μ) * f x)) + gaussianPDFReal μ v x * f' x := by
    ring
  have h0 := integral_eq_zero_of_hasDerivAt_of_integrable
    (fun x => (hasDerivAt_gaussianPDFReal μ v x).mul (hf x))
    ((h1.add h2).congr (ae_of_all _ fun x => (e x).symm))
    (hiff.1 hfi)
  rw [integral_congr_ae (ae_of_all _ e), integral_add h1 h2, integral_const_mul, neg_mul,
    neg_add_eq_zero] at h0
  rw [integral_gaussianReal_eq_integral_smul hv, integral_gaussianReal_eq_integral_smul hv]
  simp only [smul_eq_mul]
  rw [← h0, mul_inv_cancel_left₀ (NNReal.coe_ne_zero.2 hv)]

/-- Every polynomial is integrable under a real Gaussian, since its moment generating function is
finite everywhere. -/
theorem integrable_eval_gaussianReal (p : ℝ[X]) :
    Integrable (fun x => p.eval x) (gaussianReal μ v) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [eval_add]
    exact hp.add hq
  | monomial n a =>
    simpa only [eval_monomial] using (integrable_pow_of_mem_interior_integrableExpSet
      (X := fun x : ℝ => x) (by simp) n).const_mul a

/-- **Stein's lemma for polynomials**: for `x ∼ N(μ, v)` and a real polynomial `p`,
`E[(x - μ) p x] = v E[p' x]`. -/
theorem integral_sub_mul_eval_gaussianReal (p : ℝ[X]) :
    ∫ x, (x - μ) * p.eval x ∂gaussianReal μ v =
      v * ∫ x, (derivative p).eval x ∂gaussianReal μ v :=
  integral_sub_mul_gaussianReal (fun x => p.hasDerivAt x) (integrable_eval_gaussianReal p)
    ((integrable_eval_gaussianReal ((X - C μ) * p)).congr (ae_of_all _ fun x => by simp))
    (integrable_eval_gaussianReal _)

end ProbabilityTheory
