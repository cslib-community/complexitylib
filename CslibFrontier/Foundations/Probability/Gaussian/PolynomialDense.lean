/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate (Mathlib, a new file `Mathlib/Probability/Distributions/Gaussian/`
-- `PolynomialDense.lean`)

public import CslibFrontier.Init
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Probability.Distributions.Gaussian.Real
import CslibFrontier.Foundations.MeasureTheory.Function.L2Space
import CslibFrontier.Foundations.Probability.Gaussian.Multivariate
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Probability.Moments.IntegrableExpMul

/-!
# Polynomials are dense in `L²` of the standard Gaussian measure

Let `γⁿ = Measure.pi fun _ : ι => gaussianReal 0 1` be the standard Gaussian measure on `ι → ℝ`.
Every monomial `z ↦ ∏ i, z i ^ k i` lies in `L²(γⁿ)` (`memLp_prod_pow_pi_gaussianReal`), and the
monomials span a dense subspace of `L²(γⁿ)` (`topologicalClosure_span_prod_pow_pi_gaussianReal`):
this is [O'Donnell, Theorem 11.22][ODonnell2014] for `p = 2`. Equivalently, every `f ∈ L²(γⁿ)` is
an `L²` limit of polynomials (`exists_eLpNorm_sub_eval_lt_pi_gaussianReal`).

The proof shows that a function `f ∈ L²(γⁿ)` orthogonal to every monomial vanishes almost
everywhere (`ae_eq_zero_of_forall_integral_mul_prod_pow_eq_zero_pi_gaussianReal`). For each
linear form `L z = a ⬝ᵥ z`, the function `|f| exp |L|` is integrable by Cauchy–Schwarz, since
`L` is a centered real Gaussian under `γⁿ`. Expanding `exp (i L z)` in its power series and
integrating term by term gives `∫ f exp (i L) dγⁿ = ∑ₙ iⁿ / n! ∫ f Lⁿ dγⁿ = 0`, as each `Lⁿ` is a
polynomial. Hence the finite measures `f⁺ γⁿ` and `f⁻ γⁿ` have the same characteristic function,
so they are equal and `f = 0` almost everywhere.

## Main results

* `ProbabilityTheory.memLp_prod_pow_pi_gaussianReal`,
  `ProbabilityTheory.memLp_eval_pi_gaussianReal`: monomials and polynomials lie in `L²(γⁿ)`.
* `ProbabilityTheory.ae_eq_zero_of_forall_integral_mul_prod_pow_eq_zero_pi_gaussianReal`: a
  function in `L²(γⁿ)` orthogonal to all monomials vanishes.
* `ProbabilityTheory.topologicalClosure_span_prod_pow_pi_gaussianReal`,
  `ProbabilityTheory.exists_eLpNorm_sub_eval_lt_pi_gaussianReal`: polynomials are dense in `L²(γⁿ)`
  (Theorem 11.22 for `p = 2`).

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

open MeasureTheory Real
open scoped ENNReal Nat

namespace ProbabilityTheory

variable {ι : Type*} [Fintype ι]

/-- Every monomial `z ↦ ∏ i, z i ^ k i` lies in `L²` of the standard Gaussian measure. -/
theorem memLp_prod_pow_pi_gaussianReal (k : ι → ℕ) :
    MemLp (fun z : ι → ℝ => ∏ i, z i ^ k i) 2 (Measure.pi fun _ : ι => gaussianReal 0 1) := by
  refine (memLp_two_iff_integrable_sq (f := fun z : ι → ℝ => ∏ i, z i ^ k i)
    (continuous_finsetProd _ fun i _ => (continuous_apply i).pow _).aestronglyMeasurable).2 ?_
  simp only [← Finset.prod_pow, ← pow_mul]
  exact Integrable.fintype_prod (f := fun i (t : ℝ) => t ^ (k i * 2)) fun i =>
    integrable_pow_of_mem_interior_integrableExpSet (X := fun x : ℝ => x)
      (μ := gaussianReal 0 1) (by simp) _

/-- Every polynomial lies in `L²` of the standard Gaussian measure. -/
theorem memLp_eval_pi_gaussianReal (p : MvPolynomial ι ℝ) :
    MemLp (fun z : ι → ℝ => MvPolynomial.eval z p) 2
      (Measure.pi fun _ : ι => gaussianReal 0 1) := by
  simp only [MvPolynomial.eval_eq']
  exact memLp_finsetSum _ fun d _ => (memLp_prod_pow_pi_gaussianReal _).const_mul _

/-- `exp |a ⬝ᵥ z|` lies in `L²` of the standard Gaussian measure, as `a ⬝ᵥ z` is a centered
real Gaussian. -/
private theorem memLp_exp_abs_dotProduct (a : ι → ℝ) :
    MemLp (fun z : ι → ℝ => exp |a ⬝ᵥ z|) 2 (Measure.pi fun _ : ι => gaussianReal 0 1) := by
  have h : MemLp (fun x : ℝ => exp |x|) 2 (gaussianReal 0 (‖WithLp.toLp 2 a‖₊ ^ 2)) := by
    refine (memLp_two_iff_integrable_sq (by fun_prop)).2 ?_
    simpa only [← exp_nat_mul, Nat.cast_ofNat, id] using integrable_exp_mul_abs (X := id)
      (integrable_exp_mul_gaussianReal 2) (integrable_exp_mul_gaussianReal (-2))
  exact h.comp_measurePreserving ⟨by fun_prop, pi_gaussianReal_map_dotProduct a⟩

/-- Orthogonality to all monomials is orthogonality to all polynomials. -/
private theorem integral_mul_eval_eq_zero {f : (ι → ℝ) → ℝ}
    (hf : MemLp f 2 (Measure.pi fun _ : ι => gaussianReal 0 1))
    (h : ∀ k : ι → ℕ, ∫ z, f z * ∏ i, z i ^ k i ∂Measure.pi (fun _ : ι => gaussianReal 0 1) = 0)
    (p : MvPolynomial ι ℝ) :
    ∫ z, f z * MvPolynomial.eval z p ∂Measure.pi (fun _ : ι => gaussianReal 0 1) = 0 := by
  simp only [MvPolynomial.eval_eq', Finset.mul_sum, mul_left_comm (f _)]
  rw [integral_finsetSum _ fun d _ => ?_]
  · simp only [integral_const_mul, h, mul_zero, Finset.sum_const_zero]
  · exact (hf.integrable_mul (memLp_prod_pow_pi_gaussianReal d)).const_mul _

/-- If `f ∈ L²(γⁿ)` is orthogonal to all polynomials, then `∫ f (z) exp (i (a ⬝ᵥ z)) dγⁿ = 0`:
expand the exponential and integrate term by term, dominated by `|f| exp |a ⬝ᵥ z|`. -/
private theorem integral_mul_cexp_eq_zero {f : (ι → ℝ) → ℝ}
    (hf : MemLp f 2 (Measure.pi fun _ : ι => gaussianReal 0 1))
    (h : ∀ p : MvPolynomial ι ℝ,
      ∫ z, f z * MvPolynomial.eval z p ∂Measure.pi (fun _ : ι => gaussianReal 0 1) = 0)
    (a : ι → ℝ) :
    ∫ z, (f z : ℂ) * Complex.exp ((a ⬝ᵥ z : ℝ) * Complex.I)
      ∂Measure.pi (fun _ : ι => gaussianReal 0 1) = 0 := by
  set γ := Measure.pi fun _ : ι => gaussianReal 0 1
  set s : (ι → ℝ) → ℝ := fun z => a ⬝ᵥ z with hs
  have hG : Integrable (fun z => |f z| * exp |s z|) γ :=
    (hf.integrable_mul (memLp_exp_abs_dotProduct a)).norm.congr
      (ae_of_all _ fun z => by simp only [Pi.mul_apply, norm_mul, Real.norm_eq_abs, abs_exp]; rfl)
  set F : ℕ → (ι → ℝ) → ℂ := fun n z => (f z : ℂ) * (((s z : ℂ) * Complex.I) ^ n / n !)
    with hF
  have hF_norm (n : ℕ) (z : ι → ℝ) : ‖F n z‖ = |f z| * (|s z| ^ n / n !) := by
    simp only [hF, norm_mul, norm_div, norm_pow, Complex.norm_real, Complex.norm_I, mul_one,
      Complex.norm_natCast, Real.norm_eq_abs]
  have hf1 := hf.aestronglyMeasurable
  have hsc : Continuous s := by fun_prop
  have hF_int (n : ℕ) : Integrable (F n) γ :=
    hG.mono' (by fun_prop) (ae_of_all _ fun z => by
      rw [hF_norm]
      exact mul_le_mul_of_nonneg_left (pow_div_factorial_le_exp _ (abs_nonneg _) n) (abs_nonneg _))
  have hF_sum : Summable fun n => ∫ z, ‖F n z‖ ∂γ := by
    refine summable_of_sum_range_le (c := ∫ z, |f z| * exp |s z| ∂γ)
      (fun n => integral_nonneg fun z => norm_nonneg _) fun N => ?_
    rw [← integral_finsetSum _ fun n _ => (hF_int n).norm]
    refine integral_mono (integrable_finsetSum _ fun n _ => (hF_int n).norm) hG fun z => ?_
    simp only [hF_norm, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_le_exp_of_nonneg (abs_nonneg _) N) (abs_nonneg _)
  have hterm (n : ℕ) : ∫ z, F n z ∂γ = 0 := by
    have hpt (z : ι → ℝ) : F n z = (Complex.I ^ n / n ! : ℂ) * ((f z * MvPolynomial.eval z
        ((∑ i, MvPolynomial.C (a i) * MvPolynomial.X i) ^ n) : ℝ) : ℂ) := by
      simp only [hF, hs, dotProduct, map_pow, map_sum, map_mul, MvPolynomial.eval_C,
        MvPolynomial.eval_X,
        Complex.ofReal_mul, Complex.ofReal_pow, mul_pow]
      ring
    simp only [hpt]
    rw [integral_const_mul, integral_complex_ofReal, h, Complex.ofReal_zero, mul_zero]
  have hsum (z : ι → ℝ) : ∑' n, F n z = (f z : ℂ) * Complex.exp ((s z : ℂ) * Complex.I) := by
    rw [Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div, ← tsum_mul_left]
  have key := hasSum_integral_of_summable_integral_norm hF_int hF_sum
  simp only [hterm, hsum] at key
  exact key.unique hasSum_zero

/-- **A function orthogonal to all polynomials vanishes**: if `f ∈ L²(γⁿ)` satisfies
`∫ f (z) ∏ i, z i ^ k i dγⁿ = 0` for every multi-index `k`, then `f = 0` almost everywhere. The
finite measures `f⁺ γⁿ` and `f⁻ γⁿ` have the same characteristic function, by expanding
`exp (i L z)` in its power series. -/
theorem ae_eq_zero_of_forall_integral_mul_prod_pow_eq_zero_pi_gaussianReal {f : (ι → ℝ) → ℝ}
    (hf : MemLp f 2 (Measure.pi fun _ : ι => gaussianReal 0 1))
    (h : ∀ k : ι → ℕ, ∫ z, f z * ∏ i, z i ^ k i ∂Measure.pi (fun _ : ι => gaussianReal 0 1) = 0) :
    f =ᵐ[Measure.pi fun _ : ι => gaussianReal 0 1] 0 := by
  classical
  set γ := Measure.pi fun _ : ι => gaussianReal 0 1
  have hfi : Integrable f γ := hf.integrable one_le_two
  have hm (g : (ι → ℝ) → ℝ) (hg : Integrable g γ) :
      AEMeasurable (fun z => ENNReal.ofReal (g z)) γ :=
    hg.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  -- The characteristic function of `g⁺ γⁿ`.
  have hchar (g : (ι → ℝ) → ℝ) (hg : Integrable g γ) (L : StrongDual ℝ (ι → ℝ)) :
      charFunDual (γ.withDensity fun z => ENNReal.ofReal (g z)) L =
        ∫ z, (max (g z) 0 : ℝ) * Complex.exp (L z * Complex.I) ∂γ := by
    rw [charFunDual_apply, integral_withDensity_eq_integral_toReal_smul₀ (hm g hg)
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal', Complex.real_smul]
  have hint (g : (ι → ℝ) → ℝ) (hg : Integrable g γ) (L : StrongDual ℝ (ι → ℝ)) :
      Integrable (fun z => (g z : ℂ) * Complex.exp (L z * Complex.I)) γ := by
    have hg1 := hg.aestronglyMeasurable
    refine hg.norm.mono' (by fun_prop) (ae_of_all _ fun z => ?_)
    rw [norm_mul, Complex.norm_real, Complex.norm_exp_ofReal_mul_I, mul_one]
  have : IsFiniteMeasure (γ.withDensity fun z => ENNReal.ofReal (f z)) :=
    isFiniteMeasure_withDensity_ofReal hfi.2
  have : IsFiniteMeasure (γ.withDensity fun z => ENNReal.ofReal (-f z)) :=
    isFiniteMeasure_withDensity_ofReal hfi.neg.2
  have hμ : (γ.withDensity fun z => ENNReal.ofReal (f z)) =
      γ.withDensity fun z => ENNReal.ofReal (-f z) := by
    refine Measure.ext_of_charFunDual (funext fun L => ?_)
    have hL (z : ι → ℝ) : L z = (fun i => L fun j => if i = j then 1 else 0) ⬝ᵥ z := by
      simpa [dotProduct, mul_comm] using L.toLinearMap.pi_apply_eq_sum_univ z
    have h0 := integral_mul_cexp_eq_zero hf (integral_mul_eval_eq_zero hf h)
      fun i => L fun j => if i = j then 1 else 0
    simp only [← hL] at h0
    have hpt (z : ι → ℝ) : ((max (f z) 0 : ℝ) : ℂ) * Complex.exp (L z * Complex.I) =
        (f z : ℂ) * Complex.exp (L z * Complex.I) +
          ((max (-f z) 0 : ℝ) : ℂ) * Complex.exp (L z * Complex.I) := by
      have e : max (f z) 0 = f z + max (-f z) 0 := by
        linarith [max_zero_sub_max_neg_zero_eq_self (f z)]
      rw [e, Complex.ofReal_add, add_mul]
    rw [hchar f hfi, hchar (fun z => -f z) hfi.neg, integral_congr_ae (ae_of_all _ hpt),
      integral_add (hint f hfi L) (hint _ hfi.neg_part L), h0, zero_add]
  filter_upwards [(withDensity_eq_iff_of_sigmaFinite (hm f hfi) (hm _ hfi.neg)).1 hμ] with z hz
  have h' := congrArg ENNReal.toReal hz
  simp only [Pi.neg_apply, ENNReal.toReal_ofReal'] at h'
  change f z = 0
  linarith [max_zero_sub_max_neg_zero_eq_self (f z)]

/-- **Polynomials are dense in `L²(γⁿ)`** [O'Donnell, Theorem 11.22][ODonnell2014], for `p = 2`:
the monomials `z ↦ ∏ i, z i ^ k i` span a dense subspace of `L²` of the standard Gaussian
measure. -/
theorem topologicalClosure_span_prod_pow_pi_gaussianReal :
    (Submodule.span ℝ (Set.range fun k : ι → ℕ =>
      (memLp_prod_pow_pi_gaussianReal k).toLp _)).topologicalClosure = ⊤ :=
  L2.topologicalClosure_span_toLp_eq_top _ fun _ hf h =>
    ae_eq_zero_of_forall_integral_mul_prod_pow_eq_zero_pi_gaussianReal hf h

/-- **Polynomials are dense in `L²(γⁿ)`** [O'Donnell, Theorem 11.22][ODonnell2014], for `p = 2`:
every `f ∈ L²` of the standard Gaussian measure is within any `ε > 0` of a polynomial in `L²`
norm. -/
theorem exists_eLpNorm_sub_eval_lt_pi_gaussianReal {f : (ι → ℝ) → ℝ}
    (hf : MemLp f 2 (Measure.pi fun _ : ι => gaussianReal 0 1)) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ p : MvPolynomial ι ℝ, eLpNorm (f - fun z => MvPolynomial.eval z p) 2
      (Measure.pi fun _ : ι => gaussianReal 0 1) < ε := by
  set γ := Measure.pi fun _ : ι => gaussianReal 0 1
  have hmem : hf.toLp f ∈ closure (Submodule.span ℝ (Set.range fun k : ι → ℕ =>
      (memLp_prod_pow_pi_gaussianReal k).toLp _) : Set (Lp ℝ 2 γ)) := by
    rw [← Submodule.topologicalClosure_coe, topologicalClosure_span_prod_pow_pi_gaussianReal]
    trivial
  -- Every element of the span is (the class of) a polynomial.
  have hpoly (u : Lp ℝ 2 γ) (hu : u ∈ Submodule.span ℝ (Set.range fun k : ι → ℕ =>
      (memLp_prod_pow_pi_gaussianReal k).toLp _)) :
      ∃ p : MvPolynomial ι ℝ, ⇑u =ᵐ[γ] fun z => MvPolynomial.eval z p := by
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      refine ⟨∏ i, MvPolynomial.X i ^ k i, ?_⟩
      filter_upwards [(memLp_prod_pow_pi_gaussianReal k).coeFn_toLp] with z hz
      simp only [hz, map_prod, map_pow, MvPolynomial.eval_X]
    | zero =>
      refine ⟨0, ?_⟩
      filter_upwards [Lp.coeFn_zero ℝ 2 γ] with z hz
      simp only [hz, Pi.zero_apply, map_zero]
    | add x y _ _ hx hy =>
      obtain ⟨p, hp⟩ := hx
      obtain ⟨q, hq⟩ := hy
      refine ⟨p + q, ?_⟩
      filter_upwards [Lp.coeFn_add x y, hp, hq] with z hz hpz hqz
      simp only [hz, Pi.add_apply, hpz, hqz, map_add]
    | smul c x _ hx =>
      obtain ⟨p, hp⟩ := hx
      refine ⟨MvPolynomial.C c * p, ?_⟩
      filter_upwards [Lp.coeFn_smul c x, hp] with z hz hpz
      simp only [hz, Pi.smul_apply, hpz, smul_eq_mul, map_mul, MvPolynomial.eval_C]
  obtain ⟨u, hu, hdist⟩ := EMetric.mem_closure_iff.1 hmem ε hε
  obtain ⟨p, hp⟩ := hpoly u hu
  refine ⟨p, ?_⟩
  rw [Lp.edist_def] at hdist
  refine (eLpNorm_congr_ae ?_).trans_lt hdist
  filter_upwards [hf.coeFn_toLp, hp] with z hz hpz
  simp only [Pi.sub_apply, hz, hpz]

end ProbabilityTheory
