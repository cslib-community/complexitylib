/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.Degree
public import CslibFrontier.Foundations.BooleanAnalysis.Influence
public import CslibFrontier.Foundations.Probability.Multilinear.Invariance
public import Cslib.Probability.PMF
import CslibFrontier.Foundations.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# The Basic Invariance Principle on the Boolean cube

A uniform random sign has law `rademacher`, the image of a uniform bit under `signVal`
(`false ↦ 1`, `true ↦ -1`); it satisfies Hypothesis 11.65 of [O'Donnell][ODonnell2014]
(`hasInvarianceMoments_rademacher`), and the product of `n` copies is the uniform distribution on
the signs of the cube (`integral_pi_rademacher`). Evaluating the Fourier expansion of
`f : (ι → Bool) → ℝ` at the signs of `x` gives `f x`, and the influences of the formal polynomial
are those of `f` (`multilinearEval_fourierCoeff_signVal`, `multilinearInfluence_fourierCoeff`).

So the Basic Invariance Principle compares a function of degree at most `k` on uniformly random
bits with its Fourier expansion on any independent variables satisfying Hypothesis 11.65, for
instance standard Gaussians: for `ψ` with `‖ψ⁗‖_∞ ≤ C`,
`|𝔼_x ψ(f x) - E[ψ(F(y))]| ≤ C / 12 · 9 ^ k · ∑_i Inf_i[f] ^ 2`
(`abs_expect_comp_sub_integral_comp_multilinearEval_le`) [O'Donnell, Section 11.6, Basic Invariance
Principle][ODonnell2014], and if moreover `Var[f] ≤ 1` and every `Inf_i[f] ≤ ε`, the bound is
`C / 12 · k 9 ^ k · ε` (`abs_expect_comp_sub_integral_comp_multilinearEval_le_of_influence_le`,
Corollary 11.67).

## Main definitions

* `Cslib.BitString.rademacher`: the law of a uniform random sign.

## Main results

* `Cslib.BitString.hasInvarianceMoments_rademacher`: uniform signs satisfy Hypothesis 11.65.
* `Cslib.BitString.integral_pi_rademacher`: the product of uniform signs is the uniform
  distribution on the signs of the cube.
* `Cslib.BitString.multilinearEval_fourierCoeff_signVal`: the Fourier expansion evaluates `f`.
* `Cslib.BitString.abs_expect_comp_sub_integral_comp_multilinearEval_le`: the Basic Invariance
  Principle for functions on the cube.
* `Cslib.BitString.abs_expect_comp_sub_integral_comp_multilinearEval_le_of_influence_le`:
  Corollary 11.67 for functions on the cube.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014], Section 11.6.
-/

public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators

namespace Cslib.BitString

/-! ### Uniform random signs -/

/-- The law of a uniform random sign: the image of a uniform bit under `signVal`. -/
noncomputable def rademacher : Measure ℝ :=
  (Probability.PMF.uniformOfFintype Bool).toMeasure.map signVal

private theorem measurableEmbedding_signVal : MeasurableEmbedding signVal :=
  .of_countable fun a b h => by revert h; cases a <;> cases b <;> norm_num [signVal]

instance : IsProbabilityMeasure rademacher := by
  rw [rademacher]; infer_instance

/-- The expectation of `g` at a uniform random sign is `(g 1 + g (-1)) / 2`. -/
theorem integral_rademacher (g : ℝ → ℝ) : ∫ s, g s ∂rademacher = (g 1 + g (-1)) / 2 := by
  rw [rademacher, measurableEmbedding_signVal.integral_map, integral_fintype .of_finite]
  simp [Measure.real, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  ring

/-- Uniform random signs satisfy Hypothesis 11.65 of [O'Donnell][ODonnell2014], with
`E[s⁴] = 1`. -/
theorem hasInvarianceMoments_rademacher : HasInvarianceMoments rademacher where
  memLp_four := by
    refine (memLp_map_measure_iff aestronglyMeasurable_id
      (measurable_of_countable _).aemeasurable).2 ?_
    exact .of_discrete
  integral_id := by rw [integral_rademacher]; norm_num
  integral_sq := by rw [integral_rademacher]; norm_num
  integral_pow_three := by rw [integral_rademacher]; norm_num
  integral_pow_four_le := by rw [integral_rademacher]; norm_num

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The product of uniform random signs is uniform on the signs of the cube**: the expectation of
`g` at independent uniform signs is `𝔼_x g(signVal ∘ x)`. -/
theorem integral_pi_rademacher (g : (ι → ℝ) → ℝ) :
    ∫ z, g z ∂Measure.pi (fun _ : ι => rademacher) =
      𝔼 x : ι → Bool, g (fun i => signVal (x i)) := by
  have hmap : Measure.pi (fun _ : ι => rademacher) =
      (Measure.pi fun _ : ι => (Probability.PMF.uniformOfFintype Bool).toMeasure).map
        (fun x i => signVal (x i)) := by
    rw [rademacher, Measure.pi_map_pi fun _ => (measurable_of_countable _).aemeasurable]
  have hemb : MeasurableEmbedding (fun (x : ι → Bool) i => signVal (x i)) :=
    .of_countable fun x y h => funext fun i => measurableEmbedding_signVal.injective (congrFun h i)
  rw [hmap, hemb.integral_map, integral_fintype .of_finite, Fintype.expect_eq_sum_div_card,
    sum_div]
  refine sum_congr rfl fun x _ => ?_
  rw [← Set.univ_pi_singleton, Measure.real, Measure.pi_pi]
  simp [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), div_eq_inv_mul]

/-! ### Functions on the cube as multilinear polynomials -/

/-- The Fourier expansion of `f`, evaluated at the signs of `x`, is `f x`. -/
theorem multilinearEval_fourierCoeff_signVal (f : (ι → Bool) → ℝ) (x : ι → Bool) :
    multilinearEval (fourierCoeff f) (fun i => signVal (x i)) = f x := by
  rw [multilinearEval_def, ← sum_fourierCoeff_mul_chi f x]
  simp only [chi_eq_prod_signVal]

/-- The influences of the Fourier expansion of `f` are the influences of `f`. -/
theorem multilinearInfluence_fourierCoeff (f : (ι → Bool) → ℝ) (i : ι) :
    multilinearInfluence (fourierCoeff f) i = influence i f := by
  rw [multilinearInfluence_def, influence_eq_sum_fourierCoeff_sq]

/-! ### The Basic Invariance Principle on the cube -/

variable (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]

/-- **The Basic Invariance Principle on the cube** [O'Donnell, Section 11.6, equation
(11.29)][ODonnell2014]. Let `f : (ι → Bool) → ℝ` have degree at most `k`, and let `y` be a vector
of independent random variables with laws `μ i`, each satisfying Hypothesis 11.65 (for instance
standard Gaussians, `hasInvarianceMoments_gaussianReal`). If `ψ : ℝ → ℝ` is `C⁴` with `|ψ⁗| ≤ C`,
then the expectation of `ψ ∘ f` at uniformly random bits differs from that of `ψ` applied to the
Fourier expansion of `f` at `y` by at most `C / 12 · 9 ^ k · ∑_i Inf_i[f] ^ 2`. -/
theorem abs_expect_comp_sub_integral_comp_multilinearEval_le
    (hμ : ∀ i, HasInvarianceMoments (μ i)) {f : (ι → Bool) → ℝ} {k : ℕ} (hf : totalDegree f ≤ k)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 4 ψ) {C : ℝ} (hC : ∀ y, |iteratedDeriv 4 ψ y| ≤ C) :
    |𝔼 x, ψ (f x) - ∫ y, ψ (multilinearEval (fourierCoeff f) y) ∂Measure.pi μ| ≤
      C / 12 * 9 ^ k * ∑ i, influence i f ^ 2 := by
  have h := abs_integral_comp_multilinearEval_sub_le (fun _ => rademacher) μ
    (fun _ => hasInvarianceMoments_rademacher) hμ (totalDegree_le_iff_fourierCoeff_eq_zero.1 hf)
    hψ hC
  simpa only [integral_pi_rademacher, multilinearEval_fourierCoeff_signVal,
    multilinearInfluence_fourierCoeff] using h

/-- **Invariance for functions with small influences** [O'Donnell, Corollary 11.67][ODonnell2014].
In the setting of `abs_expect_comp_sub_integral_comp_multilinearEval_le`, if moreover
`Var[f] ≤ 1` and `Inf_i[f] ≤ ε` for every `i`, the bound is `C / 12 · k 9 ^ k · ε`. The hypothesis
`0 ≤ ε` only matters when there are no coordinates. -/
theorem abs_expect_comp_sub_integral_comp_multilinearEval_le_of_influence_le
    (hμ : ∀ i, HasInvarianceMoments (μ i)) {f : (ι → Bool) → ℝ} {k : ℕ} (hf : totalDegree f ≤ k)
    (hvar : 𝔼 x, (f x - 𝔼 y, f y) ^ 2 ≤ 1) {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ∀ i, influence i f ≤ ε)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 4 ψ) {C : ℝ} (hC : ∀ y, |iteratedDeriv 4 ψ y| ≤ C) :
    |𝔼 x, ψ (f x) - ∫ y, ψ (multilinearEval (fourierCoeff f) y) ∂Measure.pi μ| ≤
      C / 12 * k * 9 ^ k * ε := by
  rw [expect_sub_expect_sq_eq_sum_fourierCoeff_sq] at hvar
  have h := abs_integral_comp_multilinearEval_sub_le_of_influence_le (fun _ => rademacher) μ
    (fun _ => hasInvarianceMoments_rademacher) hμ (totalDegree_le_iff_fourierCoeff_eq_zero.1 hf)
    hvar hε0 (fun i => (multilinearInfluence_fourierCoeff f i).trans_le (hε i)) hψ hC
  simpa only [integral_pi_rademacher, multilinearEval_fourierCoeff_signVal] using h

/-- **The Basic Invariance Principle on the cube, `C³` form**: in the setting of
`abs_expect_comp_sub_integral_comp_multilinearEval_le`, if `ψ` is only `C³` with `|ψ‴| ≤ C`, the
bound is `C / 3 · 3 ^ k · ∑_i Inf_i[f] ^ (3 / 2)` (the analogue under Hypothesis 11.65 of
[O'Donnell, Remark 11.66][ODonnell2014]). -/
theorem abs_expect_comp_sub_integral_comp_multilinearEval_le_of_contDiff_three
    (hμ : ∀ i, HasInvarianceMoments (μ i)) {f : (ι → Bool) → ℝ} {k : ℕ} (hf : totalDegree f ≤ k)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 3 ψ) {C : ℝ} (hC : ∀ y, |iteratedDeriv 3 ψ y| ≤ C) :
    |𝔼 x, ψ (f x) - ∫ y, ψ (multilinearEval (fourierCoeff f) y) ∂Measure.pi μ| ≤
      C / 3 * 3 ^ k * ∑ i, influence i f ^ ((3 : ℝ) / 2) := by
  have h := abs_integral_comp_multilinearEval_sub_le_of_contDiff_three (fun _ => rademacher) μ
    (fun _ => hasInvarianceMoments_rademacher) hμ (totalDegree_le_iff_fourierCoeff_eq_zero.1 hf)
    hψ hC
  simpa only [integral_pi_rademacher, multilinearEval_fourierCoeff_signVal,
    multilinearInfluence_fourierCoeff] using h

end Cslib.BitString
