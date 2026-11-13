/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate (Mathlib, a new file `Mathlib/Probability/Distributions/Gaussian/`
-- `Hermite.lean`)

public import CslibFrontier.Foundations.Probability.Gaussian.NoiseOperator
public import Mathlib.RingTheory.Polynomial.Hermite.Basic
import CslibFrontier.Foundations.Probability.Gaussian.Stein
import CslibFrontier.Foundations.RingTheory.Polynomial.Hermite
import Mathlib.Topology.Algebra.Polynomial

/-!
# Hermite polynomials in Gaussian space

The probabilists' Hermite polynomials `H_j = Polynomial.hermite j` are orthogonal in `L²(γ)` for
the standard Gaussian measure `γ`, with `⟨H_j, H_k⟩ = j!` if `j = k` and `0` otherwise
[O'Donnell, (11.9)][ODonnell2014] (`integral_aeval_hermite_mul_aeval_hermite`). The normalized
Hermite polynomials `h_j = H_j / √(j!)` (Definition 11.29, `normalizedHermite`) are therefore
orthonormal, and so are their products `h_α z = ∏ i, h_{α i} (z i)` over a multi-index
`α : ι → ℕ` (Definition 11.32, `multiHermite`) in `L²(γⁿ)`. Each `h_α` is an eigenfunction of the
Gaussian noise operator, `U_ρ h_α = ρ ^ |α| h_α` for `|ρ| ≤ 1`, so for `ρ`-correlated `(z, z')`,
`E[h_α z h_β z'] = ⟨h_α, U_ρ h_β⟩` is `ρ ^ |α|` if `α = β` and `0` otherwise (Proposition 11.33,
and Proposition 11.31 in one dimension). Completeness of the Hermite basis
(Propositions 11.30 and 11.33, `ProbabilityTheory.normalizedHermiteBasis` and
`ProbabilityTheory.hermiteBasis`) and Hermite expansions are in
`CslibFrontier.Foundations.Probability.Gaussian.HermiteExpansion`.

The book derives these facts from the generating function of `H_j` (11.7)–(11.8). Here they
follow from Stein's lemma `E[x p x] = E[p' x]` for polynomials `p`
(`integral_sub_mul_eval_gaussianReal`) together with `H_{j+1} = X H_j - H_j'` (Mathlib's
definition) and the Appell property `H_{j+1}' = (j + 1) H_j`
(`Polynomial.derivative_hermite_succ`):

* Integration by parts against `H_{k+1}` gives `E[p H_{k+1}] = E[p' H_k]`
  (`integral_eval_mul_aeval_hermite_succ`), so `E[p H_k] = E[p⁽ᵏ⁾]`
  (`integral_eval_mul_aeval_hermite`) and `⟨H_j, H_{k+1}⟩ = j ⟨H_{j-1}, H_k⟩`.
* For the noisy point `y = ρ x + √(1 - ρ²) g`, Stein's lemma in `g` gives
  `E[H_{n+1} y] = ρ x E[H_n y] - ρ² E[H_n' y]`, and induction on `n` gives
  `E_g[H_n y] = ρ ^ n H_n x` (`integral_aeval_hermite_gaussianNoise`).

The multivariate statements follow by independence of the coordinates. For an indicator
multi-index, `h_α` is the monomial `∏ i ∈ S, zᵢ` (`multiHermite_indicator`, Remark 11.35), so on
monomials the eigenvalue identity agrees with `ProbabilityTheory.gaussianNoiseOp_prod`
(Fact 11.13, Remark 11.38).

## Main definitions

* `ProbabilityTheory.normalizedHermite`: the normalized Hermite polynomial `h_j` as a function.
* `ProbabilityTheory.multiHermite`: the multivariate Hermite polynomial `h_α` as a function.

## Main results

* `ProbabilityTheory.integral_eval_mul_aeval_hermite_succ`,
  `ProbabilityTheory.integral_eval_mul_aeval_hermite`: `E[p H_k] = E[p⁽ᵏ⁾]`.
* `ProbabilityTheory.integral_aeval_hermite_mul_aeval_hermite`,
  `ProbabilityTheory.integral_normalizedHermite_mul_normalizedHermite`: orthogonality (11.9) and
  orthonormality (Proposition 11.30, without completeness).
* `ProbabilityTheory.integral_aeval_hermite_gaussianNoise`,
  `ProbabilityTheory.integral_normalizedHermite_gaussianNoise`: `U_ρ h_j = ρ ^ j h_j` in one
  dimension.
* `ProbabilityTheory.integral_correlatedGaussian_normalizedHermite`: correlations of the
  normalized Hermite polynomials (Proposition 11.31).
* `ProbabilityTheory.gaussianNoiseOp_multiHermite`: `U_ρ h_α = ρ ^ |α| h_α`.
* `ProbabilityTheory.integral_multiHermite_mul_multiHermite`,
  `ProbabilityTheory.integral_multiHermite_mul_gaussianNoiseOp`,
  `ProbabilityTheory.integral_correlatedGaussianPi_multiHermite`: orthonormality and the
  correlations of Proposition 11.33, without completeness.
* `ProbabilityTheory.multiHermite_indicator`: `h_S z = ∏ i ∈ S, zᵢ` (Definition 11.32,
  Remark 11.35).

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

open MeasureTheory Real Polynomial
open scoped Nat

namespace ProbabilityTheory

/-! ### Univariate Hermite polynomials -/

section Univariate

/-- The expectation `p ↦ E[p x]` of a real polynomial under the standard Gaussian, as a linear
functional. -/
private noncomputable def gaussE : ℝ[X] →ₗ[ℝ] ℝ where
  toFun p := ∫ x, p.eval x ∂gaussianReal 0 1
  map_add' p q := by
    simp only [eval_add]
    exact integral_add (integrable_eval_gaussianReal p) (integrable_eval_gaussianReal q)
  map_smul' c p := by
    simp only [eval_smul, smul_eq_mul, RingHom.id_apply]
    exact integral_const_mul c _

private theorem gaussE_apply (p : ℝ[X]) : gaussE p = ∫ x, p.eval x ∂gaussianReal 0 1 := rfl

private theorem gaussE_C_mul (c : ℝ) (p : ℝ[X]) : gaussE (C c * p) = c * gaussE p := by
  rw [C_mul', map_smul, smul_eq_mul]

private theorem gaussE_one : gaussE 1 = 1 := by
  simp only [gaussE_apply, eval_one, integral_const, probReal_univ, smul_eq_mul, mul_one]

/-- Stein's lemma for the standard Gaussian: `E[x p x] = E[p' x]`. -/
private theorem gaussE_X_mul (p : ℝ[X]) : gaussE (X * p) = gaussE (derivative p) := by
  have h := integral_sub_mul_eval_gaussianReal (μ := 0) (v := 1) p
  simp only [sub_zero, NNReal.coe_one, one_mul] at h
  simp only [gaussE_apply, eval_mul, eval_X, h]

/-- The Hermite polynomial `H_n` with real coefficients. -/
private noncomputable abbrev hermiteR (n : ℕ) : ℝ[X] := (hermite n).map (algebraMap ℤ ℝ)

private theorem aeval_hermite (n : ℕ) (x : ℝ) : aeval x (hermite n) = (hermiteR n).eval x :=
  (eval_map_algebraMap _ _).symm

private theorem hermiteR_zero : hermiteR 0 = 1 := by
  simp only [hermiteR, hermite_zero, C_1, Polynomial.map_one]

private theorem hermiteR_succ (n : ℕ) :
    hermiteR (n + 1) = X * hermiteR n - derivative (hermiteR n) := by
  simp only [hermiteR, hermite_succ, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_X,
    derivative_map]

private theorem derivative_hermiteR_succ (n : ℕ) :
    derivative (hermiteR (n + 1)) = C ((n : ℝ) + 1) * hermiteR n := by
  rw [hermiteR, hermiteR, derivative_map, derivative_hermite_succ, Polynomial.map_mul]
  congr 1
  simp

/-- Integration by parts against `H_{k+1}`: `E[p H_{k+1}] = E[p' H_k]`. -/
private theorem gaussE_mul_hermiteR_succ (p : ℝ[X]) (k : ℕ) :
    gaussE (p * hermiteR (k + 1)) = gaussE (derivative p * hermiteR k) := by
  rw [hermiteR_succ, show p * (X * hermiteR k - derivative (hermiteR k)) =
    X * (p * hermiteR k) - p * derivative (hermiteR k) by ring, map_sub, gaussE_X_mul,
    derivative_mul, map_add, add_sub_cancel_right]

/-- **Gaussian integration by parts against a Hermite polynomial**: for a real polynomial `p`,
`E[p H_{k+1}] = E[p' H_k]` under the standard Gaussian. -/
theorem integral_eval_mul_aeval_hermite_succ (p : ℝ[X]) (k : ℕ) :
    ∫ x, p.eval x * aeval x (hermite (k + 1)) ∂gaussianReal 0 1 =
      ∫ x, (derivative p).eval x * aeval x (hermite k) ∂gaussianReal 0 1 := by
  simpa only [gaussE_apply, eval_mul, aeval_hermite] using gaussE_mul_hermiteR_succ p k

/-- **Gaussian integration by parts against `H_k`**: for a real polynomial `p`,
`E[p H_k] = E[p⁽ᵏ⁾]` under the standard Gaussian. In particular `H_k` is orthogonal to every
polynomial of degree less than `k`. -/
theorem integral_eval_mul_aeval_hermite (p : ℝ[X]) (k : ℕ) :
    ∫ x, p.eval x * aeval x (hermite k) ∂gaussianReal 0 1 =
      ∫ x, (derivative^[k] p).eval x ∂gaussianReal 0 1 := by
  induction k generalizing p with
  | zero => simp only [aeval_hermite, hermiteR_zero, eval_one, mul_one, Function.iterate_zero_apply]
  | succ k ih => rw [integral_eval_mul_aeval_hermite_succ, ih, Function.iterate_succ_apply]

private theorem gaussE_hermiteR_mul_hermiteR (j k : ℕ) :
    gaussE (hermiteR j * hermiteR k) = if j = k then (k ! : ℝ) else 0 := by
  induction k generalizing j with
  | zero =>
    rw [hermiteR_zero, mul_one]
    cases j with
    | zero => rw [hermiteR_zero, gaussE_one, ite_eq_left rfl, Nat.factorial_zero, Nat.cast_one]
    | succ j =>
      rw [hermiteR_succ, map_sub, gaussE_X_mul, sub_self, ite_eq_right (Nat.succ_ne_zero j)]
  | succ k ih =>
    rw [gaussE_mul_hermiteR_succ]
    cases j with
    | zero =>
      rw [hermiteR_zero, derivative_one, zero_mul, map_zero, ite_eq_right (Nat.succ_ne_zero k).symm]
    | succ j =>
      rw [derivative_hermiteR_succ, mul_assoc, gaussE_C_mul, ih]
      by_cases h : j = k
      · subst h
        rw [ite_eq_left rfl, ite_eq_left rfl, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
      · rw [ite_eq_right h, ite_eq_right (by omega), mul_zero]

/-- **Orthogonality of the Hermite polynomials** [O'Donnell, (11.9)][ODonnell2014]:
`⟨H_j, H_k⟩ = j!` if `j = k` and `0` otherwise, in `L²` of the standard Gaussian. -/
theorem integral_aeval_hermite_mul_aeval_hermite (j k : ℕ) :
    ∫ x, aeval x (hermite j) * aeval x (hermite k) ∂gaussianReal 0 1 =
      if j = k then (j ! : ℝ) else 0 := by
  have h := gaussE_hermiteR_mul_hermiteR j k
  simp only [gaussE_apply, eval_mul] at h
  simp only [aeval_hermite, h]
  split_ifs with hjk <;> simp only [hjk]

/-- The noisy point `ρ x + √(1 - ρ²) g` as a polynomial in `g`. -/
private noncomputable abbrev noisyPoly (ρ x : ℝ) : ℝ[X] := C (ρ * x) + C √(1 - ρ ^ 2) * X

private theorem eval_noisyPoly (ρ x g : ℝ) :
    (noisyPoly ρ x).eval g = ρ * x + √(1 - ρ ^ 2) * g := by
  simp only [noisyPoly, eval_add, eval_C, eval_mul, eval_X]

/-- The eigenvalue identity `E_g[H_n (ρ x + √(1 - ρ²) g)] = ρ ^ n H_n x`, by strong induction
on `n` through `H_{n+1} = X H_n - H_n'` and Stein's lemma in `g`. -/
private theorem gaussE_hermiteR_comp_noisyPoly {ρ : ℝ} (hρ : |ρ| ≤ 1) (x : ℝ) :
    ∀ n, gaussE ((hermiteR n).comp (noisyPoly ρ x)) = ρ ^ n * (hermiteR n).eval x
  | 0 => by rw [hermiteR_zero, one_comp, gaussE_one, eval_one, pow_zero, mul_one]
  | n + 1 => by
    have hσ : √(1 - ρ ^ 2) ^ 2 = 1 - ρ ^ 2 :=
      sq_sqrt (sub_nonneg.2 ((sq_le_one_iff_abs_le_one ρ).2 hρ))
    -- `ρ E[H_n' y] = ρ ^ n H_n' x`, from the induction hypothesis at `n - 1`.
    have hD : ρ * gaussE ((derivative (hermiteR n)).comp (noisyPoly ρ x)) =
        ρ ^ n * (derivative (hermiteR n)).eval x := by
      cases n with
      | zero => rw [hermiteR_zero, derivative_one, zero_comp, map_zero, eval_zero, mul_zero,
          mul_zero]
      | succ m =>
        rw [derivative_hermiteR_succ, mul_comp, C_comp, gaussE_C_mul,
          gaussE_hermiteR_comp_noisyPoly hρ x m, eval_mul, eval_C]
        ring
    -- Stein's lemma in `g`: `E[g H_n y] = √(1 - ρ²) E[H_n' y]`.
    have hS : gaussE (X * (hermiteR n).comp (noisyPoly ρ x)) =
        √(1 - ρ ^ 2) * gaussE ((derivative (hermiteR n)).comp (noisyPoly ρ x)) := by
      rw [gaussE_X_mul, derivative_comp, noisyPoly, derivative_add, derivative_C, zero_add,
        derivative_mul, derivative_C, zero_mul, zero_add, derivative_X, mul_one, gaussE_C_mul]
    have hE : (hermiteR (n + 1)).comp (noisyPoly ρ x) =
        C (ρ * x) * (hermiteR n).comp (noisyPoly ρ x) +
          C √(1 - ρ ^ 2) * (X * (hermiteR n).comp (noisyPoly ρ x)) -
            (derivative (hermiteR n)).comp (noisyPoly ρ x) := by
      rw [hermiteR_succ, sub_comp, mul_comp, X_comp, noisyPoly]
      ring
    rw [hE, map_sub, map_add, gaussE_C_mul, gaussE_C_mul, hS,
      gaussE_hermiteR_comp_noisyPoly hρ x n, hermiteR_succ, eval_sub, eval_mul, eval_X]
    linear_combination gaussE ((derivative (hermiteR n)).comp (noisyPoly ρ x)) * hσ - ρ * hD

/-- **Hermite polynomials are eigenfunctions of the Gaussian noise operator**, in one dimension;
the identity behind [O'Donnell, Proposition 11.31][ODonnell2014]: for `|ρ| ≤ 1`,
`E_g[H_n (ρ x + √(1 - ρ²) g)] = ρ ^ n H_n x` for a standard Gaussian `g`. -/
theorem integral_aeval_hermite_gaussianNoise {ρ : ℝ} (hρ : |ρ| ≤ 1) (n : ℕ) (x : ℝ) :
    ∫ g, aeval (ρ * x + √(1 - ρ ^ 2) * g) (hermite n) ∂gaussianReal 0 1 =
      ρ ^ n * aeval x (hermite n) := by
  have h := gaussE_hermiteR_comp_noisyPoly hρ x n
  simp only [gaussE_apply, eval_comp, eval_noisyPoly] at h
  simp only [aeval_hermite, h]

/-- The **normalized Hermite polynomial** `h_j = H_j / √(j!)`
[O'Donnell, Definition 11.29][ODonnell2014], as a function on `ℝ`. The book defines `H_j` by the
generating function (11.8); Mathlib's `Polynomial.hermite` is defined by the recursion
`H_{j+1} = X H_j - H_j'` and agrees with the Rodrigues formula (11.10) by
`Polynomial.hermite_eq_deriv_gaussian`. -/
noncomputable def normalizedHermite (j : ℕ) (x : ℝ) : ℝ :=
  aeval x (hermite j) / √(j ! : ℝ)

/-- Unfolding `h_j = H_j / √(j!)`. -/
theorem normalizedHermite_def (j : ℕ) (x : ℝ) :
    normalizedHermite j x = aeval x (hermite j) / √(j ! : ℝ) := by
  rw [normalizedHermite]

/-- `h_0 = 1`. -/
@[simp] theorem normalizedHermite_zero (x : ℝ) : normalizedHermite 0 x = 1 := by
  simp only [normalizedHermite, hermite_zero, map_one, Nat.factorial_zero, Nat.cast_one,
    sqrt_one, div_one]

/-- `h_1 x = x`. -/
@[simp] theorem normalizedHermite_one (x : ℝ) : normalizedHermite 1 x = x := by
  simp only [normalizedHermite, hermite_one, aeval_X, Nat.factorial_one, Nat.cast_one, sqrt_one,
    div_one]

/-- `h_2 x = (x² - 1) / √2`. -/
theorem normalizedHermite_two (x : ℝ) : normalizedHermite 2 x = (x ^ 2 - 1) / √2 := by
  rw [normalizedHermite, show hermite 2 = X ^ 2 - 1 by
    rw [hermite_succ_succ, hermite_one, hermite_zero, C_1]; ring]
  norm_num

/-- The normalized Hermite polynomials are continuous. -/
@[fun_prop] theorem continuous_normalizedHermite (j : ℕ) : Continuous (normalizedHermite j) :=
  ((hermite j).continuous_aeval).div_const _

/-- **Orthonormality of the normalized Hermite polynomials**
[O'Donnell, Proposition 11.30][ODonnell2014] (without completeness, which is
`normalizedHermiteBasis`): `⟨h_j, h_k⟩ = 1` if `j = k` and `0` otherwise, in `L²` of the standard
Gaussian. -/
theorem integral_normalizedHermite_mul_normalizedHermite (j k : ℕ) :
    ∫ x, normalizedHermite j x * normalizedHermite k x ∂gaussianReal 0 1 =
      if j = k then 1 else 0 := by
  simp only [normalizedHermite, div_mul_div_comm]
  rw [integral_div, integral_aeval_hermite_mul_aeval_hermite]
  split_ifs with h
  · subst h
    rw [← sq, sq_sqrt (Nat.cast_nonneg _), div_self (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _))]
  · rw [zero_div]

/-- **Normalized Hermite polynomials are eigenfunctions of the Gaussian noise operator**, in one
dimension; the identity behind [O'Donnell, Proposition 11.31][ODonnell2014]: for `|ρ| ≤ 1`,
`E_g[h_n (ρ x + √(1 - ρ²) g)] = ρ ^ n h_n x` for a standard Gaussian `g`. -/
theorem integral_normalizedHermite_gaussianNoise {ρ : ℝ} (hρ : |ρ| ≤ 1) (n : ℕ) (x : ℝ) :
    ∫ g, normalizedHermite n (ρ * x + √(1 - ρ ^ 2) * g) ∂gaussianReal 0 1 =
      ρ ^ n * normalizedHermite n x := by
  simp only [normalizedHermite]
  rw [integral_div, integral_aeval_hermite_gaussianNoise hρ, mul_div_assoc]

/-- Products of normalized Hermite polynomials are integrable under the standard Gaussian. -/
private theorem integrable_normalizedHermite_mul (j k : ℕ) :
    Integrable (fun x => normalizedHermite j x * normalizedHermite k x) (gaussianReal 0 1) := by
  refine ((integrable_eval_gaussianReal (hermiteR j * hermiteR k)).div_const
    (√(j ! : ℝ) * √(k ! : ℝ))).congr (ae_of_all _ fun x => ?_)
  simp only [normalizedHermite, aeval_hermite, eval_mul, div_mul_div_comm]

/-- The normalized Hermite polynomials lie in `L²` of the standard Gaussian. -/
theorem memLp_normalizedHermite (j : ℕ) : MemLp (normalizedHermite j) 2 (gaussianReal 0 1) :=
  (memLp_two_iff_integrable_sq (continuous_normalizedHermite j).aestronglyMeasurable).2
    (by simpa only [sq] using integrable_normalizedHermite_mul j j)

end Univariate

/-! ### Multivariate Hermite polynomials -/

section Multivariate

variable {ι : Type*} [Fintype ι]

/-- The **multivariate Hermite polynomial** `h_α z = ∏ i, h_{α i} (z i)` of a multi-index
`α : ι → ℕ` [O'Donnell, Definition 11.32][ODonnell2014], as a function on `ι → ℝ`. Its total
degree is `|α| = ∑ i, α i`. -/
noncomputable def multiHermite (α : ι → ℕ) (z : ι → ℝ) : ℝ :=
  ∏ i, normalizedHermite (α i) (z i)

/-- Unfolding `h_α z = ∏ i, h_{α i} (z i)`. -/
theorem multiHermite_def (α : ι → ℕ) (z : ι → ℝ) :
    multiHermite α z = ∏ i, normalizedHermite (α i) (z i) := by
  rw [multiHermite]

/-- The multivariate Hermite polynomials are continuous. -/
@[fun_prop] theorem continuous_multiHermite (α : ι → ℕ) : Continuous (multiHermite α) :=
  continuous_finsetProd _ fun i _ => (continuous_normalizedHermite (α i)).comp (continuous_apply i)

/-- **The multivariate Hermite polynomials of subsets**
[O'Donnell, Definition 11.32 and Remark 11.35][ODonnell2014]: for the indicator multi-index of
`S`, `h_S z = ∏ i ∈ S, zᵢ`. Hence a multilinear polynomial `∑_S c_S ∏ i ∈ S, zᵢ` is the
combination `∑_S c_S h_S`. That this is its Hermite expansion, the rest of Remark 11.35, is
`hermiteCoeff_sum_mul_prod` in the module
`CslibFrontier.Foundations.Probability.Gaussian.HermiteExpansion`. -/
theorem multiHermite_indicator [DecidableEq ι] (S : Finset ι) (z : ι → ℝ) :
    multiHermite (fun i => if i ∈ S then 1 else 0) z = ∏ i ∈ S, z i := by
  have h (i : ι) : normalizedHermite (if i ∈ S then 1 else 0) (z i) = if i ∈ S then z i else 1 := by
    split_ifs
    · exact normalizedHermite_one _
    · exact normalizedHermite_zero _
  simp only [multiHermite, h, Fintype.prod_ite_mem]

/-- **Multivariate Hermite polynomials are eigenfunctions of the Gaussian noise operator**, the
identity behind [O'Donnell, Propositions 11.33 and 11.37][ODonnell2014]: for `|ρ| ≤ 1`,
`U_ρ h_α = ρ ^ |α| h_α`. -/
theorem gaussianNoiseOp_multiHermite {ρ : ℝ} (hρ : |ρ| ≤ 1) (α : ι → ℕ) (z : ι → ℝ) :
    gaussianNoiseOp ρ (multiHermite α) z = ρ ^ (∑ i, α i) * multiHermite α z := by
  simp only [gaussianNoiseOp, multiHermite]
  rw [integral_fintype_prod_eq_prod
    (fun i t => normalizedHermite (α i) (ρ * z i + √(1 - ρ ^ 2) * t))]
  simp only [integral_normalizedHermite_gaussianNoise hρ]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

/-- The products `h_α h_β` are integrable under the standard Gaussian. -/
theorem integrable_multiHermite_mul (α β : ι → ℕ) :
    Integrable (fun z => multiHermite α z * multiHermite β z)
      (Measure.pi fun _ : ι => gaussianReal 0 1) := by
  simp only [multiHermite, ← Finset.prod_mul_distrib]
  exact Integrable.fintype_prod (f := fun i t => normalizedHermite (α i) t *
    normalizedHermite (β i) t) fun i => integrable_normalizedHermite_mul (α i) (β i)

/-- The multivariate Hermite polynomials lie in `L²(γⁿ)`. -/
theorem memLp_multiHermite (α : ι → ℕ) :
    MemLp (multiHermite α) 2 (Measure.pi fun _ : ι => gaussianReal 0 1) :=
  (memLp_two_iff_integrable_sq (continuous_multiHermite α).aestronglyMeasurable).2
    (by simpa only [sq] using integrable_multiHermite_mul α α)

/-- **Orthonormality of the multivariate Hermite polynomials**
[O'Donnell, Proposition 11.33][ODonnell2014] (without completeness, which is `hermiteBasis`):
`⟨h_α, h_β⟩ = 1` if `α = β` and `0` otherwise, in `L²(γⁿ)`. -/
theorem integral_multiHermite_mul_multiHermite (α β : ι → ℕ) :
    ∫ z, multiHermite α z * multiHermite β z ∂Measure.pi (fun _ : ι => gaussianReal 0 1) =
      if α = β then 1 else 0 := by
  simp only [multiHermite, ← Finset.prod_mul_distrib]
  rw [integral_fintype_prod_eq_prod
    (fun i t => normalizedHermite (α i) t * normalizedHermite (β i) t)]
  simp only [integral_normalizedHermite_mul_normalizedHermite, Fintype.prod_boole, funext_iff]

/-- **Correlations of multivariate Hermite polynomials**
[O'Donnell, Proposition 11.33][ODonnell2014]: for `|ρ| ≤ 1`, `⟨h_α, U_ρ h_β⟩ = ρ ^ |α|` if
`α = β` and `0` otherwise. By self-adjointness (`integral_mul_gaussianNoiseOp_comm`) this is
also `⟨U_ρ h_α, h_β⟩`. -/
theorem integral_multiHermite_mul_gaussianNoiseOp {ρ : ℝ} (hρ : |ρ| ≤ 1) (α β : ι → ℕ) :
    ∫ z, multiHermite α z * gaussianNoiseOp ρ (multiHermite β) z
        ∂Measure.pi (fun _ : ι => gaussianReal 0 1) =
      if α = β then ρ ^ (∑ i, α i) else 0 := by
  simp only [gaussianNoiseOp_multiHermite hρ, mul_left_comm (multiHermite α _)]
  rw [integral_const_mul, integral_multiHermite_mul_multiHermite]
  split_ifs with h
  · rw [h, mul_one]
  · rw [mul_zero]

/-- **Correlations of multivariate Hermite polynomials**
[O'Donnell, Proposition 11.33][ODonnell2014]: for `ρ`-correlated standard Gaussian vectors
`(z, z')` with `|ρ| ≤ 1`, `E[h_α z h_β z'] = ρ ^ |α|` if `α = β` and `0` otherwise. -/
theorem integral_correlatedGaussianPi_multiHermite {ρ : ℝ} (hρ : |ρ| ≤ 1) (α β : ι → ℕ) :
    ∫ p, multiHermite α p.1 * multiHermite β p.2 ∂correlatedGaussianPi ι ρ =
      if α = β then ρ ^ (∑ i, α i) else 0 := by
  rw [← integral_mul_gaussianNoiseOp hρ (memLp_multiHermite α) (memLp_multiHermite β),
    integral_multiHermite_mul_gaussianNoiseOp hρ]

/-- **Correlations of normalized Hermite polynomials** [O'Donnell, Proposition 11.31][ODonnell2014]:
for `ρ`-correlated standard Gaussians `(z, z')` with `|ρ| ≤ 1`, `E[h_j z h_k z'] = ρ ^ j` if
`j = k` and `0` otherwise. This is the one-dimensional case of
`integral_correlatedGaussianPi_multiHermite`. -/
theorem integral_correlatedGaussian_normalizedHermite {ρ : ℝ} (hρ : |ρ| ≤ 1) (j k : ℕ) :
    ∫ p, normalizedHermite j p.1 * normalizedHermite k p.2 ∂correlatedGaussian ρ =
      if j = k then ρ ^ j else 0 := by
  rw [← correlatedGaussianPi_map_eval Unit ρ (), integral_map (by fun_prop) (by fun_prop)]
  have h := integral_correlatedGaussianPi_multiHermite (ι := Unit) hρ (fun _ => j) (fun _ => k)
  simp only [multiHermite, Finset.univ_unique, Finset.prod_singleton, Finset.sum_singleton,
    funext_iff, forall_const] at h
  exact h

end Multivariate

end ProbabilityTheory
