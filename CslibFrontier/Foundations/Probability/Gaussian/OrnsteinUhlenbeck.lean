/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate (Mathlib, a new file `Mathlib/Probability/Distributions/Gaussian/`
-- `OrnsteinUhlenbeck.lean`)

public import CslibFrontier.Foundations.Probability.Gaussian.HermiteExpansion
import CslibFrontier.Foundations.MeasureTheory.Integral.PiUpdate
import CslibFrontier.Foundations.Probability.Gaussian.Stein
import CslibFrontier.Foundations.RingTheory.Polynomial.Hermite
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The Ornstein–Uhlenbeck operator

The *Ornstein–Uhlenbeck operator* `L f = (d/dρ) U_ρ f |_{ρ = 1}`
[O'Donnell, Definition 11.24][ODonnell2014] is the infinitesimal generator of the Gaussian noise
operators `U_ρ`; in the exponential parametrization `ρ = e^{-t}` it is
`L f = -(d/dt) U_{e^{-t}} f |_{t = 0}`. On a smooth `f` it is the differential operator
`L f = x · ∇f - Δf` (Proposition 11.26), it satisfies the integration by parts formula
`⟨L f, g⟩ = ⟨∇f, ∇g⟩` (Proposition 11.28), and it gives the derivative of `U_ρ f`:
`(d/dρ) U_ρ f = ρ⁻¹ L U_ρ f = ρ⁻¹ U_ρ L f` (Proposition 11.27). Throughout, `γⁿ` is
`Measure.pi fun _ : ι => gaussianReal 0 1` and `|α| = ∑ i, α i`.

* **The Hermite polynomials in differential form** (Propositions 11.26 and 11.40): `h_α` satisfies
  `x · ∇h_α - Δh_α = |α| h_α`, with the coordinate partial derivatives written as derivatives of
  `t ↦ h_α (Function.update z i t)` (`sum_mul_deriv_multiHermite_update_sub`); in one dimension
  this is `x h_n' - h_n'' = n h_n` (`mul_deriv_normalizedHermite_sub`), from the Hermite
  differential equation `Polynomial.X_mul_derivative_hermite_sub` (Exercise 11.10(c)).
* **Integration by parts** (Proposition 11.28, Exercise 11.8): in one dimension, for a twice
  differentiable `f` and a differentiable `g`, `E[(x f' - f'') g] = E[f' g']` under the standard
  Gaussian, given the integrability of the terms
  (`integral_mul_deriv_sub_deriv_deriv_mul_gaussianReal`). This is Stein's lemma
  (`integral_sub_mul_gaussianReal`) applied to `f' g`. In `n` dimensions,
  `E[(x · ∇f - Δf) g] = ∑ i, E[∂ᵢf ∂ᵢg]` under `γⁿ`
  (`integral_sum_mul_deriv_update_sub_mul_pi_gaussianReal`), with partial derivatives along
  coordinate lines as above; each coordinate reduces to one dimension by Fubini along that
  coordinate (`MeasureTheory.integral_integral_update`,
  `integral_mul_deriv_update_sub_mul_pi_gaussianReal`).
* **`L` on `L²`** (Definition 11.24, Proposition 11.40, Exercise 11.18): `ornsteinUhlenbeck f` is
  the series `L f = ∑ α, |α| f̂(α) h_α` in `L²(γⁿ)`, and its domain
  `MemOrnsteinUhlenbeckDomain f` is `f ∈ L²(γⁿ)` with `∑ α, |α|² f̂(α)² < ∞`. On the domain, the
  `L²`-valued map `ρ ↦ U_ρ f` has left derivative `L f` at `ρ = 1`
  (`hasDerivWithinAt_gaussianNoiseOp`), equivalently `t ↦ U_{e^{-t}} f` has right derivative
  `-L f` at `t = 0` (`hasDerivWithinAt_gaussianNoiseOp_exp_neg_zero`). Conversely, for
  `f ∈ L²(γⁿ)`, every left derivative at `ρ = 1` is `L f`
  (`eq_ornsteinUhlenbeck_of_hasDerivWithinAt`), and one exists iff `f` is in the domain
  (`exists_hasDerivWithinAt_gaussianNoiseOp_iff`). The `α`-th Hermite coordinate of
  `(σ - ρ)⁻¹ (U_σ f - U_ρ f)` is `slope (· ^ |α|) ρ σ f̂(α)`; it tends to
  `|α| ρ ^ (|α| - 1) f̂(α)` as `σ → ρ` and is bounded by `|α| r ^ (|α| - 1) |f̂(α)|` for
  `|σ|, |ρ| ≤ r` (`abs_pow_sub_pow_le`), so dominated convergence of the coordinates gives the
  `L²` limits.
* **Smoothing** (Exercise 11.18(c)): for `f ∈ L²(γⁿ)` and `|ρ| < 1`, `U_ρ f` is in the domain of
  `L` (`memOrnsteinUhlenbeckDomain_gaussianNoiseOp`), since `m² ρ ^ (2 m)` is bounded.
* **The derivative of `U_ρ f`** (Proposition 11.27): for `f ∈ L²(γⁿ)` and `|ρ| < 1`, `ρ ↦ U_ρ f`
  is differentiable at `ρ`, with derivative `∑ α, |α| ρ ^ (|α| - 1) f̂(α) h_α`
  (`hasDerivAt_gaussianNoiseOp`, which covers `ρ = 0`); for `f` in the domain of `L`, the map
  restricted to `[-1, 1]` has this derivative at every `ρ ∈ [-1, 1]`
  (`hasDerivWithinAt_Icc_gaussianNoiseOp`). For `ρ ≠ 0` the
  derivative is `ρ⁻¹ L U_ρ f` (`hasDerivAt_gaussianNoiseOp_eq_inv_smul_ornsteinUhlenbeck`), and
  `ρ⁻¹ U_ρ L f` for `f` in the domain (`hasDerivAt_gaussianNoiseOp_eq_inv_smul_gaussianNoiseOp`),
  by `L U_ρ f = U_ρ L f` (`ornsteinUhlenbeck_gaussianNoiseOp`). In exponential time,
  `(d/dt) U_{e^{-t}} f = -L U_{e^{-t}} f` for `t > 0` (`hasDerivAt_gaussianNoiseOp_exp_neg`). The
  book derives Proposition 11.27 from the semigroup property; here it is read off the Hermite
  expansion `U_ρ f = ∑ α, ρ ^ |α| f̂(α) h_α`.

Not formalized here: Proposition 11.26 for general smooth `f` (the identification of the series
`L f` with `x · ∇f - Δf` is proved only for Hermite polynomials), the symmetric form
`⟨f, L g⟩ = ⟨L f, g⟩` of Proposition 11.28 for `L` on `L²`, and the derivatives of `U_ρ f` in
the pointwise (rather than `L²`) sense. `L` is a function on all of `(ι → ℝ) → ℝ` with a
separate domain predicate, not an unbounded operator in the sense of Mathlib's
`LinearPMap`.

## Main definitions

* `ProbabilityTheory.ornsteinUhlenbeck`: the Ornstein–Uhlenbeck operator
  `L f = ∑ α, |α| f̂(α) h_α`.
* `ProbabilityTheory.MemOrnsteinUhlenbeckDomain`: its domain, `f ∈ L²(γⁿ)` with
  `∑ α, |α|² f̂(α)² < ∞`.

## Main results

* `ProbabilityTheory.mul_deriv_normalizedHermite_sub`,
  `ProbabilityTheory.sum_mul_deriv_multiHermite_update_sub`: Hermite polynomials are
  eigenfunctions of `x · ∇ - Δ`.
* `ProbabilityTheory.integral_mul_deriv_sub_deriv_deriv_mul_gaussianReal`: Proposition 11.28 in
  one dimension.
* `ProbabilityTheory.integral_sum_mul_deriv_update_sub_mul_pi_gaussianReal`: Proposition 11.28 in
  `n` dimensions (Exercise 11.8); one coordinate is
  `ProbabilityTheory.integral_mul_deriv_update_sub_mul_pi_gaussianReal`.
* `ProbabilityTheory.hermiteBasis_repr_ornsteinUhlenbeck`,
  `ProbabilityTheory.hermiteCoeff_ornsteinUhlenbeck`: `(L f)^(α) = |α| f̂(α)`
  (Proposition 11.40).
* `ProbabilityTheory.hasDerivWithinAt_gaussianNoiseOp`,
  `ProbabilityTheory.eq_ornsteinUhlenbeck_of_hasDerivWithinAt`,
  `ProbabilityTheory.hasDerivWithinAt_gaussianNoiseOp_exp_neg_zero`: `L f` is the derivative of
  `ρ ↦ U_ρ f` at `ρ = 1` (Definition 11.24, Proposition 11.40).
* `ProbabilityTheory.exists_hasDerivWithinAt_gaussianNoiseOp_iff`,
  `ProbabilityTheory.memOrnsteinUhlenbeckDomain_of_hasDerivWithinAt`: Exercise 11.18, the domain
  of `L`.
* `ProbabilityTheory.memOrnsteinUhlenbeckDomain_gaussianNoiseOp`: Exercise 11.18(c);
  `ProbabilityTheory.MemOrnsteinUhlenbeckDomain.gaussianNoiseOp`: `U_ρ` preserves the domain.
* `ProbabilityTheory.ornsteinUhlenbeck_gaussianNoiseOp`: `L U_ρ f = U_ρ L f`.
* `ProbabilityTheory.hasDerivWithinAt_Icc_gaussianNoiseOp`,
  `ProbabilityTheory.hasDerivAt_gaussianNoiseOp`,
  `ProbabilityTheory.hasDerivAt_gaussianNoiseOp_eq_inv_smul_ornsteinUhlenbeck`,
  `ProbabilityTheory.hasDerivAt_gaussianNoiseOp_eq_inv_smul_gaussianNoiseOp`,
  `ProbabilityTheory.hasDerivAt_gaussianNoiseOp_exp_neg`: Proposition 11.27.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

open MeasureTheory Real Polynomial Filter
open scoped Nat Topology

namespace ProbabilityTheory

/-! ### The Hermite polynomials in differential form -/

/-- The derivative of `x ↦ q(x) c` for an integer polynomial `q`. -/
private theorem deriv_aeval_mul_const (q : ℤ[X]) (c : ℝ) :
    deriv (fun x : ℝ => aeval x q * c) = fun x => aeval x (derivative q) * c := by
  funext x
  rw [deriv_mul_const (Polynomial.differentiable_aeval q x), Polynomial.deriv_aeval]

/-- `h_n x = H_n x · (√(n!))⁻¹`. -/
private theorem normalizedHermite_eq_mul (n : ℕ) :
    normalizedHermite n = fun x => aeval x (hermite n) * (√(n ! : ℝ))⁻¹ := by
  funext x
  rw [normalizedHermite_def, div_eq_mul_inv]

/-- The Hermite differential equation, evaluated: `x H_n' x - H_n'' x = n H_n x`. -/
private theorem aeval_X_mul_derivative_hermite_sub (n : ℕ) (x : ℝ) :
    x * aeval x (derivative (hermite n)) - aeval x (derivative (derivative (hermite n))) =
      n * aeval x (hermite n) := by
  have h := congrArg (aeval x) (X_mul_derivative_hermite_sub n)
  simpa only [map_sub, map_mul, aeval_X, map_natCast] using h

/-- **The normalized Hermite polynomials are eigenfunctions of the Ornstein–Uhlenbeck operator**
in differential form [O'Donnell, Propositions 11.26 and 11.40][ODonnell2014], in one dimension:
`x h_n' x - h_n'' x = n h_n x`. This is the Hermite differential equation
[O'Donnell, Exercise 11.10(c)][ODonnell2014] (`Polynomial.X_mul_derivative_hermite_sub`). -/
theorem mul_deriv_normalizedHermite_sub (n : ℕ) (x : ℝ) :
    x * deriv (normalizedHermite n) x - deriv (deriv (normalizedHermite n)) x =
      n * normalizedHermite n x := by
  rw [normalizedHermite_eq_mul, deriv_aeval_mul_const, deriv_aeval_mul_const]
  linear_combination (√(n ! : ℝ))⁻¹ * aeval_X_mul_derivative_hermite_sub n x

variable {ι : Type*} [Fintype ι]

/-- Along the `i`-th coordinate line through `z`, `h_α` is `H_{α i}` times a constant. -/
private theorem multiHermite_update [DecidableEq ι] (α : ι → ℕ) (z : ι → ℝ) (i : ι) :
    (fun t => multiHermite α (Function.update z i t)) = fun t =>
      aeval t (hermite (α i)) * ((√((α i) ! : ℝ))⁻¹ *
        ∏ j ∈ Finset.univ.erase i, normalizedHermite (α j) (z j)) := by
  funext t
  rw [multiHermite_def, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i), Function.update_self,
    normalizedHermite_def, div_eq_mul_inv, mul_assoc]
  congr 2
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

/-- **The multivariate Hermite polynomials are eigenfunctions of the Ornstein–Uhlenbeck
operator** in differential form [O'Donnell, Propositions 11.26 and 11.40][ODonnell2014]:
`x · ∇h_α - Δh_α = |α| h_α`. The `i`-th partial derivatives `∂ᵢ h_α z` and `∂ᵢ² h_α z` are the
first and second derivatives of `t ↦ h_α (Function.update z i t)` at `t = z i`. -/
theorem sum_mul_deriv_multiHermite_update_sub [DecidableEq ι] (α : ι → ℕ) (z : ι → ℝ) :
    ∑ i, (z i * deriv (fun t => multiHermite α (Function.update z i t)) (z i) -
        deriv (deriv fun t => multiHermite α (Function.update z i t)) (z i)) =
      ((∑ i, α i : ℕ) : ℝ) * multiHermite α z := by
  rw [Nat.cast_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hz := congrFun (multiHermite_update α z i) (z i)
  rw [Function.update_eq_self] at hz
  rw [multiHermite_update, deriv_aeval_mul_const, deriv_aeval_mul_const, hz]
  linear_combination ((√((α i) ! : ℝ))⁻¹ *
    ∏ j ∈ Finset.univ.erase i, normalizedHermite (α j) (z j)) *
      aeval_X_mul_derivative_hermite_sub (α i) (z i)

/-! ### Integration by parts -/

/-- **Gaussian integration by parts for the Ornstein–Uhlenbeck operator**
[O'Donnell, Proposition 11.28][ODonnell2014], in one dimension: for `f` with differentiable
derivative `f'` and differentiable `g`, `⟨x f' - f'', g⟩ = ⟨f', g'⟩` in `L²` of the standard
Gaussian, that is, `⟨L f, g⟩ = ⟨∇f, ∇g⟩` with `L f = x f' - f''` (Proposition 11.26). The book
assumes `f, g` are `C³` and in the domain of `L`; here the four integrability hypotheses are what
Stein's lemma for `f' g` needs. -/
theorem integral_mul_deriv_sub_deriv_deriv_mul_gaussianReal {f g : ℝ → ℝ}
    (hf : Differentiable ℝ (deriv f)) (hg : Differentiable ℝ g)
    (h₁ : Integrable (fun x => deriv f x * g x) (gaussianReal 0 1))
    (h₂ : Integrable (fun x => x * deriv f x * g x) (gaussianReal 0 1))
    (h₃ : Integrable (fun x => deriv (deriv f) x * g x) (gaussianReal 0 1))
    (h₄ : Integrable (fun x => deriv f x * deriv g x) (gaussianReal 0 1)) :
    ∫ x, (x * deriv f x - deriv (deriv f) x) * g x ∂gaussianReal 0 1 =
      ∫ x, deriv f x * deriv g x ∂gaussianReal 0 1 := by
  have hS := integral_sub_mul_gaussianReal (μ := 0) (v := 1) (f := fun x => deriv f x * g x)
    (fun x => (hf x).hasDerivAt.mul (hg x).hasDerivAt) h₁
    (h₂.congr (ae_of_all _ fun x => by simp only [sub_zero, mul_assoc]))
    (h₃.add h₄)
  simp only [sub_zero, NNReal.coe_one, one_mul] at hS
  have e : (fun x => (x * deriv f x - deriv (deriv f) x) * g x) =
      fun x => x * (deriv f x * g x) - deriv (deriv f) x * g x := by
    funext x
    ring
  rw [e, integral_sub (h₂.congr (ae_of_all _ fun x => by simp only [mul_assoc])) h₃, hS,
    integral_add h₃ h₄, add_sub_cancel_left]

/-- **Gaussian integration by parts along one coordinate**
[O'Donnell, Proposition 11.28 and Exercise 11.8][ODonnell2014]: under `γⁿ`,
`⟨x_i ∂ᵢf - ∂ᵢ²f, g⟩ = ⟨∂ᵢf, ∂ᵢg⟩`, where `∂ᵢ f z` and `∂ᵢ² f z` are the first and second
derivatives of `t ↦ f (Function.update z i t)` at `t = z i`. Fubini along the `i`-th coordinate
reduces this to the one-dimensional `integral_mul_deriv_sub_deriv_deriv_mul_gaussianReal`; the four
integrability hypotheses are the `n`-dimensional versions of those there. -/
theorem integral_mul_deriv_update_sub_mul_pi_gaussianReal [DecidableEq ι] {f g : (ι → ℝ) → ℝ}
    (i : ι) (hf : ∀ z, Differentiable ℝ (deriv fun t => f (Function.update z i t)))
    (hg : ∀ z, Differentiable ℝ fun t => g (Function.update z i t))
    (h₁ : Integrable (fun z => deriv (fun t => f (Function.update z i t)) (z i) * g z)
      (Measure.pi fun _ : ι => gaussianReal 0 1))
    (h₂ : Integrable (fun z => z i * deriv (fun t => f (Function.update z i t)) (z i) * g z)
      (Measure.pi fun _ : ι => gaussianReal 0 1))
    (h₃ : Integrable (fun z => deriv (deriv fun t => f (Function.update z i t)) (z i) * g z)
      (Measure.pi fun _ : ι => gaussianReal 0 1))
    (h₄ : Integrable (fun z => deriv (fun t => f (Function.update z i t)) (z i) *
      deriv (fun t => g (Function.update z i t)) (z i))
      (Measure.pi fun _ : ι => gaussianReal 0 1)) :
    ∫ z, (z i * deriv (fun t => f (Function.update z i t)) (z i) -
        deriv (deriv fun t => f (Function.update z i t)) (z i)) * g z
        ∂Measure.pi (fun _ : ι => gaussianReal 0 1) =
      ∫ z, deriv (fun t => f (Function.update z i t)) (z i) *
        deriv (fun t => g (Function.update z i t)) (z i)
        ∂Measure.pi (fun _ : ι => gaussianReal 0 1) := by
  have h₀ : Integrable (fun z => (z i * deriv (fun t => f (Function.update z i t)) (z i) -
      deriv (deriv fun t => f (Function.update z i t)) (z i)) * g z)
      (Measure.pi fun _ : ι => gaussianReal 0 1) :=
    (h₂.sub h₃).congr (ae_of_all _ fun z => by simp only [Pi.sub_apply]; ring)
  rw [← integral_integral_update _ h₀ i, ← integral_integral_update _ h₄ i]
  refine integral_congr_ae ?_
  filter_upwards [ae_integrable_update _ h₁ i, ae_integrable_update _ h₂ i,
    ae_integrable_update _ h₃ i, ae_integrable_update _ h₄ i] with z hz₁ hz₂ hz₃ hz₄
  simp only [Function.update_self, Function.update_idem] at hz₁ hz₂ hz₃ hz₄ ⊢
  exact integral_mul_deriv_sub_deriv_deriv_mul_gaussianReal (hf z) (hg z) hz₁ hz₂ hz₃ hz₄

/-- **Gaussian integration by parts for the Ornstein–Uhlenbeck operator**
[O'Donnell, Proposition 11.28 and Exercise 11.8][ODonnell2014]: under `γⁿ`,
`⟨x · ∇f - Δf, g⟩ = ∑ i, ⟨∂ᵢf, ∂ᵢg⟩ = ⟨∇f, ∇g⟩`, that is, `⟨L f, g⟩ = ⟨∇f, ∇g⟩` with
`L f = x · ∇f - Δf` (Proposition 11.26). The partial derivatives `∂ᵢ f z` and `∂ᵢ² f z` are the
first and second derivatives of `t ↦ f (Function.update z i t)` at `t = z i`, as in
`sum_mul_deriv_multiHermite_update_sub`. The book assumes `f, g` are `C³` and in the domain of
`L`; here each coordinate carries the hypotheses of
`integral_mul_deriv_update_sub_mul_pi_gaussianReal`. -/
theorem integral_sum_mul_deriv_update_sub_mul_pi_gaussianReal [DecidableEq ι]
    {f g : (ι → ℝ) → ℝ}
    (hf : ∀ i z, Differentiable ℝ (deriv fun t => f (Function.update z i t)))
    (hg : ∀ i z, Differentiable ℝ fun t => g (Function.update z i t))
    (h₁ : ∀ i, Integrable (fun z => deriv (fun t => f (Function.update z i t)) (z i) * g z)
      (Measure.pi fun _ : ι => gaussianReal 0 1))
    (h₂ : ∀ i, Integrable (fun z => z i * deriv (fun t => f (Function.update z i t)) (z i) * g z)
      (Measure.pi fun _ : ι => gaussianReal 0 1))
    (h₃ : ∀ i, Integrable (fun z => deriv (deriv fun t => f (Function.update z i t)) (z i) * g z)
      (Measure.pi fun _ : ι => gaussianReal 0 1))
    (h₄ : ∀ i, Integrable (fun z => deriv (fun t => f (Function.update z i t)) (z i) *
      deriv (fun t => g (Function.update z i t)) (z i))
      (Measure.pi fun _ : ι => gaussianReal 0 1)) :
    ∫ z, (∑ i, (z i * deriv (fun t => f (Function.update z i t)) (z i) -
        deriv (deriv fun t => f (Function.update z i t)) (z i))) * g z
        ∂Measure.pi (fun _ : ι => gaussianReal 0 1) =
      ∑ i, ∫ z, deriv (fun t => f (Function.update z i t)) (z i) *
        deriv (fun t => g (Function.update z i t)) (z i)
        ∂Measure.pi (fun _ : ι => gaussianReal 0 1) := by
  simp only [Finset.sum_mul]
  rw [integral_finsetSum _ fun i _ => ((h₂ i).sub (h₃ i)).congr
    (ae_of_all _ fun z => by simp only [Pi.sub_apply]; ring)]
  exact Finset.sum_congr rfl fun i _ =>
    integral_mul_deriv_update_sub_mul_pi_gaussianReal i (hf i) (hg i) (h₁ i) (h₂ i) (h₃ i) (h₄ i)

/-! ### The Ornstein–Uhlenbeck operator on `L²` -/

/-- The **domain of the Ornstein–Uhlenbeck operator** [O'Donnell, Exercise 11.18][ODonnell2014]:
`f ∈ L²(γⁿ)` with `∑ α, |α|² f̂(α)² < ∞`, where `|α| = ∑ i, α i`. By
`exists_hasDerivWithinAt_gaussianNoiseOp_iff`, these are the `f ∈ L²(γⁿ)` for which
`ρ ↦ U_ρ f` has a left derivative in `L²(γⁿ)` at `ρ = 1`. -/
def MemOrnsteinUhlenbeckDomain (f : (ι → ℝ) → ℝ) : Prop :=
  MemLp f 2 (Measure.pi fun _ : ι => gaussianReal 0 1) ∧
    Summable fun α : ι → ℕ => ((∑ i, α i : ℕ) : ℝ) ^ 2 * hermiteCoeff f α ^ 2

/-- Unfolding the domain of the Ornstein–Uhlenbeck operator. -/
theorem memOrnsteinUhlenbeckDomain_iff {f : (ι → ℝ) → ℝ} :
    MemOrnsteinUhlenbeckDomain f ↔ MemLp f 2 (Measure.pi fun _ : ι => gaussianReal 0 1) ∧
      Summable fun α : ι → ℕ => ((∑ i, α i : ℕ) : ℝ) ^ 2 * hermiteCoeff f α ^ 2 := by
  rw [MemOrnsteinUhlenbeckDomain]

/-- A function in the domain of `L` is in `L²(γⁿ)`. -/
theorem MemOrnsteinUhlenbeckDomain.memLp {f : (ι → ℝ) → ℝ} (hf : MemOrnsteinUhlenbeckDomain f) :
    MemLp f 2 (Measure.pi fun _ : ι => gaussianReal 0 1) :=
  (memOrnsteinUhlenbeckDomain_iff.1 hf).1

/-- For `f` in the domain of `L`, `∑ α, |α|² f̂(α)² < ∞`. -/
theorem MemOrnsteinUhlenbeckDomain.summable {f : (ι → ℝ) → ℝ}
    (hf : MemOrnsteinUhlenbeckDomain f) :
    Summable fun α : ι → ℕ => ((∑ i, α i : ℕ) : ℝ) ^ 2 * hermiteCoeff f α ^ 2 :=
  (memOrnsteinUhlenbeckDomain_iff.1 hf).2

/-- The family `α ↦ |α| c(α)` is square-summable iff `∑ α, |α|² c(α)²` converges. -/
theorem memℓp_two_sum_mul_iff {c : (ι → ℕ) → ℝ} :
    Memℓp (fun α : ι → ℕ => ((∑ i, α i : ℕ) : ℝ) * c α) 2 ↔
      Summable fun α : ι → ℕ => ((∑ i, α i : ℕ) : ℝ) ^ 2 * c α ^ 2 := by
  simp only [memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal), ENNReal.toReal_ofNat,
    Real.rpow_two, Real.norm_eq_abs, sq_abs, mul_pow]

/-- The **Ornstein–Uhlenbeck operator** `L f = ∑ α, |α| f̂(α) h_α` on `L²(γⁿ)`
[O'Donnell, Definition 11.24 and Proposition 11.40][ODonnell2014]. The book defines `L f` as the
derivative `(d/dρ) U_ρ f |_{ρ = 1}`; for `f` in the domain of `L` (`MemOrnsteinUhlenbeckDomain`),
`hasDerivWithinAt_gaussianNoiseOp` shows that this series is that left derivative, and
`eq_ornsteinUhlenbeck_of_hasDerivWithinAt` that it is the only one. Outside the domain the series
need not converge, and the value is then that of `tsum`. -/
noncomputable def ornsteinUhlenbeck (f : (ι → ℝ) → ℝ) :
    Lp ℝ 2 (Measure.pi fun _ : ι => gaussianReal 0 1) :=
  ∑' α, (((∑ i, α i : ℕ) : ℝ) * hermiteCoeff f α) • hermiteBasis ι α

/-- Unfolding `L f = ∑ α, |α| f̂(α) h_α`. -/
theorem ornsteinUhlenbeck_def (f : (ι → ℝ) → ℝ) :
    ornsteinUhlenbeck f = ∑' α, (((∑ i, α i : ℕ) : ℝ) * hermiteCoeff f α) • hermiteBasis ι α := by
  rw [ornsteinUhlenbeck]

/-- **The Hermite coordinates of `L f`** [O'Donnell, Proposition 11.40][ODonnell2014]: for `f` in
the domain of `L`, the `α`-th Hermite coordinate of `L f` is `|α| f̂(α)`. -/
theorem hermiteBasis_repr_ornsteinUhlenbeck {f : (ι → ℝ) → ℝ}
    (hf : MemOrnsteinUhlenbeckDomain f) (α : ι → ℕ) :
    (hermiteBasis ι).repr (ornsteinUhlenbeck f) α = ((∑ i, α i : ℕ) : ℝ) * hermiteCoeff f α :=
  hermiteBasis_repr_tsum_smul (memℓp_two_sum_mul_iff.2 hf.summable) α

/-- **The Hermite coefficients of `L f`** [O'Donnell, Proposition 11.40][ODonnell2014]: for `f` in
the domain of `L`, `(L f)^(α) = |α| f̂(α)`. -/
theorem hermiteCoeff_ornsteinUhlenbeck {f : (ι → ℝ) → ℝ} (hf : MemOrnsteinUhlenbeckDomain f)
    (α : ι → ℕ) :
    hermiteCoeff (⇑(ornsteinUhlenbeck f)) α = ((∑ i, α i : ℕ) : ℝ) * hermiteCoeff f α := by
  rw [hermiteCoeff_coeFn, hermiteBasis_repr_ornsteinUhlenbeck hf]

/-- The noise operators preserve the domain of `L`: for `|ρ| ≤ 1`, `(U_ρ f)^(α) = ρ ^ |α| f̂(α)`
is bounded by `|f̂(α)|`. -/
theorem MemOrnsteinUhlenbeckDomain.gaussianNoiseOp {f : (ι → ℝ) → ℝ}
    (hf : MemOrnsteinUhlenbeckDomain f) {ρ : ℝ} (hρ : |ρ| ≤ 1) :
    MemOrnsteinUhlenbeckDomain (gaussianNoiseOp ρ f) := by
  refine ⟨hf.memLp.gaussianNoiseOp hρ one_le_two,
    hf.summable.of_nonneg_of_le (fun _ => by positivity) fun α => ?_⟩
  have h : (ρ ^ (∑ i, α i)) ^ 2 ≤ 1 := by
    rw [sq_le_one_iff_abs_le_one, abs_pow]
    exact pow_le_one₀ (abs_nonneg ρ) hρ
  rw [hermiteCoeff_gaussianNoiseOp hρ hf.memLp, mul_pow]
  exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (sq_nonneg _) h) (sq_nonneg _)

/-- **Noise smooths into the domain of `L`** [O'Donnell, Exercise 11.18(c)][ODonnell2014]: for
`f ∈ L²(γⁿ)` and `|ρ| < 1`, `U_ρ f` is in the domain of `L`. Its coefficients are
`ρ ^ |α| f̂(α)` and `m² ρ ^ (2 m) → 0`, so `|α|² (ρ ^ |α| f̂(α))² ≤ C f̂(α)²`, which is summable
by Parseval. -/
theorem memOrnsteinUhlenbeckDomain_gaussianNoiseOp {f : (ι → ℝ) → ℝ}
    (hf : MemLp f 2 (Measure.pi fun _ : ι => gaussianReal 0 1)) {ρ : ℝ} (hρ : |ρ| < 1) :
    MemOrnsteinUhlenbeckDomain (gaussianNoiseOp ρ f) := by
  have hρ2 : |ρ ^ 2| < 1 := by
    rw [abs_pow]
    exact pow_lt_one₀ (abs_nonneg ρ) hρ two_ne_zero
  obtain ⟨C, hC⟩ := (tendsto_pow_const_mul_const_pow_of_abs_lt_one 2 hρ2).bddAbove_range
  refine ⟨hf.gaussianNoiseOp hρ.le one_le_two, ((hasSum_hermiteCoeff_sq hf).summable.mul_left
    C).of_nonneg_of_le (fun _ => by positivity) fun α => ?_⟩
  rw [hermiteCoeff_gaussianNoiseOp hρ.le hf]
  calc ((∑ i, α i : ℕ) : ℝ) ^ 2 * (ρ ^ (∑ i, α i) * hermiteCoeff f α) ^ 2 =
        (((∑ i, α i : ℕ) : ℝ) ^ 2 * (ρ ^ 2) ^ (∑ i, α i)) * hermiteCoeff f α ^ 2 := by ring
    _ ≤ C * hermiteCoeff f α ^ 2 :=
        mul_le_mul_of_nonneg_right (hC ⟨∑ i, α i, rfl⟩) (sq_nonneg _)

/-- `ρ⁻¹ (m ρ ^ m c) = m ρ ^ (m - 1) c` for `ρ ≠ 0`. -/
private theorem inv_mul_mul_pow_mul {ρ : ℝ} (hρ : ρ ≠ 0) (m : ℕ) (c : ℝ) :
    ρ⁻¹ * (m * (ρ ^ m * c)) = m * ρ ^ (m - 1) * c := by
  cases m with
  | zero => simp
  | succ k =>
    rw [pow_succ, Nat.add_sub_cancel]
    field_simp

/-- An `L²` class `u ρ` of `U_ρ f` is `U_ρ f` as an element of `L²(γⁿ)`. -/
private theorem eq_toLp_gaussianNoiseOp {f : (ι → ℝ) → ℝ}
    (hf : MemLp f 2 (Measure.pi fun _ : ι => gaussianReal 0 1))
    {u : ℝ → Lp ℝ 2 (Measure.pi fun _ : ι => gaussianReal 0 1)}
    (hu : ∀ ρ, |ρ| ≤ 1 → u ρ =ᵐ[Measure.pi fun _ : ι => gaussianReal 0 1] gaussianNoiseOp ρ f)
    {ρ : ℝ} (hρ : |ρ| ≤ 1) :
    u ρ = (hf.gaussianNoiseOp hρ one_le_two).toLp (gaussianNoiseOp ρ f) := by
  rw [← Lp.toLp_coeFn (u ρ) (Lp.memLp _)]
  exact MemLp.toLp_congr _ _ (hu ρ hρ)

/-- The Hermite coordinates of the difference quotient `(σ - ρ)⁻¹ (U_σ f - U_ρ f)` are
`slope (· ^ |α|) ρ σ f̂(α)`, since `(U_σ f)^(α) = σ ^ |α| f̂(α)`. -/
private theorem hermiteBasis_repr_slope {f : (ι → ℝ) → ℝ}
    (hf : MemLp f 2 (Measure.pi fun _ : ι => gaussianReal 0 1))
    {u : ℝ → Lp ℝ 2 (Measure.pi fun _ : ι => gaussianReal 0 1)}
    (hu : ∀ ρ, |ρ| ≤ 1 → u ρ =ᵐ[Measure.pi fun _ : ι => gaussianReal 0 1] gaussianNoiseOp ρ f)
    {σ ρ : ℝ} (hσ : |σ| ≤ 1) (hρ : |ρ| ≤ 1) (α : ι → ℕ) :
    (hermiteBasis ι).repr (slope u ρ σ) α =
      slope (fun s : ℝ => s ^ (∑ i, α i)) ρ σ * hermiteCoeff f α := by
  rw [slope_def_module, eq_toLp_gaussianNoiseOp hf hu hσ, eq_toLp_gaussianNoiseOp hf hu hρ,
    map_smul, map_sub]
  simp only [lp.coeFn_sub, lp.coeFn_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    hermiteBasis_repr, hermiteCoeff_gaussianNoiseOp hσ hf, hermiteCoeff_gaussianNoiseOp hρ hf,
    slope_def_field]
  ring

/-- `|slope (· ^ m) ρ σ| ≤ m r ^ (m - 1)` for `|σ|, |ρ| ≤ r`, by `abs_pow_sub_pow_le`. -/
private theorem abs_slope_pow_le {σ ρ r : ℝ} (hσ : |σ| ≤ r) (hρ : |ρ| ≤ r) (m : ℕ) :
    |slope (fun s : ℝ => s ^ m) ρ σ| ≤ m * r ^ (m - 1) := by
  rcases eq_or_ne σ ρ with rfl | h
  · rw [slope_same, abs_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg ((abs_nonneg σ).trans hσ) _)
  rw [slope_def_field, abs_div, div_le_iff₀ (abs_pos.2 (sub_ne_zero.2 h))]
  calc |σ ^ m - ρ ^ m| ≤ |σ - ρ| * m * max |σ| |ρ| ^ (m - 1) := abs_pow_sub_pow_le σ ρ m
    _ ≤ |σ - ρ| * m * r ^ (m - 1) := by gcongr; exact max_le hσ hρ
    _ = m * r ^ (m - 1) * |σ - ρ| := by ring

/-- `‖v‖² = ∑ α, v_α²` for the Hermite coordinates `v_α` of `v ∈ L²(γⁿ)`. -/
private theorem norm_sq_eq_tsum_hermiteBasis_repr_sq
    (v : Lp ℝ 2 (Measure.pi fun _ : ι => gaussianReal 0 1)) :
    ‖v‖ ^ 2 = ∑' α, (hermiteBasis ι).repr v α ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal) ((hermiteBasis ι).repr v)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, LinearIsometryEquiv.norm_map, Real.norm_eq_abs,
    sq_abs] using h

/-- The coefficients `|α| ρ ^ (|α| - 1) f̂(α)` of `(d/dρ) U_ρ f` are square-summable when
`|ρ| ≤ r` and `∑ α, |α|² (r ^ |α| f̂(α))² < ∞`. -/
private theorem memℓp_mul_pow_mul_hermiteCoeff_of_summable {f : (ι → ℝ) → ℝ} {r ρ : ℝ}
    (hr : 0 < r) (hρ : |ρ| ≤ r) (hs : Summable fun α : ι → ℕ =>
      ((∑ i, α i : ℕ) : ℝ) ^ 2 * (r ^ (∑ i, α i) * hermiteCoeff f α) ^ 2) :
    Memℓp (fun α : ι → ℕ => ((∑ i, α i : ℕ) : ℝ) * ρ ^ (∑ i, α i - 1) * hermiteCoeff f α) 2 :=
  ((memℓp_two_sum_mul_iff.2 hs).const_mul r⁻¹).mono' fun α => by
    rw [inv_mul_mul_pow_mul hr.ne']
    simp only [norm_mul, norm_pow, Real.norm_eq_abs, Nat.abs_cast, abs_of_pos hr]
    gcongr

/-- **The derivative of the Gaussian noise operators in `L²`**, the general form: if
`0 < r ≤ 1`, `|ρ| ≤ r` and `∑ α, |α|² (r ^ |α| f̂(α))² < ∞`, then `σ ↦ U_σ f`, restricted to
`[-r, r]`, has derivative `∑ α, |α| ρ ^ (|α| - 1) f̂(α) h_α` at `ρ`. The `α`-th Hermite coordinate
of the difference quotient is `slope (· ^ |α|) ρ σ f̂(α)`; it tends to `|α| ρ ^ (|α| - 1) f̂(α)`,
and it is bounded by `|α| r ^ (|α| - 1) |f̂(α)|`. Dominated convergence of the squared coordinates
gives the `L²` limit. -/
private theorem hasDerivWithinAt_Icc_of_summable {f : (ι → ℝ) → ℝ}
    (hf : MemLp f 2 (Measure.pi fun _ : ι => gaussianReal 0 1)) {r : ℝ} (hr : 0 < r)
    (hr1 : r ≤ 1) (hs : Summable fun α : ι → ℕ =>
      ((∑ i, α i : ℕ) : ℝ) ^ 2 * (r ^ (∑ i, α i) * hermiteCoeff f α) ^ 2)
    {u : ℝ → Lp ℝ 2 (Measure.pi fun _ : ι => gaussianReal 0 1)}
    (hu : ∀ ρ, |ρ| ≤ 1 → u ρ =ᵐ[Measure.pi fun _ : ι => gaussianReal 0 1] gaussianNoiseOp ρ f)
    {ρ : ℝ} (hρ : |ρ| ≤ r) :
    HasDerivWithinAt u
      (∑' α, (((∑ i, α i : ℕ) : ℝ) * ρ ^ (∑ i, α i - 1) * hermiteCoeff f α) • hermiteBasis ι α)
      (Set.Icc (-r) r) ρ := by
  have hc := memℓp_mul_pow_mul_hermiteCoeff_of_summable hr hρ hs
  have hT : Tendsto (fun σ => ∑' α : ι → ℕ,
      (slope (fun s : ℝ => s ^ (∑ i, α i)) ρ σ * hermiteCoeff f α -
        ((∑ i, α i : ℕ) : ℝ) * ρ ^ (∑ i, α i - 1) * hermiteCoeff f α) ^ 2)
      (𝓝[Set.Icc (-r) r \ {ρ}] ρ) (𝓝 0) := by
    have h := tendsto_tsum_of_dominated_convergence (𝓕 := 𝓝[Set.Icc (-r) r \ {ρ}] ρ)
      (f := fun σ (α : ι → ℕ) => (slope (fun s : ℝ => s ^ (∑ i, α i)) ρ σ * hermiteCoeff f α -
        ((∑ i, α i : ℕ) : ℝ) * ρ ^ (∑ i, α i - 1) * hermiteCoeff f α) ^ 2) (g := fun _ => 0)
      (bound := fun α => (2 * r⁻¹) ^ 2 *
        (((∑ i, α i : ℕ) : ℝ) ^ 2 * (r ^ (∑ i, α i) * hermiteCoeff f α) ^ 2))
      (hs.mul_left ((2 * r⁻¹) ^ 2)) ?_ ?_
    · rwa [tsum_zero] at h
    · intro α
      have h0 := ((hasDerivAt_iff_tendsto_slope.1 (hasDerivAt_pow (∑ i, α i) ρ)).mono_left
        (nhdsWithin_mono ρ (Set.sdiff_subset_compl (Set.Icc (-r) r) {ρ}))).mul_const
          (hermiteCoeff f α)
      simpa only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] using
        (h0.sub_const (((∑ i, α i : ℕ) : ℝ) * ρ ^ (∑ i, α i - 1) * hermiteCoeff f α)).pow 2
    · filter_upwards [self_mem_nhdsWithin] with σ hσ α
      set m : ℕ := ∑ i, α i
      have h1 := abs_le.1 (abs_slope_pow_le (abs_le.2 hσ.1) hρ m)
      have h2 : |(m : ℝ) * ρ ^ (m - 1)| ≤ m * r ^ (m - 1) := by
        rw [abs_mul, Nat.abs_cast, abs_pow]
        gcongr
      have h3 := abs_le.1 h2
      have h4 : (slope (fun s : ℝ => s ^ m) ρ σ - m * ρ ^ (m - 1)) ^ 2 ≤
          (2 * (m * r ^ (m - 1))) ^ 2 := sq_le_sq' (by linarith) (by linarith)
      have h5 := inv_mul_mul_pow_mul hr.ne' m 1
      rw [mul_one, mul_one] at h5
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sub_mul, mul_pow]
      calc (slope (fun s : ℝ => s ^ m) ρ σ - m * ρ ^ (m - 1)) ^ 2 * hermiteCoeff f α ^ 2 ≤
            (2 * (r⁻¹ * (m * r ^ m))) ^ 2 * hermiteCoeff f α ^ 2 :=
          mul_le_mul_of_nonneg_right (h5 ▸ h4) (sq_nonneg _)
        _ = (2 * r⁻¹) ^ 2 * ((m : ℝ) ^ 2 * (r ^ m * hermiteCoeff f α) ^ 2) := by ring
  rw [hasDerivWithinAt_iff_tendsto_slope, tendsto_iff_norm_sub_tendsto_zero]
  have hS := hT.sqrt
  rw [Real.sqrt_zero] at hS
  refine hS.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  rw [← Real.sqrt_sq (norm_nonneg _), norm_sq_eq_tsum_hermiteBasis_repr_sq]
  congr 1
  refine tsum_congr fun α => ?_
  rw [map_sub, lp.coeFn_sub, Pi.sub_apply, hermiteBasis_repr_tsum_smul hc,
    hermiteBasis_repr_slope hf hu ((abs_le.2 hσ.1).trans hr1) (hρ.trans hr1)]

/-- **The derivative of the Gaussian noise operators on `[-1, 1]`**
[O'Donnell, Propositions 11.27 and 11.40][ODonnell2014]: for `f` in the domain of `L` and
`|ρ| ≤ 1`, the map `σ ↦ U_σ f` into `L²(γⁿ)`, restricted to `σ ∈ [-1, 1]`, has derivative
`∑ α, |α| ρ ^ (|α| - 1) f̂(α) h_α` at `ρ`. Here `u σ` is any `L²` class of `U_σ f` for
`|σ| ≤ 1`. -/
theorem hasDerivWithinAt_Icc_gaussianNoiseOp {f : (ι → ℝ) → ℝ}
    (hf : MemOrnsteinUhlenbeckDomain f)
    {u : ℝ → Lp ℝ 2 (Measure.pi fun _ : ι => gaussianReal 0 1)}
    (hu : ∀ ρ, |ρ| ≤ 1 → u ρ =ᵐ[Measure.pi fun _ : ι => gaussianReal 0 1] gaussianNoiseOp ρ f)
    {ρ : ℝ} (hρ : |ρ| ≤ 1) :
    HasDerivWithinAt u
      (∑' α, (((∑ i, α i : ℕ) : ℝ) * ρ ^ (∑ i, α i - 1) * hermiteCoeff f α) • hermiteBasis ι α)
      (Set.Icc (-1) 1) ρ :=
  hasDerivWithinAt_Icc_of_summable hf.memLp one_pos le_rfl
    (by simpa only [one_pow, one_mul] using hf.summable) hu hρ

/-- **The Ornstein–Uhlenbeck operator is the derivative of the noise operators at `ρ = 1`**
[O'Donnell, Definition 11.24 and Proposition 11.40][ODonnell2014]: for `f` in the domain of `L`,
the map `ρ ↦ U_ρ f` into `L²(γⁿ)` has left derivative `L f` at `ρ = 1`. Here `u ρ` is any `L²`
class of `U_ρ f` for `|ρ| ≤ 1`; its values for `|ρ| > 1` are irrelevant. The derivative is in the
sense of `L²` limits of difference quotients, as in the book. In the exponential
parametrization `ρ = e^{-t}` this reads `L f = -(d/dt) U_{e^{-t}} f |_{t = 0⁺}`
(`hasDerivWithinAt_gaussianNoiseOp_exp_neg_zero`). -/
theorem hasDerivWithinAt_gaussianNoiseOp {f : (ι → ℝ) → ℝ} (hf : MemOrnsteinUhlenbeckDomain f)
    {u : ℝ → Lp ℝ 2 (Measure.pi fun _ : ι => gaussianReal 0 1)}
    (hu : ∀ ρ, |ρ| ≤ 1 → u ρ =ᵐ[Measure.pi fun _ : ι => gaussianReal 0 1] gaussianNoiseOp ρ f) :
    HasDerivWithinAt u (ornsteinUhlenbeck f) (Set.Iic 1) 1 := by
  have h := (hasDerivWithinAt_Icc_gaussianNoiseOp hf hu (ρ := 1) (by simp))
    |>.mono_of_mem_nhdsWithin (Icc_mem_nhdsLE (by norm_num : (-1 : ℝ) < 1))
  simpa only [one_pow, mul_one, ← ornsteinUhlenbeck_def] using h

/-- **`L` in exponential time** [O'Donnell, Definition 11.24][ODonnell2014]: for `f` in the
domain of `L`, the map `t ↦ U_{e^{-t}} f` into `L²(γⁿ)` has right derivative `-L f` at `t = 0`.
Here `u ρ` is any `L²` class of `U_ρ f` for `|ρ| ≤ 1`. -/
theorem hasDerivWithinAt_gaussianNoiseOp_exp_neg_zero {f : (ι → ℝ) → ℝ}
    (hf : MemOrnsteinUhlenbeckDomain f)
    {u : ℝ → Lp ℝ 2 (Measure.pi fun _ : ι => gaussianReal 0 1)}
    (hu : ∀ ρ, |ρ| ≤ 1 → u ρ =ᵐ[Measure.pi fun _ : ι => gaussianReal 0 1] gaussianNoiseOp ρ f) :
    HasDerivWithinAt (fun t => u (Real.exp (-t))) (-ornsteinUhlenbeck f) (Set.Ici 0) 0 := by
  have hh : HasDerivWithinAt (fun t : ℝ => Real.exp (-t)) (-1) (Set.Ici 0) 0 := by
    simpa [Function.comp_def] using
      ((Real.hasDerivAt_exp (-0)).comp 0 (hasDerivAt_neg 0)).hasDerivWithinAt (s := Set.Ici 0)
  have h := (hasDerivWithinAt_gaussianNoiseOp hf hu).scomp_of_eq 0 hh
    (fun t ht => Real.exp_le_one_iff.2 (neg_nonpos.2 ht)) (by simp)
  simpa only [Function.comp_def, neg_one_smul] using h

/-- The Hermite coordinates of a left derivative `g` of `ρ ↦ U_ρ f` at `ρ = 1` are `|α| f̂(α)`:
the `α`-th coordinate of the difference quotient is `slope (· ^ |α|) 1 ρ f̂(α)`, which tends both
to that of `g` and to `|α| f̂(α)` as `ρ → 1⁻`. -/
private theorem hermiteBasis_repr_of_hasDerivWithinAt {f : (ι → ℝ) → ℝ}
    (hf : MemLp f 2 (Measure.pi fun _ : ι => gaussianReal 0 1))
    {u : ℝ → Lp ℝ 2 (Measure.pi fun _ : ι => gaussianReal 0 1)}
    (hu : ∀ ρ, |ρ| ≤ 1 → u ρ =ᵐ[Measure.pi fun _ : ι => gaussianReal 0 1] gaussianNoiseOp ρ f)
    {g : Lp ℝ 2 (Measure.pi fun _ : ι => gaussianReal 0 1)}
    (hg : HasDerivWithinAt u g (Set.Iic 1) 1) (α : ι → ℕ) :
    (hermiteBasis ι).repr g α = ((∑ i, α i : ℕ) : ℝ) * hermiteCoeff f α := by
  rw [hasDerivWithinAt_iff_tendsto_slope, Set.Iic_sdiff_right] at hg
  have hc : Continuous fun v : Lp ℝ 2 (Measure.pi fun _ : ι => gaussianReal 0 1) =>
      (hermiteBasis ι).repr v α := by
    simp only [HilbertBasis.repr_apply_apply]
    exact continuous_const.inner continuous_id
  refine tendsto_nhds_unique ((hc.tendsto g).comp hg) ?_
  have h1 := ((hasDerivAt_iff_tendsto_slope.1 (hasDerivAt_pow (∑ i, α i) (1 : ℝ))).mono_left
    (nhdsWithin_mono 1 fun x (hx : x ∈ Set.Iio (1 : ℝ)) =>
      Set.mem_compl_singleton_iff.2 (ne_of_lt hx))).mul_const
      (hermiteCoeff f α)
  rw [one_pow, mul_one] at h1
  refine h1.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (show (-1 : ℝ) < 1 by norm_num)] with ρ hρ
  rw [Function.comp_apply, hermiteBasis_repr_slope hf hu (abs_le.2 ⟨hρ.1.le, hρ.2.le⟩) (by simp)]

/-- **The domain of the Ornstein–Uhlenbeck operator** [O'Donnell, Exercise 11.18][ODonnell2014],
converse direction: if the map `ρ ↦ U_ρ f` into `L²(γⁿ)` has a left derivative at `ρ = 1`, then
`f` is in the domain of `L`. The derivative's Hermite coordinates are `|α| f̂(α)`, and they are
square-summable. -/
theorem memOrnsteinUhlenbeckDomain_of_hasDerivWithinAt {f : (ι → ℝ) → ℝ}
    (hf : MemLp f 2 (Measure.pi fun _ : ι => gaussianReal 0 1))
    {u : ℝ → Lp ℝ 2 (Measure.pi fun _ : ι => gaussianReal 0 1)}
    (hu : ∀ ρ, |ρ| ≤ 1 → u ρ =ᵐ[Measure.pi fun _ : ι => gaussianReal 0 1] gaussianNoiseOp ρ f)
    {g : Lp ℝ 2 (Measure.pi fun _ : ι => gaussianReal 0 1)}
    (hg : HasDerivWithinAt u g (Set.Iic 1) 1) :
    MemOrnsteinUhlenbeckDomain f := by
  have h := lp.memℓp ((hermiteBasis ι).repr g)
  rw [funext (hermiteBasis_repr_of_hasDerivWithinAt hf hu hg)] at h
  exact ⟨hf, memℓp_two_sum_mul_iff.1 h⟩

/-- **The Ornstein–Uhlenbeck operator is the derivative of the noise operators at `ρ = 1`**
[O'Donnell, Definition 11.24 and Proposition 11.40][ODonnell2014], in the book's form: for
`f ∈ L²(γⁿ)`, every left derivative of `ρ ↦ U_ρ f` in `L²(γⁿ)` at `ρ = 1` is `L f`. -/
theorem eq_ornsteinUhlenbeck_of_hasDerivWithinAt {f : (ι → ℝ) → ℝ}
    (hf : MemLp f 2 (Measure.pi fun _ : ι => gaussianReal 0 1))
    {u : ℝ → Lp ℝ 2 (Measure.pi fun _ : ι => gaussianReal 0 1)}
    (hu : ∀ ρ, |ρ| ≤ 1 → u ρ =ᵐ[Measure.pi fun _ : ι => gaussianReal 0 1] gaussianNoiseOp ρ f)
    {g : Lp ℝ 2 (Measure.pi fun _ : ι => gaussianReal 0 1)}
    (hg : HasDerivWithinAt u g (Set.Iic 1) 1) :
    g = ornsteinUhlenbeck f :=
  (uniqueDiffWithinAt_Iic 1).eq_deriv _ hg
    (hasDerivWithinAt_gaussianNoiseOp (memOrnsteinUhlenbeckDomain_of_hasDerivWithinAt hf hu hg) hu)

/-- **The domain of the Ornstein–Uhlenbeck operator** [O'Donnell, Exercise 11.18][ODonnell2014]:
for `f ∈ L²(γⁿ)`, the map `ρ ↦ U_ρ f` into `L²(γⁿ)` has a left derivative at `ρ = 1` if and only
if `∑ α, |α|² f̂(α)² < ∞`. The derivative is then `L f` (`hasDerivWithinAt_gaussianNoiseOp`). -/
theorem exists_hasDerivWithinAt_gaussianNoiseOp_iff {f : (ι → ℝ) → ℝ}
    (hf : MemLp f 2 (Measure.pi fun _ : ι => gaussianReal 0 1))
    {u : ℝ → Lp ℝ 2 (Measure.pi fun _ : ι => gaussianReal 0 1)}
    (hu : ∀ ρ, |ρ| ≤ 1 → u ρ =ᵐ[Measure.pi fun _ : ι => gaussianReal 0 1] gaussianNoiseOp ρ f) :
    (∃ g, HasDerivWithinAt u g (Set.Iic 1) 1) ↔ MemOrnsteinUhlenbeckDomain f :=
  ⟨fun ⟨_, hg⟩ => memOrnsteinUhlenbeckDomain_of_hasDerivWithinAt hf hu hg,
    fun h => ⟨_, hasDerivWithinAt_gaussianNoiseOp h hu⟩⟩

/-! ### The derivative of `U_ρ f` inside `(-1, 1)` -/

/-- **`L` commutes with `U_ρ`** [O'Donnell, Proposition 11.27][ODonnell2014]: for `f` in the
domain of `L` and `|ρ| ≤ 1`, `L (U_ρ f) = U_ρ (L f)` in `L²(γⁿ)`; both have Hermite coordinates
`|α| ρ ^ |α| f̂(α)`. -/
theorem ornsteinUhlenbeck_gaussianNoiseOp {f : (ι → ℝ) → ℝ} (hf : MemOrnsteinUhlenbeckDomain f)
    {ρ : ℝ} (hρ : |ρ| ≤ 1) :
    ornsteinUhlenbeck (gaussianNoiseOp ρ f) =
      ((Lp.memLp (ornsteinUhlenbeck f)).gaussianNoiseOp hρ one_le_two).toLp
        (gaussianNoiseOp ρ ⇑(ornsteinUhlenbeck f)) := by
  refine (hermiteBasis ι).repr.injective (lp.ext (funext fun α => ?_))
  rw [hermiteBasis_repr_ornsteinUhlenbeck (hf.gaussianNoiseOp hρ), hermiteBasis_repr,
    hermiteCoeff_gaussianNoiseOp hρ (Lp.memLp _), hermiteCoeff_ornsteinUhlenbeck hf,
    hermiteCoeff_gaussianNoiseOp hρ hf.memLp]
  ring

/-- For `f ∈ L²(γⁿ)` and `|ρ| < 1` there is `r` with `|ρ| < r < 1` and
`∑ α, |α|² (r ^ |α| f̂(α))² < ∞`, by Exercise 11.18(c). -/
private theorem exists_summable_of_abs_lt_one {f : (ι → ℝ) → ℝ}
    (hf : MemLp f 2 (Measure.pi fun _ : ι => gaussianReal 0 1)) {ρ : ℝ} (hρ : |ρ| < 1) :
    ∃ r, 0 < r ∧ r < 1 ∧ |ρ| < r ∧ Summable fun α : ι → ℕ =>
      ((∑ i, α i : ℕ) : ℝ) ^ 2 * (r ^ (∑ i, α i) * hermiteCoeff f α) ^ 2 := by
  have hr : 0 < (|ρ| + 1) / 2 := by positivity
  have hr1 : (|ρ| + 1) / 2 < 1 := by linarith
  refine ⟨_, hr, hr1, by linarith, ?_⟩
  have h := (memOrnsteinUhlenbeckDomain_gaussianNoiseOp hf
    (show |(|ρ| + 1) / 2| < 1 by rwa [abs_of_pos hr])).summable
  simpa only [hermiteCoeff_gaussianNoiseOp (abs_of_pos hr ▸ hr1.le) hf] using h

/-- For `f ∈ L²(γⁿ)` and `|ρ| < 1`, the coefficients `|α| ρ ^ (|α| - 1) f̂(α)` of `(d/dρ) U_ρ f`
are square-summable, so `hermiteBasis_repr_tsum_smul` reads off the coordinates of the derivative
in `hasDerivAt_gaussianNoiseOp`. -/
theorem memℓp_mul_pow_mul_hermiteCoeff {f : (ι → ℝ) → ℝ}
    (hf : MemLp f 2 (Measure.pi fun _ : ι => gaussianReal 0 1)) {ρ : ℝ} (hρ : |ρ| < 1) :
    Memℓp (fun α : ι → ℕ => ((∑ i, α i : ℕ) : ℝ) * ρ ^ (∑ i, α i - 1) * hermiteCoeff f α) 2 := by
  obtain ⟨r, hr, -, hρr, hs⟩ := exists_summable_of_abs_lt_one hf hρ
  exact memℓp_mul_pow_mul_hermiteCoeff_of_summable hr hρr.le hs

/-- **The derivative of the Gaussian noise operators** [O'Donnell, Proposition 11.27][ODonnell2014],
in Hermite form: for `f ∈ L²(γⁿ)` and `|ρ| < 1`, the map `ρ ↦ U_ρ f` into `L²(γⁿ)` is
differentiable at `ρ`, with derivative `∑ α, |α| ρ ^ (|α| - 1) f̂(α) h_α`; `f` need not be in the
domain of `L`. Here `u σ` is any `L²` class of `U_σ f` for `|σ| ≤ 1`. For `ρ ≠ 0` this is
`ρ⁻¹ L U_ρ f` (`hasDerivAt_gaussianNoiseOp_eq_inv_smul_ornsteinUhlenbeck`), and `ρ⁻¹ U_ρ L f`
when `f` is in the domain of `L` (`hasDerivAt_gaussianNoiseOp_eq_inv_smul_gaussianNoiseOp`). The
book derives Proposition 11.27 from the semigroup property; here it is read off the Hermite
expansion `U_ρ f = ∑ α, ρ ^ |α| f̂(α) h_α`, whose coefficients `|α| ρ ^ (|α| - 1) f̂(α)` are
dominated by `|α| r ^ (|α| - 1) |f̂(α)|` for some `|ρ| < r < 1`. -/
theorem hasDerivAt_gaussianNoiseOp {f : (ι → ℝ) → ℝ}
    (hf : MemLp f 2 (Measure.pi fun _ : ι => gaussianReal 0 1))
    {u : ℝ → Lp ℝ 2 (Measure.pi fun _ : ι => gaussianReal 0 1)}
    (hu : ∀ ρ, |ρ| ≤ 1 → u ρ =ᵐ[Measure.pi fun _ : ι => gaussianReal 0 1] gaussianNoiseOp ρ f)
    {ρ : ℝ} (hρ : |ρ| < 1) :
    HasDerivAt u
      (∑' α, (((∑ i, α i : ℕ) : ℝ) * ρ ^ (∑ i, α i - 1) * hermiteCoeff f α) • hermiteBasis ι α)
      ρ := by
  obtain ⟨r, hr, hr1, hρr, hs⟩ := exists_summable_of_abs_lt_one hf hρ
  exact (hasDerivWithinAt_Icc_of_summable hf hr hr1.le hs hu hρr.le).hasDerivAt
    (Icc_mem_nhds (by linarith [neg_abs_le ρ]) (by linarith [le_abs_self ρ]))

/-- **The derivative of the Gaussian noise operators** [O'Donnell, Proposition 11.27][ODonnell2014],
`(d/dρ) U_ρ f = ρ⁻¹ L U_ρ f`: for `f ∈ L²(γⁿ)` and `0 < |ρ| < 1`, the map `ρ ↦ U_ρ f` into
`L²(γⁿ)` has derivative `ρ⁻¹ L (U_ρ f)` at `ρ`; `U_ρ f` is in the domain of `L` by
`memOrnsteinUhlenbeckDomain_gaussianNoiseOp`. Here `u σ` is any `L²` class of `U_σ f` for
`|σ| ≤ 1`. -/
theorem hasDerivAt_gaussianNoiseOp_eq_inv_smul_ornsteinUhlenbeck {f : (ι → ℝ) → ℝ}
    (hf : MemLp f 2 (Measure.pi fun _ : ι => gaussianReal 0 1))
    {u : ℝ → Lp ℝ 2 (Measure.pi fun _ : ι => gaussianReal 0 1)}
    (hu : ∀ ρ, |ρ| ≤ 1 → u ρ =ᵐ[Measure.pi fun _ : ι => gaussianReal 0 1] gaussianNoiseOp ρ f)
    {ρ : ℝ} (hρ : |ρ| < 1) (hρ0 : ρ ≠ 0) :
    HasDerivAt u (ρ⁻¹ • ornsteinUhlenbeck (gaussianNoiseOp ρ f)) ρ := by
  convert hasDerivAt_gaussianNoiseOp hf hu hρ using 1
  refine (hermiteBasis ι).repr.injective (lp.ext (funext fun α => ?_))
  rw [map_smul, lp.coeFn_smul, Pi.smul_apply,
    hermiteBasis_repr_ornsteinUhlenbeck (memOrnsteinUhlenbeckDomain_gaussianNoiseOp hf hρ),
    hermiteBasis_repr_tsum_smul (memℓp_mul_pow_mul_hermiteCoeff hf hρ),
    hermiteCoeff_gaussianNoiseOp hρ.le hf, smul_eq_mul, inv_mul_mul_pow_mul hρ0]

/-- **The derivative of the Gaussian noise operators** [O'Donnell, Proposition 11.27][ODonnell2014],
`(d/dρ) U_ρ f = ρ⁻¹ U_ρ L f`: for `f` in the domain of `L` and `0 < |ρ| < 1`, the map
`ρ ↦ U_ρ f` into `L²(γⁿ)` has derivative `ρ⁻¹ U_ρ (L f)` at `ρ`. Here `u σ` is any `L²` class of
`U_σ f` for `|σ| ≤ 1`. -/
theorem hasDerivAt_gaussianNoiseOp_eq_inv_smul_gaussianNoiseOp {f : (ι → ℝ) → ℝ}
    (hf : MemOrnsteinUhlenbeckDomain f)
    {u : ℝ → Lp ℝ 2 (Measure.pi fun _ : ι => gaussianReal 0 1)}
    (hu : ∀ ρ, |ρ| ≤ 1 → u ρ =ᵐ[Measure.pi fun _ : ι => gaussianReal 0 1] gaussianNoiseOp ρ f)
    {ρ : ℝ} (hρ : |ρ| < 1) (hρ0 : ρ ≠ 0) :
    HasDerivAt u (ρ⁻¹ • ((Lp.memLp (ornsteinUhlenbeck f)).gaussianNoiseOp hρ.le one_le_two).toLp
      (gaussianNoiseOp ρ ⇑(ornsteinUhlenbeck f))) ρ := by
  rw [← ornsteinUhlenbeck_gaussianNoiseOp hf hρ.le]
  exact hasDerivAt_gaussianNoiseOp_eq_inv_smul_ornsteinUhlenbeck hf.memLp hu hρ hρ0

/-- **The derivative of the Gaussian noise operators in exponential time**
[O'Donnell, Proposition 11.27][ODonnell2014], `(d/dt) U_{e^{-t}} f = -L U_{e^{-t}} f`: for
`f ∈ L²(γⁿ)` and `t > 0`, the map `t ↦ U_{e^{-t}} f` into `L²(γⁿ)` has derivative
`-L (U_{e^{-t}} f)` at `t`. This is `hasDerivAt_gaussianNoiseOp_eq_inv_smul_ornsteinUhlenbeck`
composed with `t ↦ e^{-t}`; at `t = 0` it is `hasDerivWithinAt_gaussianNoiseOp_exp_neg_zero`. -/
theorem hasDerivAt_gaussianNoiseOp_exp_neg {f : (ι → ℝ) → ℝ}
    (hf : MemLp f 2 (Measure.pi fun _ : ι => gaussianReal 0 1))
    {u : ℝ → Lp ℝ 2 (Measure.pi fun _ : ι => gaussianReal 0 1)}
    (hu : ∀ ρ, |ρ| ≤ 1 → u ρ =ᵐ[Measure.pi fun _ : ι => gaussianReal 0 1] gaussianNoiseOp ρ f)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => u (Real.exp (-s)))
      (-ornsteinUhlenbeck (gaussianNoiseOp (Real.exp (-t)) f)) t := by
  have hρ : |Real.exp (-t)| < 1 := by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.2 (neg_lt_zero.2 ht)
  have h := (hasDerivAt_gaussianNoiseOp_eq_inv_smul_ornsteinUhlenbeck hf hu hρ
    (Real.exp_pos _).ne').scomp t ((Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t))
  refine h.congr_deriv ?_
  rw [smul_smul, mul_neg_one, neg_mul, mul_inv_cancel₀ (Real.exp_pos _).ne', neg_one_smul]

end ProbabilityTheory
