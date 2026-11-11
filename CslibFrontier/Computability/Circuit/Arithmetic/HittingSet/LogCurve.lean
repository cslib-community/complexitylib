/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.RingTheory.PowerSeries.Constants
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.PowerSeries.Log
public import Mathlib.Algebra.Algebra.Rat

/-!
# The logarithmic curve and its derivation

The hitting-set generator of [Bhardwaj et al.][BhardwajEtAl2026] substitutes
the power series `Pᵢ = ln (1 + (i + 1) t)` for the variable `xᵢ`. Its derivative is the rational
function `(i + 1) / (1 + (i + 1) t)`. Clearing the common denominator
`Q = ∏ᵢ (1 + (i + 1) t)` gives polynomials `bᵢ = (i + 1) Q / (1 + (i + 1) t)` with
`Q * Pᵢ' = bᵢ`.

On polynomials in `x` with coefficients in `F[t]`, that is on `MvPolynomial (Fin n) F[X]`, the
derivation `D = Q ∂ₜ + ∑ᵢ bᵢ ∂ᵢ` is the lift of `Q * d/dt` along the substitution: by the chain
rule, `(D g)(P) = Q * (g(P))'`. Here `∂ₜ` differentiates the coefficients. This is the source's
derivation `∂ₜ + ∑ᵢ (i / (1 + i t)) ∂ᵢ` multiplied by `Q`, so that no rational functions are
needed.

## Main definitions

* `logDenom`, `logCoeff`: the polynomials `Q` and `bᵢ`.
* `logSeries`: the power series `ln (1 + (i + 1) t)`.
* `coeffDeriv`: the derivation `∂ₜ` of `MvPolynomial σ F[X]`, acting on coefficients.
* `logDeriv`: the derivation `D`.

## Main results

* `logDenom_mul_derivative_logSeries`: `Q * Pᵢ' = bᵢ`.
* `coeff_logDeriv`: the coefficients of `D g`.
* `aeval_logDeriv`: the chain rule `(D g)(P) = Q * (g(P))'`.

## References

* [S. Bhardwaj, F. Lakhani, P. Mukhopadhyay, R. Saptharishi, P. Shastri,
  A. K. Sinhababu, *Hitting sets from derivations: Waring rank and noncommutative
  ABPs*][BhardwajEtAl2026], §2
-/

@[expose] public section

open scoped Polynomial PowerSeries

namespace Cslib.Circuits.Arithmetic

open Finset

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

/-- The common denominator `Q = ∏ᵢ (1 + (i + 1) t)` of the derivatives of the logarithms. -/
noncomputable def logDenom : F[X] :=
  ∏ i : Fin n, (1 + Polynomial.C ((i : ℕ) + 1 : F) * Polynomial.X)

/-- The numerator `bᵢ = (i + 1) ∏_{j ≠ i} (1 + (j + 1) t)` of the derivative of the `i`-th
logarithm over the common denominator. -/
noncomputable def logCoeff (i : Fin n) : F[X] :=
  Polynomial.C ((i : ℕ) + 1 : F) *
    ∏ j ∈ univ.erase i, (1 + Polynomial.C ((j : ℕ) + 1 : F) * Polynomial.X)

/-- The power series `ln (1 + (i + 1) t)`. -/
noncomputable def logSeries (i : Fin n) : F⟦X⟧ :=
  PowerSeries.rescale ((i : ℕ) + 1 : F) (PowerSeries.log F)

variable {F n}

omit [CharZero F] in
theorem logCoeff_mul (i : Fin n) :
    logCoeff F n i * (1 + Polynomial.C ((i : ℕ) + 1 : F) * Polynomial.X) =
      Polynomial.C ((i : ℕ) + 1 : F) * logDenom F n := by
  rw [logCoeff, logDenom, ← mul_prod_erase univ _ (mem_univ i)]
  ring

/-- `Q * Pᵢ' = bᵢ`. -/
theorem logDenom_mul_derivative_logSeries (i : Fin n) :
    (logDenom F n : F⟦X⟧) * d⁄dX (logSeries F n i) = (logCoeff F n i : F⟦X⟧) := by
  have h₁ : d⁄dX (logSeries F n i) *
      (1 + PowerSeries.C ((i : ℕ) + 1 : F) * PowerSeries.X) = PowerSeries.C ((i : ℕ) + 1 : F) := by
    have h := congrArg (PowerSeries.rescale ((i : ℕ) + 1 : F))
      (PowerSeries.derivative_log_mul_one_add_X (A := F))
    rw [map_mul, map_add, map_one, PowerSeries.rescale_X] at h
    rw [logSeries, PowerSeries.derivative_rescale, Algebra.smul_def, mul_assoc, h, mul_one]
    rfl
  have h₂ := congrArg (fun p : F[X] => (p : F⟦X⟧)) (logCoeff_mul (F := F) i)
  simp only [Polynomial.coe_mul, Polynomial.coe_add, Polynomial.coe_one, Polynomial.coe_C,
    Polynomial.coe_X] at h₂
  have hunit : (1 + PowerSeries.C ((i : ℕ) + 1 : F) * PowerSeries.X : F⟦X⟧) ≠ 0 := by
    intro h
    simpa using congrArg PowerSeries.constantCoeff h
  refine mul_right_cancel₀ hunit ?_
  rw [mul_assoc, h₁, h₂, mul_comm]

section CoeffDeriv

variable {σ : Type*}

/-- The derivative of the coefficients of a polynomial with coefficients in `F[X]`. -/
noncomputable def coeffDerivFun (g : MvPolynomial σ F[X]) : MvPolynomial σ F[X] :=
  ∑ m ∈ g.support, MvPolynomial.monomial m (Polynomial.derivative (g.coeff m))

omit [CharZero F] in
theorem coeff_coeffDerivFun (g : MvPolynomial σ F[X]) (m : σ →₀ ℕ) :
    (coeffDerivFun g).coeff m = Polynomial.derivative (g.coeff m) := by
  classical
  rw [coeffDerivFun, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [sum_ite_eq' g.support m]
  split_ifs with h
  · rfl
  · rw [MvPolynomial.notMem_support_iff.1 h, map_zero]

/-- The derivation `∂ₜ` of `MvPolynomial σ F[X]` that differentiates every coefficient. -/
noncomputable def coeffDeriv : Derivation F (MvPolynomial σ F[X]) (MvPolynomial σ F[X]) :=
  Derivation.mk'
    { toFun := coeffDerivFun
      map_add' := fun p q => MvPolynomial.ext _ _ fun m => by simp [coeff_coeffDerivFun]
      map_smul' := fun c p => MvPolynomial.ext _ _ fun m => by simp [coeff_coeffDerivFun] }
    fun p q => MvPolynomial.ext _ _ fun m => by
      classical
      change (coeffDerivFun (p * q)).coeff m = (p * coeffDerivFun q + q * coeffDerivFun p).coeff m
      have hadd : (p * coeffDerivFun q + q * coeffDerivFun p).coeff m =
          (p * coeffDerivFun q).coeff m + (coeffDerivFun p * q).coeff m := by
        rw [mul_comm q]; simp
      rw [hadd]
      simp only [coeff_coeffDerivFun, MvPolynomial.coeff_mul, map_sum, Polynomial.derivative_mul,
        sum_add_distrib]
      exact add_comm _ _

omit [CharZero F] in
@[simp]
theorem coeff_coeffDeriv (g : MvPolynomial σ F[X]) (m : σ →₀ ℕ) :
    (coeffDeriv g).coeff m = Polynomial.derivative (g.coeff m) :=
  coeff_coeffDerivFun g m

omit [CharZero F] in
theorem coeffDeriv_C (a : F[X]) :
    coeffDeriv (MvPolynomial.C a : MvPolynomial σ F[X]) =
      MvPolynomial.C (Polynomial.derivative a) := by
  classical
  ext m
  rw [coeff_coeffDeriv, MvPolynomial.coeff_C, MvPolynomial.coeff_C]
  split_ifs <;> simp

omit [CharZero F] in
theorem coeffDeriv_X (i : σ) : coeffDeriv (MvPolynomial.X i : MvPolynomial σ F[X]) = 0 := by
  classical
  ext m
  rw [coeff_coeffDeriv, MvPolynomial.coeff_X]
  split_ifs <;> simp

end CoeffDeriv

variable (F n) in
/-- The derivation `D = Q ∂ₜ + ∑ᵢ bᵢ ∂ᵢ` of `MvPolynomial (Fin n) F[X]`. -/
noncomputable def logDeriv :
    Derivation F (MvPolynomial (Fin n) F[X]) (MvPolynomial (Fin n) F[X]) :=
  (MvPolynomial.C (logDenom F n) : MvPolynomial (Fin n) F[X]) • coeffDeriv +
    ∑ i, (MvPolynomial.C (logCoeff F n i) : MvPolynomial (Fin n) F[X]) •
      (MvPolynomial.pderiv (R := F[X]) (σ := Fin n) i).restrictScalars F

omit [CharZero F] in
theorem logDeriv_apply (g : MvPolynomial (Fin n) F[X]) :
    logDeriv F n g = MvPolynomial.C (logDenom F n) * coeffDeriv g +
      ∑ i, MvPolynomial.C (logCoeff F n i) * MvPolynomial.pderiv i g := by
  have hsum (s : Finset (Fin n)) :
      (∑ i ∈ s, (MvPolynomial.C (logCoeff F n i) : MvPolynomial (Fin n) F[X]) •
        (MvPolynomial.pderiv (R := F[X]) (σ := Fin n) i).restrictScalars F) g =
      ∑ i ∈ s, MvPolynomial.C (logCoeff F n i) * MvPolynomial.pderiv i g := by
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [sum_insert ha, sum_insert ha, add_apply, ih, smul_apply, smul_eq_mul]
      rfl
  rw [logDeriv, add_apply, hsum, smul_apply, smul_eq_mul]

omit [CharZero F] in
theorem logDeriv_C (a : F[X]) :
    logDeriv F n (MvPolynomial.C a) = MvPolynomial.C (logDenom F n * Polynomial.derivative a) := by
  simp [logDeriv_apply, coeffDeriv_C]

omit [CharZero F] in
theorem logDeriv_X (i : Fin n) :
    logDeriv F n (MvPolynomial.X i) = MvPolynomial.C (logCoeff F n i) := by
  classical
  simp [logDeriv_apply, coeffDeriv_X, MvPolynomial.pderiv_X, Pi.single_apply]

omit [CharZero F] in
/-- The coefficients of `D g`. -/
theorem coeff_logDeriv (g : MvPolynomial (Fin n) F[X]) (m : Fin n →₀ ℕ) :
    (logDeriv F n g).coeff m = logDenom F n * Polynomial.derivative (g.coeff m) +
      ∑ i, logCoeff F n i * (g.coeff (m + Finsupp.single i 1) * (m i + 1)) := by
  simp [logDeriv_apply, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_pderiv]

omit [CharZero F] in
/-- `D` commutes with the partial derivatives in `x`. -/
theorem logDeriv_pderiv (i : Fin n) (g : MvPolynomial (Fin n) F[X]) :
    logDeriv F n (MvPolynomial.pderiv i g) = MvPolynomial.pderiv i (logDeriv F n g) := by
  refine MvPolynomial.ext _ _ fun m => ?_
  rw [coeff_logDeriv, MvPolynomial.coeff_pderiv (logDeriv F n g) m, coeff_logDeriv,
    MvPolynomial.coeff_pderiv g m, add_mul, sum_mul]
  have hnat : Polynomial.derivative (g.coeff (m + Finsupp.single i 1) * ((m i : F[X]) + 1)) =
      Polynomial.derivative (g.coeff (m + Finsupp.single i 1)) * ((m i : F[X]) + 1) := by
    have h0 : Polynomial.derivative ((m i : F[X]) + 1) = 0 := by
      rw [Polynomial.derivative_add, Polynomial.derivative_natCast, Polynomial.derivative_one,
        add_zero]
    rw [Polynomial.derivative_mul, h0, mul_zero, add_zero]
  rw [hnat]
  congr 1
  · ring
  · refine sum_congr rfl fun j _ => ?_
    rw [MvPolynomial.coeff_pderiv, add_right_comm m (Finsupp.single j 1) (Finsupp.single i 1)]
    by_cases hij : j = i
    · subst hij
      simp only [Finsupp.add_apply, Finsupp.single_eq_same]
      push_cast
      ring
    · simp only [Finsupp.add_apply, Finsupp.single_eq_of_ne hij,
        Finsupp.single_eq_of_ne (Ne.symm hij), add_zero]
      ring

/-- The chain rule: `D` lifts `Q * d/dt` along the substitution of the logarithms. -/
theorem aeval_logDeriv (g : MvPolynomial (Fin n) F[X]) :
    MvPolynomial.aeval (logSeries F n) (logDeriv F n g) =
      (logDenom F n : F⟦X⟧) * d⁄dX (MvPolynomial.aeval (logSeries F n) g) := by
  have halg (a : F[X]) : algebraMap F[X] F⟦X⟧ a = (a : F⟦X⟧) := by
    simp [PowerSeries.algebraMap_apply']
  induction g using MvPolynomial.induction_on with
  | C a =>
    rw [logDeriv_C, MvPolynomial.aeval_C, MvPolynomial.aeval_C, halg, halg, Polynomial.coe_mul,
      PowerSeries.derivative_coe]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add, mul_add]
  | mul_X p i hp =>
    rw [Derivation.leibniz, map_add, smul_eq_mul, smul_eq_mul, map_mul, map_mul, hp, logDeriv_X,
      MvPolynomial.aeval_C, MvPolynomial.aeval_X, halg, map_mul, Derivation.leibniz,
      ← logDenom_mul_derivative_logSeries]
    simp only [smul_eq_mul, MvPolynomial.aeval_X]
    ring

end Cslib.Circuits.Arithmetic
