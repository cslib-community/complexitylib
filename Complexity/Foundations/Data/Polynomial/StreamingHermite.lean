/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, finite-field recovery of confluent Taylor data)

public import Complexity.Init
public import Complexity.Foundations.Data.Polynomial.HermiteInterpolation
public import Complexity.Foundations.FieldTheory.Finite.UnitSum

/-!
# Hermite recovery from finite-field evaluations

Suppose that `H` has degree less than the sum of the prescribed multiplicities at distinct nodes.
At node `t i` let `Y i` agree with the Taylor expansion of `H` below the prescribed multiplicity.
The higher coefficients of `Y i` may be arbitrary. Over a finite field of cardinality `q`, when
`degree (Y i) < q - 1`, values of these untruncated polynomials on the nonzero field elements
recover `H x` by an explicit double sum.

The proof first extracts a coefficient with the finite-field power sum, then applies the existing
Chinese-remainder form of Hermite interpolation. The kernel uses the normalized Hermite basis;
this is an equivalent normalization of the finite-field recovery argument communicated by
Charlie Cruz [Cruz2026SublinearSpace]. In particular, the recovery theorem does not assume a
reconstruction identity or a table of Taylor coefficients. This file proves the algebraic identity;
it makes no machine-space claim.

## Main definitions

* `Polynomial.hermiteEvalWeight`: the contribution of one Taylor monomial to evaluation at `x`.
* `Polynomial.hermiteEvalKernel`: the finite-field evaluation kernel at one node.

## Main results

* `FiniteField.sum_units_pow_mul_eval`: a weighted sum of polynomial values extracts one
  coefficient, under the sharp upper bound that excludes the next congruent degree.
* `Polynomial.eval_eq_sum_hermiteEvalWeight_mul_coeff`: Hermite reconstruction from arbitrary
  polynomials agreeing with the required Taylor coefficients.
* `Polynomial.eval_eq_sum_hermiteEvalKernel_mul_eval`: reconstruction by a double sum of
  finite-field evaluations, with no Taylor table in the formula.

## References

* Charlie Cruz, personal communication, 2026 [Cruz2026SublinearSpace].
-/

public noncomputable section

open Finset Polynomial

namespace FiniteField

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- The finite-field coefficient projector. The upper degree bound excludes the next exponent
congruent to `i` modulo `q - 1`; thus it also applies to polynomials of degree at least `q - 1`
when extracting a higher coefficient. -/
theorem sum_units_pow_mul_eval {P : K[X]} {i : ℕ}
    (hi : i < Fintype.card K - 1)
    (hP : P.natDegree < i + (Fintype.card K - 1)) :
    (∑ u : Kˣ, (u : K) ^ (Fintype.card K - 1 - i) * P.eval (u : K)) = -P.coeff i := by
  classical
  let q := Fintype.card K - 1
  change i < q at hi
  change P.natDegree < i + q at hP
  have hpow (j : ℕ) (hj : j ≤ P.natDegree) : q ∣ q - i + j ↔ j = i := by
    constructor
    · rintro ⟨m, hm⟩
      have hm0 : 0 < m := by
        by_contra hm0
        have : m = 0 := by omega
        simp only [this, mul_zero] at hm
        omega
      have hm2 : m < 2 := by
        by_contra hm2
        have hle := Nat.mul_le_mul_left q (show 2 ≤ m by omega)
        omega
      have hm1 : m = 1 := by omega
      simp only [hm1, mul_one] at hm
      omega
    · rintro rfl
      simpa only [Nat.sub_add_cancel hi.le] using dvd_refl q
  calc
    (∑ u : Kˣ, (u : K) ^ (Fintype.card K - 1 - i) * P.eval (u : K)) =
        ∑ j ∈ range (P.natDegree + 1),
          P.coeff j * ∑ u : Kˣ, (u : K) ^ (q - i + j) := by
      simp only [eval_eq_sum_range, mul_sum]
      rw [sum_comm]
      refine sum_congr rfl fun j _ => ?_
      refine sum_congr rfl fun u _ => ?_
      rw [pow_add]
      dsimp only [q]
      ring
    _ = ∑ j ∈ range (P.natDegree + 1), if j = i then -P.coeff j else 0 := by
      refine sum_congr rfl fun j hj => ?_
      have hdiv : Fintype.card K - 1 ∣ q - i + j ↔ j = i := hpow j (by simpa using hj)
      simp only [FiniteField.sum_pow_units, hdiv]
      split_ifs <;> simp
    _ = -P.coeff i := by
      by_cases hiP : i ≤ P.natDegree
      · simp [hiP]
      · have hcoeff := coeff_eq_zero_of_natDegree_lt (p := P) (by omega : P.natDegree < i)
        simp [hiP, hcoeff]

end FiniteField

namespace Polynomial

section HermiteWeights

variable {R : Type*} [CommRing R] {ι : Type*} [DecidableEq ι]

/-- The coefficient weight for evaluating a Hermite interpolant at `x`: insert the Taylor
monomial `X ^ j` at node `i`, take its local Hermite quotient, and evaluate its contribution. -/
@[expose] def hermiteEvalWeight (s : Finset ι) (t : ι → R) (J : ι → ℕ)
    (x : R) (i : ι) (j : ℕ) : R :=
  (hermiteBasis s t J i).eval x *
    (hermiteQuotient s t J 1 i ((X : R[X]) ^ j)).eval (x - t i)

/-- The local Hermite quotient depends only on coefficients below its prescribed multiplicity. -/
theorem hermiteQuotient_eq_of_coeff_lt (s : Finset ι) (t : ι → R) (J : ι → ℕ)
    (i : ι) {P Q : R[X]} (h : ∀ j < J i, P.coeff j = Q.coeff j) :
    hermiteQuotient s t J 1 i P = hermiteQuotient s t J 1 i Q := by
  rw [← hermiteQuotient_trunc s t J 1 i P, ← hermiteQuotient_trunc s t J 1 i Q]
  congr 1
  ext j
  simp only [PowerSeries.coeff_trunc, coeff_coe]
  split_ifs with hj
  · exact h j hj
  · rfl

/-- Expand the local Hermite quotient as a linear combination of the quotients of monomials.
Only coefficients below its prescribed multiplicity occur. -/
theorem hermiteQuotient_eq_sum (s : Finset ι) (t : ι → R) (J : ι → ℕ)
    (i : ι) (P : R[X]) :
    hermiteQuotient s t J 1 i P = ∑ j ∈ range (J i),
      C (P.coeff j) * hermiteQuotient s t J 1 i ((X : R[X]) ^ j) := by
  rw [← hermiteQuotient_trunc s t J 1 i P]
  rw [PowerSeries.trunc_apply, Nat.Ico_zero_eq_range]
  simp only [coeff_coe]
  unfold hermiteQuotient
  rw [show ((∑ j ∈ range (J i), monomial j (P.coeff j) : R[X]) : PowerSeries R) =
      ∑ j ∈ range (J i), (monomial j (P.coeff j) : PowerSeries R) from
    map_sum coeToPowerSeries.ringHom _ _]
  simp only [sum_mul, map_sum, ← C_mul_X_pow_eq_monomial, coe_mul, coe_C, coe_pow, mul_assoc,
    PowerSeries.trunc_C_mul]

/-- Hermite reconstruction using any polynomials that agree with the requisite Taylor
coefficients. No bound on their higher coefficients is needed for this coefficient formula. -/
theorem eval_eq_sum_hermiteEvalWeight_mul_coeff {s : Finset ι} {t : ι → R} {J : ι → ℕ}
    (ht : (s : Set ι).Pairwise fun i j => IsUnit (t i - t j)) {H : R[X]}
    (hH : H.degree < ↑(∑ i ∈ s, J i)) (Y : ι → R[X])
    (hY : ∀ i ∈ s, ∀ j < J i, (Y i).coeff j = (taylor (t i) H).coeff j)
    (x : R) :
    H.eval x = ∑ i ∈ s, ∑ j ∈ range (J i),
      hermiteEvalWeight s t J x i j * (Y i).coeff j := by
  rw [eval_eq_sum_hermiteBasis_mul_hermiteQuotient ht (1 : Rˣ) hH]
  simp only [Units.val_one, inv_one, one_mul, C_1, add_comm (C _) X, ← taylor_apply]
  refine sum_congr rfl fun i hi => ?_
  rw [← hermiteQuotient_eq_of_coeff_lt s t J i (hY i hi),
    hermiteQuotient_eq_sum, eval_finsetSum, mul_sum]
  refine sum_congr rfl fun j _ => ?_
  simp only [eval_mul, eval_C, hermiteEvalWeight]
  ring

end HermiteWeights

section FiniteField

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] {ι : Type*} [DecidableEq ι]

/-- A kernel recovering a Hermite interpolant directly from values of its local polynomials.
The finite sum defining the kernel involves only the prescribed node and multiplicity data. -/
@[expose] def hermiteEvalKernel (s : Finset ι) (t : ι → K) (J : ι → ℕ)
    (x : K) (i : ι) (u : K) : K :=
  -∑ j ∈ range (J i), hermiteEvalWeight s t J x i j *
    u ^ (Fintype.card K - 1 - j)

/-- **Recovery from untruncated finite-field evaluations.** Distinct nodes and the low Taylor
coefficients determine `H`. Each local polynomial may have arbitrary higher terms of degree
less than `q - 1`; summing its values over the nonzero field elements with `hermiteEvalKernel`
recovers `H x`. The only input-dependent quantities in the double sum are the values `Y i u`.
-/
theorem eval_eq_sum_hermiteEvalKernel_mul_eval {s : Finset ι} {t : ι → K} {J : ι → ℕ}
    (ht : (s : Set ι).Pairwise fun i j => IsUnit (t i - t j))
    (hJ : ∀ i ∈ s, J i < Fintype.card K) {H : K[X]}
    (hH : H.degree < ↑(∑ i ∈ s, J i)) (Y : ι → K[X])
    (hY : ∀ i ∈ s, ∀ j < J i, (Y i).coeff j = (taylor (t i) H).coeff j)
    (hdeg : ∀ i ∈ s, (Y i).natDegree < Fintype.card K - 1) (x : K) :
    H.eval x = ∑ i ∈ s, ∑ u : Kˣ,
      hermiteEvalKernel s t J x i (u : K) * (Y i).eval (u : K) := by
  classical
  rw [eval_eq_sum_hermiteEvalWeight_mul_coeff ht hH Y hY]
  refine sum_congr rfl fun i hi => ?_
  have hcoeff (j : ℕ) (hj : j ∈ range (J i)) :
      (Y i).coeff j = -(∑ u : Kˣ,
        (u : K) ^ (Fintype.card K - 1 - j) * (Y i).eval (u : K)) := by
    have hjq : j < Fintype.card K - 1 := by
      have := hJ i hi
      have := mem_range.mp hj
      omega
    rw [FiniteField.sum_units_pow_mul_eval (P := Y i) hjq (by have := hdeg i hi; omega),
      neg_neg]
  calc
    (∑ j ∈ range (J i), hermiteEvalWeight s t J x i j * (Y i).coeff j) =
        ∑ j ∈ range (J i), hermiteEvalWeight s t J x i j *
          -(∑ u : Kˣ, (u : K) ^ (Fintype.card K - 1 - j) * (Y i).eval (u : K)) :=
      sum_congr rfl fun j hj => congrArg (hermiteEvalWeight s t J x i j * ·) (hcoeff j hj)
    _ = ∑ u : Kˣ, hermiteEvalKernel s t J x i (u : K) * (Y i).eval (u : K) := by
      simp only [hermiteEvalKernel, mul_neg, mul_sum, neg_mul, sum_mul, mul_assoc,
        ← sum_neg_distrib]
      rw [sum_comm]

end FiniteField

end Polynomial
