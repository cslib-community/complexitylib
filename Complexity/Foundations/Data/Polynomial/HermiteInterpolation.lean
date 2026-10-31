/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, confluent Hermite interpolation)

public import Complexity.Init
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Confluent Hermite interpolation

A polynomial of degree less than `∑ i, J i` is determined by its first `J i` Taylor coefficients
at each node `t i`, provided the nodes differ by units. This file proves this with node-varying
multiplicities `J : ι → ℕ` over a finite set of nodes `s`, in two forms, over any commutative ring
whose nodes have unit differences:

* uniqueness: a polynomial of degree less than `∑ i ∈ s, J i` divisible by every `(X - t i) ^ J i`
  is zero (`Polynomial.eq_zero_of_forall_X_sub_C_pow_dvd`);
* the Chinese-remainder form: such a polynomial is `p = ∑ i ∈ s, E_i * r_i`, where the Hermite
  basis polynomial `E_i = ∏_{j ≠ i} ((X - t j) / (t i - t j)) ^ J j` (`Polynomial.hermiteBasis`) is
  `1` at `t i` and vanishes to order `J j` at the other nodes, and `r_i` is the truncation below
  order `J i` of the local quotient `p / E_i` at `t i`
  (`Polynomial.eq_sum_hermiteBasis_mul_of_dvd`). The local quotient is taken in the scaled
  coordinate `T = t i + α z` for a unit `α` (`Polynomial.hermiteQuotient`), so `r_i` depends only on
  the first `J i` coefficients of `p (t i + α z)`
  (`Polynomial.eq_sum_hermiteBasis_mul_hermiteQuotient`,
  `Polynomial.eval_eq_sum_hermiteBasis_mul_hermiteQuotient`).

For a uniform multiplicity `J` at `Q` nodes `t : Fin Q → R`, the order-`J` Taylor jet is the
family of coefficients `(Polynomial.taylor (t i) p).coeff j = [z ^ j] p (t i + z)`, for `i < Q`
and `j < J` (`Polynomial.taylorJet`), and uniqueness specializes to
`Polynomial.eq_zero_of_taylorJet_eq_zero`. For integer nodes, the integer confluent Vandermonde
matrix `Polynomial.hermiteMatrix` maps the coefficient vector to the jet, it is nonsingular when the
nodes are distinct, and Cramer's rule expresses each coefficient through two determinants
(`Polynomial.det_hermiteMatrix_mul_coeff`). Over a `ℚ`-algebra this recovers every coefficient,
and in particular the value at `0`, as a rational combination of the jet
(`Polynomial.eval_zero_eq_of_taylorJet`).

The coefficient of `X ^ u` is indexed by `c : Fin Q × Fin J` with `u = finProdFinEquiv c`, so the
Hermite matrix is square over `Fin Q × Fin J`. Its entry in row `(i, j)` and column `c` is
`(u choose j) * t i ^ (u - j)`, the coefficient of `z ^ j` in `(t i + z) ^ u`; it vanishes for
`u < j` because the binomial does.

This is the interpolation step of the subexponential counting algorithms of [OpenAI2026ETH]. In
§3.4 and Appendix B.3 the count is the value at `0` of a polynomial `H` of degree less than `Q * J`,
and only Taylor coefficients of `H` at the nodes `1, …, Q` are computed. The tapered recovery of
Lemma D.5 (§D.4.4, pp. 60–61) uses node-varying multiplicities and the Chinese-remainder form,
equation (D.9), with `α = 2 ^ (a + 1)`. Ordinary Lagrange interpolation (`Lagrange.interpolate`)
is the case of multiplicity `1`.

## Main definitions

* `Polynomial.hermiteBasis`: the Hermite basis polynomial `E_i` of node-varying multiplicities.
* `Polynomial.hermiteQuotient`: the truncated local quotient `(P / E_i (t i + α z)) mod z ^ J i`.
* `Polynomial.taylorJet`: the order-`J` Taylor jet at `Q` nodes, as a linear map.
* `Polynomial.hermiteMatrix`: the integer confluent Vandermonde matrix of integer nodes.

## Main results

* `Polynomial.eq_zero_of_forall_X_sub_C_pow_dvd`: uniqueness with node-varying multiplicities.
* `Polynomial.eq_sum_hermiteBasis_mul_of_dvd`: the Chinese-remainder form for any local factors
  satisfying the local congruences.
* `Polynomial.hermiteQuotient_eq_of_X_pow_dvd`, `Polynomial.X_pow_dvd_sub_mul_hermiteQuotient`: the
  Hermite quotient is the unique polynomial of degree less than `J i` satisfying the local
  congruence.
* `Polynomial.eq_sum_hermiteBasis_mul_hermiteQuotient`,
  `Polynomial.eval_eq_sum_hermiteBasis_mul_hermiteQuotient`: reconstruction from scaled local
  jets, equation (D.9) of [OpenAI2026ETH] at `0`.
* `Polynomial.eq_zero_of_taylorJet_eq_zero`, `Polynomial.eq_of_taylorJet_eq`: uniqueness for a
  uniform multiplicity.
* `Polynomial.hermiteMatrix_mulVec`: the Hermite matrix maps coefficients to the jet.
* `Polynomial.det_hermiteMatrix_ne_zero`: it is nonsingular at distinct integer nodes.
* `Polynomial.det_hermiteMatrix_mul_coeff`: Cramer's rule for the coefficients, over any
  commutative ring.
* `Polynomial.coeff_eq_of_taylorJet`, `Polynomial.eval_zero_eq_of_taylorJet`: reconstruction over
  a `ℚ`-algebra.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH]
-/

@[expose] public section

namespace Polynomial

open Finset Matrix

variable {R : Type*} [CommRing R] {Q J : ℕ}

/-! ### Node-varying multiplicities -/

section Multiplicities

variable {ι : Type*} {s : Finset ι} {t : ι → R} {J : ι → ℕ}

/-- `(X - r) ^ n` divides `p` exactly when the first `n` Taylor coefficients of `p` at `r`
vanish. -/
theorem X_sub_C_pow_dvd_iff_taylor_coeff {r : R} {n : ℕ} {p : R[X]} :
    (X - C r) ^ n ∣ p ↔ ∀ j < n, (taylor r p).coeff j = 0 := by
  rw [X_sub_C_pow_dvd_iff, ← taylor_apply, X_pow_dvd_iff]

/-- `(X - r) ^ n` divides `p` exactly when `z ^ n` divides `p (r + α z)`, for a unit `α`. -/
theorem X_sub_C_pow_dvd_iff_X_pow_dvd_comp (α : Rˣ) {r : R} {n : ℕ} {p : R[X]} :
    (X - C r) ^ n ∣ p ↔ X ^ n ∣ p.comp (C r + C (α : R) * X) := by
  have hσ : (C r + C (α : R) * X).comp (C (↑α⁻¹ : R) * (X - C r)) = X := by
    simp only [add_comp, C_comp, mul_comp, X_comp]
    rw [← mul_assoc, ← C_mul, Units.mul_inv, C_1, one_mul, add_sub_cancel]
  have hτ : (X - C r).comp (C r + C (α : R) * X) = C (α : R) * X := by
    simp only [sub_comp, X_comp, C_comp, add_sub_cancel_left]
  constructor
  · rintro ⟨q, rfl⟩
    rw [mul_comp, pow_comp, hτ, mul_pow, mul_comm (C _ ^ n), mul_assoc]
    exact dvd_mul_right _ _
  · rintro ⟨q, hq⟩
    have hp : p = (p.comp (C r + C (α : R) * X)).comp (C (↑α⁻¹ : R) * (X - C r)) := by
      rw [comp_assoc, hσ, comp_X]
    rw [hp, hq, mul_comp, pow_comp, X_comp, mul_pow, mul_comm (C _ ^ n), mul_assoc]
    exact dvd_mul_right _ _

/-- **Uniqueness of Hermite interpolation.** A polynomial of degree less than `∑ i ∈ s, J i` that
vanishes to order `J i` at each node `t i`, for nodes with unit differences, is zero. -/
theorem eq_zero_of_forall_X_sub_C_pow_dvd (ht : (s : Set ι).Pairwise fun i j => IsUnit (t i - t j))
    {p : R[X]} (hp : p.degree < ↑(∑ i ∈ s, J i)) (h : ∀ i ∈ s, (X - C (t i)) ^ J i ∣ p) :
    p = 0 := by
  nontriviality R
  by_contra h0
  have hcop : (s : Set ι).Pairwise (Function.onFun IsCoprime fun i => (X - C (t i)) ^ J i) :=
    fun i hi j hj hij => (isCoprime_X_sub_C_of_isUnit_sub (ht hi hj hij)).pow
  have hmon : ∀ i ∈ s, ((X - C (t i)) ^ J i).Monic := fun i _ => (monic_X_sub_C _).pow _
  refine (monic_prod_of_monic _ _ hmon).not_dvd_of_natDegree_lt h0 ?_
    (Finset.prod_dvd_of_coprime hcop h)
  rw [natDegree_prod_of_monic _ _ hmon]
  simpa only [(monic_X_sub_C _).natDegree_pow, natDegree_X_sub_C, mul_one] using
    (natDegree_lt_iff_degree_lt h0).mpr hp

variable [DecidableEq ι]

/-- The *Hermite basis polynomial* of node `i`,
`E_i = ∏_{j ∈ s, j ≠ i} ((X - t j) / (t i - t j)) ^ J j`, dividing by `Ring.inverse`. At nodes with
unit differences it is `1` at `t i` (`eval_hermiteBasis_self`) and vanishes to order `J k` at
every other node `t k` (`X_sub_C_pow_dvd_hermiteBasis`). With every `J j = 1` it is the Lagrange
basis polynomial. -/
noncomputable def hermiteBasis (s : Finset ι) (t : ι → R) (J : ι → ℕ) (i : ι) : R[X] :=
  ∏ j ∈ s.erase i, (C (Ring.inverse (t i - t j)) * (X - C (t j))) ^ J j

theorem eval_hermiteBasis (s : Finset ι) (t : ι → R) (J : ι → ℕ) (i : ι) (x : R) :
    (hermiteBasis s t J i).eval x =
      ∏ j ∈ s.erase i, (Ring.inverse (t i - t j) * (x - t j)) ^ J j := by
  simp only [hermiteBasis, eval_prod, eval_pow, eval_mul, eval_C, eval_sub, eval_X]

/-- The Hermite basis polynomial of a node is `1` at that node. -/
theorem eval_hermiteBasis_self (ht : (s : Set ι).Pairwise fun i j => IsUnit (t i - t j)) {i : ι}
    (hi : i ∈ s) : (hermiteBasis s t J i).eval (t i) = 1 := by
  rw [eval_hermiteBasis]
  refine Finset.prod_eq_one fun j hj => ?_
  rw [Ring.inverse_mul_cancel _
    (ht hi (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj).symm), one_pow]

/-- The Hermite basis polynomial of `i` vanishes to order `J k` at every other node `t k`. -/
theorem X_sub_C_pow_dvd_hermiteBasis {i k : ι} (hk : k ∈ s) (hki : k ≠ i) :
    (X - C (t k)) ^ J k ∣ hermiteBasis s t J i := by
  refine (Dvd.intro_left (C (Ring.inverse (t i - t k)) ^ J k) ?_).trans
    (Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨hki, hk⟩))
  rw [mul_pow]

theorem natDegree_hermiteBasis_le (s : Finset ι) (t : ι → R) (J : ι → ℕ) (i : ι) :
    (hermiteBasis s t J i).natDegree ≤ ∑ j ∈ s.erase i, J j := by
  refine (natDegree_prod_le _ _).trans (Finset.sum_le_sum fun j _ => natDegree_pow_le.trans ?_)
  calc J j * (C (Ring.inverse (t i - t j)) * (X - C (t j))).natDegree ≤ J j * 1 :=
        Nat.mul_le_mul_left _ ((natDegree_C_mul_le _ _).trans (natDegree_X_sub_C_le _))
    _ = J j := mul_one _

/-- The Hermite basis commutes with ring homomorphisms, at nodes with unit differences. -/
theorem map_hermiteBasis {S : Type*} [CommRing S] (f : R →+* S)
    (ht : (s : Set ι).Pairwise fun i j => IsUnit (t i - t j)) {i : ι} (hi : i ∈ s) :
    (hermiteBasis s t J i).map f = hermiteBasis s (fun j => f (t j)) J i := by
  simp only [hermiteBasis, Polynomial.map_prod, Polynomial.map_pow, Polynomial.map_mul, map_C,
    Polynomial.map_sub, map_X]
  refine Finset.prod_congr rfl fun j hj => ?_
  obtain ⟨u, hu⟩ := ht hi (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj).symm
  rw [← map_sub f, ← hu, Ring.inverse_unit]
  exact congrArg (fun x => (C x * (X - C (f (t j)))) ^ J j)
    (Ring.inverse_unit (Units.map (f : R →* S) u)).symm

/-- **The Chinese-remainder form of Hermite interpolation.** Let `p` have degree less than
`∑ i ∈ s, J i`, at nodes with unit differences. If at every node `r i` has degree less than `J i`
and `E_i * r i` agrees with `p` to order `J i` at `t i`, then `p = ∑ i ∈ s, E_i * r i`. -/
theorem eq_sum_hermiteBasis_mul_of_dvd (ht : (s : Set ι).Pairwise fun i j => IsUnit (t i - t j))
    {p : R[X]} (hp : p.degree < ↑(∑ i ∈ s, J i)) (r : ι → R[X])
    (hr : ∀ i ∈ s, (r i).degree < J i)
    (hdvd : ∀ i ∈ s, (X - C (t i)) ^ J i ∣ p - hermiteBasis s t J i * r i) :
    p = ∑ i ∈ s, hermiteBasis s t J i * r i := by
  refine sub_eq_zero.mp (eq_zero_of_forall_X_sub_C_pow_dvd (J := J) ht ?_ fun k hk => ?_)
  · refine (degree_sub_le _ _).trans_lt (max_lt hp ((degree_sum_le _ _).trans_lt ?_))
    refine (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).mpr fun i hi => ?_
    by_cases hri : r i = 0
    · rw [hri, mul_zero, degree_zero]
      exact WithBot.bot_lt_coe _
    refine degree_le_natDegree.trans_lt ?_
    rw [← Finset.add_sum_erase s J hi, Nat.cast_lt]
    have hri' := (natDegree_lt_iff_degree_lt hri).mpr (hr i hi)
    have hE := natDegree_hermiteBasis_le s t J i
    have hmul := natDegree_mul_le (p := hermiteBasis s t J i) (q := r i)
    omega
  · rw [← Finset.add_sum_erase s _ hk, ← sub_sub]
    exact dvd_sub (hdvd k hk) (Finset.dvd_sum fun i hi =>
      (X_sub_C_pow_dvd_hermiteBasis hk (Finset.ne_of_mem_erase hi).symm).mul_right _)

/-- The *Hermite quotient* at node `i` with scale `α` of a power series `P`: the truncation below
`z ^ J i` of `P(z) / E_i(t i + α z)`, using the power-series inverse of `E_i(t i + α z)`, whose
constant term `E_i(t i)` is `1` at nodes with unit differences. For `P(z) = p(t i + α z)` it is
the local factor of `p` at `t i` in the Chinese-remainder form of Hermite interpolation
(`eq_sum_hermiteBasis_mul_hermiteQuotient`). -/
noncomputable def hermiteQuotient (s : Finset ι) (t : ι → R) (J : ι → ℕ) (α : R) (i : ι)
    (P : PowerSeries R) : R[X] :=
  PowerSeries.trunc (J i)
    (P * PowerSeries.invOfUnit ((hermiteBasis s t J i).comp (C (t i) + C α * X) : PowerSeries R) 1)

/-- The Hermite quotient at node `i` depends only on the first `J i` coefficients. -/
@[simp]
theorem hermiteQuotient_trunc (s : Finset ι) (t : ι → R) (J : ι → ℕ) (α : R) (i : ι)
    (P : PowerSeries R) :
    hermiteQuotient s t J α i (PowerSeries.trunc (J i) P) = hermiteQuotient s t J α i P :=
  PowerSeries.trunc_trunc_mul _ _

theorem degree_hermiteQuotient_lt (s : Finset ι) (t : ι → R) (J : ι → ℕ) (α : R) (i : ι)
    (P : PowerSeries R) : (hermiteQuotient s t J α i P).degree < J i :=
  PowerSeries.degree_trunc_lt _ _

/-- The constant term of `E_i(t i + α z)` is `1`. -/
private theorem coeff_zero_hermiteBasis_comp
    (ht : (s : Set ι).Pairwise fun i j => IsUnit (t i - t j)) (α : R) {i : ι} (hi : i ∈ s) :
    ((hermiteBasis s t J i).comp (C (t i) + C α * X)).coeff 0 = 1 := by
  rw [coeff_zero_eq_eval_zero, eval_comp, eval_add, eval_C, eval_mul, eval_C, eval_X, mul_zero,
    add_zero, eval_hermiteBasis_self ht hi]

/-- **The defining congruence of the Hermite quotient.** For a polynomial `P`, the product
`E_i(t i + α z)` times the Hermite quotient of `P` agrees with `P` below `z ^ J i`. -/
theorem X_pow_dvd_sub_mul_hermiteQuotient
    (ht : (s : Set ι).Pairwise fun i j => IsUnit (t i - t j)) (α : R) {i : ι} (hi : i ∈ s)
    (P : R[X]) :
    X ^ J i ∣
      P - (hermiteBasis s t J i).comp (C (t i) + C α * X) * hermiteQuotient s t J α i P := by
  rw [X_pow_dvd_iff]
  intro d hd
  rw [coeff_sub, ← coeff_coe, ← coeff_coe, coe_mul, hermiteQuotient,
    PowerSeries.coeff_mul_eq_coeff_trunc_mul_trunc _ _ hd, PowerSeries.trunc_trunc,
    ← PowerSeries.coeff_mul_eq_coeff_trunc_mul_trunc _ _ hd, mul_left_comm,
    PowerSeries.mul_invOfUnit _ _ (by
      rw [constantCoeff_coe, coeff_zero_hermiteBasis_comp ht α hi, Units.val_one]),
    mul_one, sub_self]

/-- **The Hermite quotient is characterized by its congruence**: a polynomial of degree less than
`J i` whose product with `E_i(t i + α z)` agrees with `P` below `z ^ J i` is the Hermite
quotient of `P`. -/
theorem hermiteQuotient_eq_of_X_pow_dvd
    (ht : (s : Set ι).Pairwise fun i j => IsUnit (t i - t j)) (α : R) {i : ι} (hi : i ∈ s)
    {P q : R[X]} (hq : q.degree < J i)
    (h : X ^ J i ∣ P - (hermiteBasis s t J i).comp (C (t i) + C α * X) * q) :
    hermiteQuotient s t J α i P = q := by
  obtain ⟨g, hg⟩ := h
  have hP : (P : PowerSeries R) =
      ((hermiteBasis s t J i).comp (C (t i) + C α * X) : PowerSeries R) * (q : PowerSeries R) +
        PowerSeries.X ^ J i * (g : PowerSeries R) := by
    rw [← coe_X, ← coe_pow, ← coe_mul, ← coe_mul, ← coe_add, ← hg, add_sub_cancel]
  rw [hermiteQuotient, hP, add_mul, mul_comm _ (q : PowerSeries R), mul_assoc,
    PowerSeries.mul_invOfUnit _ _ (by
      rw [constantCoeff_coe, coeff_zero_hermiteBasis_comp ht α hi, Units.val_one]),
    mul_one, mul_assoc, map_add, PowerSeries.trunc_X_pow_self_mul, add_zero]
  by_cases hq0 : q = 0
  · rw [hq0, coe_zero, map_zero]
  exact PowerSeries.trunc_coe_eq_self ((natDegree_lt_iff_degree_lt hq0).mpr hq)

/-- **The Chinese-remainder form of Hermite interpolation, in scaled local coordinates.** Let `p`
have degree less than `∑ i ∈ s, J i`, at nodes with unit differences, and let `α` be a unit. Then
`p(T)` is the sum over the nodes of `E_i(T)` times the Hermite quotient of `p(t i + α z)` at
`z = (T - t i) / α`. Each summand uses only the first `J i` coefficients of `p(t i + α z)`
(`hermiteQuotient_trunc`). With `α = 1` the local coordinate is `z = T - t i`. -/
theorem eq_sum_hermiteBasis_mul_hermiteQuotient
    (ht : (s : Set ι).Pairwise fun i j => IsUnit (t i - t j)) (α : Rˣ) {p : R[X]}
    (hp : p.degree < ↑(∑ i ∈ s, J i)) :
    p = ∑ i ∈ s, hermiteBasis s t J i *
      (hermiteQuotient s t J α i (p.comp (C (t i) + C (α : R) * X))).comp
        (C (↑α⁻¹ : R) * (X - C (t i))) := by
  have hτσ : ∀ r : R, (C (↑α⁻¹ : R) * (X - C r)).comp (C r + C (α : R) * X) = X := fun r => by
    simp only [mul_comp, sub_comp, C_comp, X_comp, add_sub_cancel_left]
    rw [← mul_assoc, ← C_mul, Units.inv_mul, C_1, one_mul]
  refine eq_sum_hermiteBasis_mul_of_dvd ht hp _ (fun i _ => ?_) fun i hi => ?_
  · set q := hermiteQuotient s t J α i (p.comp (C (t i) + C (α : R) * X))
    by_cases hq : q = 0
    · rw [hq, zero_comp, degree_zero]
      exact WithBot.bot_lt_coe _
    refine (degree_le_natDegree.trans (Nat.cast_le.mpr natDegree_comp_le)).trans_lt ?_
    have hlin : (C (↑α⁻¹ : R) * (X - C (t i))).natDegree ≤ 1 :=
      (natDegree_C_mul_le _ _).trans (natDegree_X_sub_C_le _)
    refine lt_of_le_of_lt (Nat.cast_le.mpr ((Nat.mul_le_mul_left _ hlin).trans (mul_one _).le)) ?_
    exact Nat.cast_lt.mpr
      ((natDegree_lt_iff_degree_lt hq).mpr (degree_hermiteQuotient_lt _ _ _ _ _ _))
  · rw [X_sub_C_pow_dvd_iff_X_pow_dvd_comp α, sub_comp, mul_comp, comp_assoc, hτσ, comp_X]
    exact X_pow_dvd_sub_mul_hermiteQuotient ht _ hi _

/-- **Hermite reconstruction of a value (D.9).** Under the hypotheses of
`eq_sum_hermiteBasis_mul_hermiteQuotient`, `p(x) = ∑ i ∈ s, E_i(x) * Q_i((x - t i) / α)`, where
`Q_i` is the Hermite quotient of `p(t i + α z)`. At `x = 0` this is equation (D.9) of
[OpenAI2026ETH, §D.4.4, p. 60]. -/
theorem eval_eq_sum_hermiteBasis_mul_hermiteQuotient
    (ht : (s : Set ι).Pairwise fun i j => IsUnit (t i - t j)) (α : Rˣ) {p : R[X]}
    (hp : p.degree < ↑(∑ i ∈ s, J i)) (x : R) :
    p.eval x = ∑ i ∈ s, (hermiteBasis s t J i).eval x *
      (hermiteQuotient s t J α i (p.comp (C (t i) + C (α : R) * X))).eval
        ((↑α⁻¹ : R) * (x - t i)) := by
  conv_lhs => rw [eq_sum_hermiteBasis_mul_hermiteQuotient ht α hp]
  simp only [eval_finsetSum, eval_mul, eval_comp, eval_C, eval_sub, eval_X]

end Multiplicities

/-! ### Uniform multiplicity: Taylor jets -/

/-- The order-`J` Taylor jet of a polynomial at the nodes `t`: the coefficient of `z ^ j` in
`p (t i + z)`, for `i < Q` and `j < J`. -/
noncomputable def taylorJet (t : Fin Q → R) (J : ℕ) : R[X] →ₗ[R] Fin Q × Fin J → R :=
  LinearMap.pi fun r => lcoeff R r.2 ∘ₗ taylor (t r.1)

@[simp]
theorem taylorJet_apply (t : Fin Q → R) (J : ℕ) (p : R[X]) (r : Fin Q × Fin J) :
    taylorJet t J p r = (taylor (t r.1) p).coeff r.2 :=
  rfl

/-- **Uniqueness of confluent Hermite interpolation.** A polynomial of degree less than `Q * J`
whose order-`J` Taylor jet vanishes at `Q` nodes with unit differences is zero. -/
theorem eq_zero_of_taylorJet_eq_zero {t : Fin Q → R} (ht : Pairwise fun i j => IsUnit (t i - t j))
    {p : R[X]} (hp : p.degree < ↑(Q * J)) (h : taylorJet t J p = 0) : p = 0 :=
  eq_zero_of_forall_X_sub_C_pow_dvd (s := univ) (J := fun _ => J) (fun i _ j _ hij => ht hij)
    (by rwa [sum_const, card_univ, Fintype.card_fin, smul_eq_mul])
    fun i _ => X_sub_C_pow_dvd_iff_taylor_coeff.mpr fun j hj => congrFun h (i, ⟨j, hj⟩)

/-- Two polynomials of degree less than `Q * J` with the same order-`J` Taylor jet at `Q` nodes
with unit differences are equal. -/
theorem eq_of_taylorJet_eq {t : Fin Q → R} (ht : Pairwise fun i j => IsUnit (t i - t j))
    {p q : R[X]} (hp : p.degree < ↑(Q * J)) (hq : q.degree < ↑(Q * J))
    (h : taylorJet t J p = taylorJet t J q) : p = q :=
  sub_eq_zero.mp <| eq_zero_of_taylorJet_eq_zero ht ((degree_sub_le p q).trans_lt (max_lt hp hq))
    (by rw [map_sub, h, sub_self])

/-! ### The Hermite matrix and reconstruction -/

/-- The integer confluent Vandermonde (Hermite) matrix of the nodes `t`: the entry in row `(i, j)`
and column `c` is `(u choose j) * t i ^ (u - j)` with `u = finProdFinEquiv c`, the coefficient of
`z ^ j` in `(t i + z) ^ u`. -/
def hermiteMatrix (t : Fin Q → ℤ) (J : ℕ) : Matrix (Fin Q × Fin J) (Fin Q × Fin J) ℤ :=
  of fun r c => ((finProdFinEquiv c : ℕ).choose r.2 : ℤ) * t r.1 ^ ((finProdFinEquiv c : ℕ) - r.2)

theorem hermiteMatrix_apply (t : Fin Q → ℤ) (r c : Fin Q × Fin J) :
    hermiteMatrix t J r c =
      ((finProdFinEquiv c : ℕ).choose r.2 : ℤ) * t r.1 ^ ((finProdFinEquiv c : ℕ) - r.2) :=
  rfl

/-- **The Hermite matrix maps coefficients to the jet.** For `p` of degree less than `Q * J`, the
Hermite matrix applied to the vector of coefficients of `X ^ (finProdFinEquiv c)` is the order-`J`
Taylor jet of `p` at the nodes, over any commutative ring. -/
theorem hermiteMatrix_mulVec (t : Fin Q → ℤ) {p : R[X]} (hp : p.degree < ↑(Q * J)) :
    (hermiteMatrix t J).map (Int.cast : ℤ → R) *ᵥ (fun c => p.coeff (finProdFinEquiv c)) =
      taylorJet (fun i => (t i : R)) J p := by
  funext r
  rw [taylorJet_apply, taylor_coeff, hasseDeriv_apply, ← sum_fin _ (fun a => by simp) hp,
    eval_finsetSum, mulVec, dotProduct, ← finProdFinEquiv.sum_comp]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [map_apply, hermiteMatrix_apply, eval_monomial]
  push_cast
  ring

/-- **The Hermite matrix is nonsingular** at distinct integer nodes. -/
theorem det_hermiteMatrix_ne_zero {t : Fin Q → ℤ} (ht : Function.Injective t) :
    (hermiteMatrix t J).det ≠ 0 := by
  intro h0
  have h0' : ((hermiteMatrix t J).map (Int.cast : ℤ → ℚ)).det = 0 := by
    rw [← Int.cast_det, h0, Int.cast_zero]
  obtain ⟨v, hv, hV⟩ := exists_mulVec_eq_zero_iff.mpr h0'
  -- the polynomial whose coefficient of `X ^ (finProdFinEquiv c)` is `v c`
  set p : ℚ[X] := ((degreeLTEquiv ℚ (Q * J)).symm (v ∘ finProdFinEquiv.symm) : ℚ[X])
  have hcoeff : (fun c => p.coeff (finProdFinEquiv c)) = v := _root_.funext fun c => by
    have := congrFun ((degreeLTEquiv ℚ (Q * J)).apply_symm_apply (v ∘ finProdFinEquiv.symm))
      (finProdFinEquiv c)
    rwa [Function.comp_apply, Equiv.symm_apply_apply] at this
  have hp : p.degree < ↑(Q * J) :=
    mem_degreeLT.mp ((degreeLTEquiv ℚ (Q * J)).symm (v ∘ finProdFinEquiv.symm)).2
  have hunit : Pairwise fun i j => IsUnit ((t i : ℚ) - t j) := fun i j hij =>
    isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr (by exact_mod_cast ht.ne hij))
  have hjet := hermiteMatrix_mulVec t hp
  rw [hcoeff, hV] at hjet
  refine hv ?_
  rw [← hcoeff, eq_zero_of_taylorJet_eq_zero hunit hp hjet.symm]
  rfl

/-- **Cramer's rule for confluent Hermite interpolation**, over any commutative ring: for `p` of
degree less than `Q * J`, the determinant of the Hermite matrix times the coefficient of
`X ^ (finProdFinEquiv c)` is the determinant of the Hermite matrix with column `c` replaced by the
order-`J` Taylor jet of `p`. -/
theorem det_hermiteMatrix_mul_coeff (t : Fin Q → ℤ) {p : R[X]} (hp : p.degree < ↑(Q * J))
    (c : Fin Q × Fin J) :
    ((hermiteMatrix t J).det : R) * p.coeff (finProdFinEquiv c) =
      (((hermiteMatrix t J).map (Int.cast : ℤ → R)).updateCol c
        (taylorJet (fun i => (t i : R)) J p)).det := by
  rw [← cramer_apply, ← hermiteMatrix_mulVec t hp, cramer_eq_adjugate_mulVec, mulVec_mulVec,
    adjugate_mul, Int.cast_det, smul_mulVec, one_mulVec, Pi.smul_apply, smul_eq_mul]

/-- **Reconstruction over a `ℚ`-algebra.** At distinct integer nodes, each coefficient of a
polynomial of degree less than `Q * J` is a rational multiple of a determinant formed from the
Hermite matrix and the order-`J` Taylor jet. -/
theorem coeff_eq_of_taylorJet (A : Type*) [CommRing A] [Algebra ℚ A] {t : Fin Q → ℤ}
    (ht : Function.Injective t) {p : A[X]} (hp : p.degree < ↑(Q * J)) (c : Fin Q × Fin J) :
    p.coeff (finProdFinEquiv c) = ((hermiteMatrix t J).det : ℚ)⁻¹ •
      (((hermiteMatrix t J).map (Int.cast : ℤ → A)).updateCol c
        (taylorJet (fun i => (t i : A)) J p)).det := by
  have hd : ((hermiteMatrix t J).det : ℚ) ≠ 0 := by exact_mod_cast det_hermiteMatrix_ne_zero ht
  rw [← det_hermiteMatrix_mul_coeff t hp c, ← zsmul_eq_mul, ← Int.cast_smul_eq_zsmul ℚ, smul_smul,
    inv_mul_cancel₀ hd, one_smul]

/-- **The value at `0` from the jet (B.1).** At distinct integer nodes, the value at `0` of a
polynomial of degree less than `Q * J`, over a `ℚ`-algebra, is the determinant of the Hermite
matrix with its column for `X ^ 0` replaced by the order-`J` Taylor jet, divided by the determinant
of the Hermite matrix. -/
theorem eval_zero_eq_of_taylorJet (A : Type*) [CommRing A] [Algebra ℚ A] {t : Fin Q → ℤ}
    (ht : Function.Injective t) (hQ : 0 < Q) (hJ : 0 < J) {p : A[X]}
    (hp : p.degree < ↑(Q * J)) :
    p.eval 0 = ((hermiteMatrix t J).det : ℚ)⁻¹ •
      (((hermiteMatrix t J).map (Int.cast : ℤ → A)).updateCol (⟨0, hQ⟩, ⟨0, hJ⟩)
        (taylorJet (fun i => (t i : A)) J p)).det := by
  rw [← coeff_eq_of_taylorJet A ht hp, ← coeff_zero_eq_eval_zero]
  congr 1

end Polynomial
