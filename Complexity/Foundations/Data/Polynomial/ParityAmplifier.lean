/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.Data.Polynomial.CoeffNorm1
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Data.Int.ModEq
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Integer parity-amplifying polynomials and shared-total-order truncation

For `ℓ ≥ 1`, the complement of the Beigel–Tarui modulus-amplifying polynomial [Toda][Toda1991],
[Arora and Barak, Section 17.4][AroraBarak09],
$$p_\ell(Y) = (1 - Y)^\ell \sum_{j=0}^{\ell-1} \binom{\ell - 1 + j}{j} Y^j \in \mathbb{Z}[Y],$$
satisfies $p_\ell(Y) \equiv 1 \pmod{Y^\ell}$ and $p_\ell(Y) \equiv 0 \pmod{(1 - Y)^\ell}$, so
for every integer $y \in \mathbb{Z}$, $p_\ell(y) \equiv \mathbf{1}_{\{2 \mid y\}} \pmod{2^\ell}$
(`Polynomial.parityAmplifier_eval_modEq_two_pow`).

Following Lemma 5.1 and Lemma B.1 of
[OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], writing $p_\ell$ in powers of
the monic quadratic $h(Y) = Y^2 - Y = Y(Y - 1)$ (`Polynomial.hPoly`) by successive monic division
produces remainders $e_0, \dots, e_{\ell-1} \in \mathbb{Z}[Y]$ (`Polynomial.parityBaseDigit`) of
degree at most $1$ with $p_\ell(Y) = \sum_{j=0}^{\ell-1} e_j(Y) h(Y)^j$
(`Polynomial.parityAmplifier_eq_sum_baseDigit`) and explicit coefficient bounds
(`Polynomial.natAbs_coeff_parityBaseDigit_le`, `Polynomial.coeffNorm1_parityBaseDigit_le`).

Since $h(y) = y(y - 1)$ is even for every $y \in \mathbb{Z}$, introducing a shared formal variable
$V$ (`Polynomial.parityFactor`) across a family of equations and discarding powers $V^s$ with
$s \ge \ell$ via `Polynomial.sumCoeffsBelow` (Lemma 5.2 of [OpenAI2026ETH]) preserves the product
of evenness indicators modulo $2^\ell$ (`Polynomial.sumCoeffsBelow_prod_parityFactor_modEq`), while
bounding the multivariate total degree of every retained coefficient and of their sum by
$d_* (\#I + 2(\ell - 1))$ when each input polynomial has total degree at most $d_*$
(`Polynomial.totalDegree_sumCoeffsBelow_prod_parityFactor_le`).

## Main definitions

* `Polynomial.hPoly`: the monic quadratic `X ^ 2 - X` in `ℤ[X]`.
* `Polynomial.parityKernel`: the partial binomial series `∑ j < ℓ, choose (ℓ - 1 + j) j * X ^ j`.
* `Polynomial.parityAmplifier`: the even-parity amplifying polynomial `p_ℓ(X) ∈ ℤ[X]`.
* `Polynomial.iterDivByH`, `Polynomial.baseDigitByH`, `Polynomial.parityBaseDigit`: successive
  monic quotients and linear remainders `e_j(X)` on division by `X ^ 2 - X`.
* `Polynomial.coeffNorm1`: the `ℓ₁` coefficient norm `∑ i ∈ p.support, (p.coeff i).natAbs`.
* `Polynomial.parityFactor`: the `V`-series factor `B(y; V) = ∑ j < ℓ, e_j(y) h(y)^j V^j`.
* `Polynomial.sumCoeffsBelow`: the truncated coefficient sum `S_ℓ(P) = ∑ s < ℓ, P.coeff s`.

## Main results

* `Polynomial.parityAmplifier_add_X_pow_mul_eq_one`: Bezout identity
  `p_ℓ(X) + X ^ ℓ * ∑ m < ℓ, choose (m + ℓ - 1) (ℓ - 1) * (1 - X) ^ m = 1` for `ℓ ≥ 1`.
* `Polynomial.parityAmplifier_eval_modEq_two_pow`:
  `p_ℓ(y) ≡ (if Even y then 1 else 0) [ZMOD 2 ^ ℓ]`.
* `Polynomial.parityAmplifier_eq_sum_baseDigit`: `p_ℓ = ∑ j < ℓ, e_j * (X ^ 2 - X) ^ j`.
* `Polynomial.coeffNorm1_parityAmplifier_le`: `‖p_ℓ‖₁ ≤ 2 ^ (3 * ℓ)`.
* `Polynomial.natAbs_coeff_parityBaseDigit_le`: `|coeff k (e_j)| ≤ (2 * ℓ) ^ j * 2 ^ (3 * ℓ)`.
* `Polynomial.coeffNorm1_parityBaseDigit_le`: `‖e_j‖₁ ≤ 2 * ((2 * ℓ) ^ j * 2 ^ (3 * ℓ))`.
* `Polynomial.sumCoeffsBelow_prod_parityFactor_modEq`: shared-`V` truncation modulo `2 ^ ℓ`.
* `Polynomial.totalDegree_sumCoeffsBelow_prod_parityFactor_le`: linear total-degree bound
  `totalDegree ≤ d_* * (#I + 2 * (ℓ - 1))`.

## References

* [S. Toda, *PP is as hard as the polynomial-time hierarchy*][Toda1991]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH] (Lemmas 5.1, 5.2, and B.1)
-/

@[expose] public noncomputable section

namespace Polynomial

open Finset

/-! ### 1. The univariate even-parity amplifier `p_ℓ(X)` -/

/-- The partial binomial series `g(m, K) = ∑ j ∈ range K, choose (m + j) j * X ^ j` in `ℤ[X]`. -/
def paritySeriesAux (m K : ℕ) : ℤ[X] :=
  ∑ j ∈ range K, (Nat.choose (m + j) j : ℤ[X]) * X ^ j

/-- The kernel `∑ j ∈ range ℓ, choose (ℓ - 1 + j) j * X ^ j` of the even-parity amplifier. -/
def parityKernel (ℓ : ℕ) : ℤ[X] :=
  paritySeriesAux (ℓ - 1) ℓ

/-- The even-parity amplifying polynomial
`p_ℓ(X) = (1 - X) ^ ℓ * ∑ j ∈ range ℓ, choose (ℓ - 1 + j) j * X ^ j` in `ℤ[X]`. -/
def parityAmplifier (ℓ : ℕ) : ℤ[X] :=
  (1 - X) ^ ℓ * parityKernel ℓ

/-- At precision `0`, `parityAmplifier 0` is `0`. -/
@[simp]
theorem parityAmplifier_zero : parityAmplifier 0 = 0 := by
  simp only [parityAmplifier, parityKernel, paritySeriesAux, range_zero, sum_empty, mul_zero]

/-- At precision `1`, `parityAmplifier 1 = 1 - X`. -/
theorem parityAmplifier_one : parityAmplifier 1 = 1 - X := by
  simp only [parityAmplifier, parityKernel, paritySeriesAux, tsub_self, range_one, sum_singleton,
    add_zero, Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one, pow_one]

/-- At precision `2`, `parityAmplifier 2 = 1 - 3 * X ^ 2 + 2 * X ^ 3`. -/
theorem parityAmplifier_two : parityAmplifier 2 = 1 - 3 * X ^ 2 + 2 * X ^ 3 := by
  have hkern : parityKernel 2 = 1 + 2 * X := by
    unfold parityKernel paritySeriesAux
    rw [sum_range_succ, sum_range_one]
    simp only [Nat.reduceSub, add_zero, Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one,
      Nat.reduceAdd, Nat.choose_one_right, Nat.cast_ofNat, pow_one]
  rw [parityAmplifier, hkern]
  ring

/-- `(1 - X) ^ ℓ` divides `parityAmplifier ℓ` in `ℤ[X]`. -/
theorem one_sub_X_pow_dvd_parityAmplifier (ℓ : ℕ) :
    (1 - X : ℤ[X]) ^ ℓ ∣ parityAmplifier ℓ :=
  dvd_mul_right _ _

private theorem one_sub_X_mul_paritySeriesAux_zero (K : ℕ) :
    (1 - X) * paritySeriesAux 0 K = 1 - X ^ K := by
  induction K with
  | zero =>
    simp only [paritySeriesAux, range_zero, sum_empty, mul_zero, pow_zero, sub_self]
  | succ K ih =>
    rw [paritySeriesAux, sum_range_succ, zero_add, Nat.choose_self, Nat.cast_one, one_mul,
      mul_add, ← paritySeriesAux, ih]
    ring

private theorem one_sub_X_mul_paritySeriesAux_succ (m k : ℕ) :
    (1 - X) * paritySeriesAux (m + 1) (k + 1) =
      paritySeriesAux m (k + 1) - (Nat.choose (m + k + 1) k : ℤ[X]) * X ^ (k + 1) := by
  induction k with
  | zero =>
    change (1 - X) * ∑ j ∈ range 1, (Nat.choose (m + 1 + j) j : ℤ[X]) * X ^ j =
      (∑ j ∈ range 1, (Nat.choose (m + j) j : ℤ[X]) * X ^ j) -
        (Nat.choose (m + 0 + 1) 0 : ℤ[X]) * X ^ 1
    simp only [range_one, sum_singleton, add_zero, Nat.choose_zero_right, Nat.cast_one,
      pow_zero, mul_one, pow_one]
    ring
  | succ k ih =>
    have hchoose :
        (Nat.choose (m + 1 + (k + 1)) (k + 1) : ℤ[X]) =
          (Nat.choose (m + k + 1) k : ℤ[X]) + (Nat.choose (m + (k + 1)) (k + 1) : ℤ[X]) := by
      have hpas : Nat.choose (m + k + 1 + 1) (k + 1) =
          Nat.choose (m + k + 1) k + Nat.choose (m + k + 1) (k + 1) :=
        Nat.choose_succ_succ (m + k + 1) k
      have hm : m + 1 + (k + 1) = m + k + 1 + 1 := by omega
      have hm2 : m + (k + 1) = m + k + 1 := by omega
      rw [hm, hm2, hpas, Nat.cast_add]
    have hstep1 : paritySeriesAux (m + 1) (k + 1 + 1) =
        paritySeriesAux (m + 1) (k + 1) +
          (Nat.choose (m + 1 + (k + 1)) (k + 1) : ℤ[X]) * X ^ (k + 1) := by
      unfold paritySeriesAux
      exact sum_range_succ _ (k + 1)
    have hstep2 : paritySeriesAux m (k + 1 + 1) =
        paritySeriesAux m (k + 1) +
          (Nat.choose (m + (k + 1)) (k + 1) : ℤ[X]) * X ^ (k + 1) := by
      unfold paritySeriesAux
      exact sum_range_succ _ (k + 1)
    have hm : m + (k + 1) + 1 = m + 1 + (k + 1) := by omega
    rw [hstep1, mul_add, ih, hstep2, hm, hchoose]
    ring

private theorem one_sub_X_pow_mul_paritySeriesAux_add_sum (m k : ℕ) :
    (1 - X) ^ (m + 1) * paritySeriesAux m (k + 1) +
      X ^ (k + 1) * ∑ i ∈ range (m + 1), (Nat.choose (i + k) k : ℤ[X]) * (1 - X) ^ i = 1 := by
  induction m with
  | zero =>
    change (1 - X) ^ 1 * paritySeriesAux 0 (k + 1) +
      X ^ (k + 1) * ∑ i ∈ range 1, (Nat.choose (i + k) k : ℤ[X]) * (1 - X) ^ i = 1
    simp only [pow_one, one_sub_X_mul_paritySeriesAux_zero, range_one, sum_singleton, zero_add,
      Nat.choose_self, Nat.cast_one, pow_zero, mul_one, sub_add_cancel]
  | succ m ih =>
    have hstep :
        (1 - X) ^ (m + 1 + 1) * paritySeriesAux (m + 1) (k + 1) =
          (1 - X) ^ (m + 1) * paritySeriesAux m (k + 1) -
            X ^ (k + 1) * ((Nat.choose (m + 1 + k) k : ℤ[X]) * (1 - X) ^ (m + 1)) := by
      calc
        (1 - X) ^ (m + 1 + 1) * paritySeriesAux (m + 1) (k + 1)
          = (1 - X) ^ (m + 1) * ((1 - X) * paritySeriesAux (m + 1) (k + 1)) := by ring
        _ = (1 - X) ^ (m + 1) *
              (paritySeriesAux m (k + 1) - (Nat.choose (m + k + 1) k : ℤ[X]) * X ^ (k + 1)) := by
            rw [one_sub_X_mul_paritySeriesAux_succ]
        _ = (1 - X) ^ (m + 1) * paritySeriesAux m (k + 1) -
              X ^ (k + 1) * ((Nat.choose (m + 1 + k) k : ℤ[X]) * (1 - X) ^ (m + 1)) := by
            have hm : m + k + 1 = m + 1 + k := by omega
            rw [hm]
            ring
    rw [sum_range_succ, mul_add, hstep]
    calc
      (1 - X) ^ (m + 1) * paritySeriesAux m (k + 1) -
          X ^ (k + 1) * ((Nat.choose (m + 1 + k) k : ℤ[X]) * (1 - X) ^ (m + 1)) +
          (X ^ (k + 1) * ∑ i ∈ range (m + 1), (Nat.choose (i + k) k : ℤ[X]) * (1 - X) ^ i +
            X ^ (k + 1) * ((Nat.choose (m + 1 + k) k : ℤ[X]) * (1 - X) ^ (m + 1)))
        = (1 - X) ^ (m + 1) * paritySeriesAux m (k + 1) +
            X ^ (k + 1) * ∑ i ∈ range (m + 1), (Nat.choose (i + k) k : ℤ[X]) * (1 - X) ^ i := by
          ring
      _ = 1 := ih

/-- Exact Bezout identity for `parityAmplifier ℓ` (`ℓ ≥ 1`):
`p_ℓ(X) + X ^ ℓ * ∑ i ∈ range ℓ, choose (i + ℓ - 1) (ℓ - 1) * (1 - X) ^ i = 1`. -/
theorem parityAmplifier_add_X_pow_mul_eq_one {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    parityAmplifier ℓ +
      X ^ ℓ * ∑ i ∈ range ℓ, (Nat.choose (i + (ℓ - 1)) (ℓ - 1) : ℤ[X]) * (1 - X) ^ i = 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
  simpa only [parityAmplifier, parityKernel, add_tsub_cancel_right] using
    one_sub_X_pow_mul_paritySeriesAux_add_sum k k

/-- For `ℓ ≥ 1`, `X ^ ℓ` divides `1 - parityAmplifier ℓ` in `ℤ[X]`. -/
theorem X_pow_dvd_one_sub_parityAmplifier {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    X ^ ℓ ∣ 1 - parityAmplifier ℓ := by
  refine ⟨∑ i ∈ range ℓ, (Nat.choose (i + (ℓ - 1)) (ℓ - 1) : ℤ[X]) * (1 - X) ^ i, ?_⟩
  exact (eq_sub_of_add_eq' (parityAmplifier_add_X_pow_mul_eq_one hℓ)).symm

/-- At any even integer `y`, `parityAmplifier ℓ` (`ℓ ≥ 1`) evaluates to `1` modulo `2 ^ ℓ`. -/
theorem parityAmplifier_eval_modEq_one_of_even {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {y : ℤ} (hy : Even y) :
    (parityAmplifier ℓ).eval y ≡ 1 [ZMOD (2 : ℤ) ^ ℓ] := by
  rw [Int.modEq_iff_dvd]
  obtain ⟨q, hq⟩ := X_pow_dvd_one_sub_parityAmplifier hℓ
  have heval : 1 - (parityAmplifier ℓ).eval y = y ^ ℓ * q.eval y := by
    have := congr_arg (eval y) hq
    simpa only [eval_sub, eval_one, eval_mul, eval_pow, eval_X] using this
  rw [heval]
  obtain ⟨k, rfl⟩ := hy
  have h2 : (2 : ℤ) ∣ k + k := ⟨k, by ring⟩
  exact dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd h2 ℓ) _

/-- At any odd integer `y`, `parityAmplifier ℓ` evaluates to `0` modulo `2 ^ ℓ`. -/
theorem parityAmplifier_eval_modEq_zero_of_odd (ℓ : ℕ) {y : ℤ} (hy : Odd y) :
    (parityAmplifier ℓ).eval y ≡ 0 [ZMOD (2 : ℤ) ^ ℓ] := by
  rw [Int.modEq_iff_dvd, zero_sub, dvd_neg]
  obtain ⟨q, hq⟩ := one_sub_X_pow_dvd_parityAmplifier ℓ
  have heval : (parityAmplifier ℓ).eval y = (1 - y) ^ ℓ * q.eval y := by
    have := congr_arg (eval y) hq
    simpa only [eval_mul, eval_pow, eval_sub, eval_one, eval_X] using this
  rw [heval]
  obtain ⟨k, rfl⟩ := hy
  have h2 : (2 : ℤ) ∣ 1 - (2 * k + 1) := ⟨-k, by ring⟩
  exact dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd h2 ℓ) _

/-- **Lemma 5.1 (parity congruence)**: for `ℓ ≥ 1` and `y ∈ ℤ`,
`p_ℓ(y) ≡ (if Even y then 1 else 0) (mod 2 ^ ℓ)`. -/
theorem parityAmplifier_eval_modEq_two_pow {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (y : ℤ) [Decidable (Even y)] :
    (parityAmplifier ℓ).eval y ≡ (if Even y then 1 else 0) [ZMOD (2 : ℤ) ^ ℓ] := by
  split_ifs with hy
  · exact parityAmplifier_eval_modEq_one_of_even hℓ hy
  · exact parityAmplifier_eval_modEq_zero_of_odd ℓ (Int.not_even_iff_odd.mp hy)

/-! ### 2. Base-`h(X)` expansion (`h(X) = X ^ 2 - X`) and degree bounds -/

/-- The monic quadratic `h(X) = X ^ 2 - X = X * (X - 1)` in `ℤ[X]`. -/
def hPoly : ℤ[X] :=
  X ^ 2 - X

/-- `hPoly = X ^ 2 - X` is monic. -/
theorem monic_hPoly : hPoly.Monic := by
  apply Monic.sub_of_left (monic_X_pow 2)
  rw [degree_X, degree_X_pow]
  decide

/-- `hPoly` has degree `2`. -/
@[simp]
theorem natDegree_hPoly : hPoly.natDegree = 2 := by
  rw [hPoly, natDegree_sub_eq_left_of_natDegree_lt]
  · exact natDegree_X_pow 2
  · rw [natDegree_X, natDegree_X_pow]
    omega

/-- `hPoly` is not equal to `1`. -/
theorem hPoly_ne_one : hPoly ≠ 1 := by
  intro h
  have := congr_arg natDegree h
  rw [natDegree_hPoly, natDegree_one] at this
  omega

/-- Evaluation of an integer polynomial `P : ℤ[X]` at `y : A` via the canonical cast `ℤ →+* A`. -/
def evalInt {A : Type*} [CommRing A] (y : A) (P : ℤ[X]) : A :=
  P.eval₂ (Int.castRingHom A) y

/-- On `ℤ`, `evalInt` coincides with `Polynomial.eval`. -/
@[simp]
theorem evalInt_int (y : ℤ) (P : ℤ[X]) : evalInt y P = P.eval y := by
  simp only [evalInt, Int.castRingHom_int, eval₂_id]

/-- Evaluating `hPoly` at `y : A` gives `y ^ 2 - y`. -/
@[simp]
theorem evalInt_hPoly {A : Type*} [CommRing A] (y : A) :
    evalInt y hPoly = y ^ 2 - y := by
  simp only [evalInt, hPoly, eval₂_sub, eval₂_X_pow, eval₂_X]

/-- Evaluating `hPoly` at `y : ℤ` gives `y ^ 2 - y`. -/
@[simp]
theorem eval_hPoly (y : ℤ) : hPoly.eval y = y ^ 2 - y := by
  simp only [hPoly, eval_sub, eval_pow, eval_X]

/-- For every integer `y`, `h(y) = y ^ 2 - y` is even. -/
theorem two_dvd_eval_hPoly (y : ℤ) : (2 : ℤ) ∣ hPoly.eval y := by
  rw [eval_hPoly]
  rcases Int.even_or_odd y with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · refine ⟨(k + k) * k - k, by ring⟩
  · refine ⟨(2 * k + 1) * k, by ring⟩

/-- Iterated monic quotient of `P : ℤ[X]` on division by `hPoly = X ^ 2 - X`. -/
def iterDivByH (P : ℤ[X]) : ℕ → ℤ[X]
  | 0 => P
  | j + 1 => iterDivByH P j /ₘ hPoly

/-- The `j`-th remainder `(iterDivByH P j) %ₘ hPoly` in the base-`hPoly` expansion of `P`. -/
def baseDigitByH (P : ℤ[X]) (j : ℕ) : ℤ[X] :=
  iterDivByH P j %ₘ hPoly

/-- The `j`-th linear remainder `e_j(X)` in the base-`(X ^ 2 - X)` expansion of `p_ℓ(X)`. -/
def parityBaseDigit (ℓ j : ℕ) : ℤ[X] :=
  baseDigitByH (parityAmplifier ℓ) j

/-- Remainder modulo `hPoly` has degree at most `1`. -/
theorem natDegree_modByMonic_hPoly_le (P : ℤ[X]) : (P %ₘ hPoly).natDegree ≤ 1 := by
  have hlt := natDegree_modByMonic_lt P monic_hPoly hPoly_ne_one
  rw [natDegree_hPoly] at hlt
  omega

/-- Each `baseDigitByH P j` has degree at most `1`. -/
theorem natDegree_baseDigitByH_le (P : ℤ[X]) (j : ℕ) :
    (baseDigitByH P j).natDegree ≤ 1 :=
  natDegree_modByMonic_hPoly_le (iterDivByH P j)

/-- Each `parityBaseDigit ℓ j` (`e_j`) has degree at most `1`. -/
theorem natDegree_parityBaseDigit_le (ℓ j : ℕ) :
    (parityBaseDigit ℓ j).natDegree ≤ 1 :=
  natDegree_baseDigitByH_le (parityAmplifier ℓ) j

/-- Explicit affine decomposition `e_j(X) = a_j + b_j X` of `parityBaseDigit ℓ j`. -/
theorem parityBaseDigit_eq_C_add_C_mul_X (ℓ j : ℕ) :
    parityBaseDigit ℓ j =
      C ((parityBaseDigit ℓ j).coeff 0) + C ((parityBaseDigit ℓ j).coeff 1) * X :=
  (eq_X_add_C_of_natDegree_le_one (natDegree_parityBaseDigit_le ℓ j)).trans (add_comm _ _)

/-- Division expansion after `m` steps of monic division by `hPoly`:
`P = (∑ j ∈ range m, baseDigitByH P j * hPoly ^ j) + iterDivByH P m * hPoly ^ m`. -/
theorem eq_sum_baseDigitByH_add_iterDivByH (P : ℤ[X]) (m : ℕ) :
    P = (∑ j ∈ range m, baseDigitByH P j * hPoly ^ j) + iterDivByH P m * hPoly ^ m := by
  induction m with
  | zero =>
    simp only [range_zero, sum_empty, iterDivByH, pow_zero, mul_one, zero_add]
  | succ m ih =>
    have hstep := modByMonic_add_div (iterDivByH P m) hPoly
    calc
      P = (∑ j ∈ range m, baseDigitByH P j * hPoly ^ j) + iterDivByH P m * hPoly ^ m := ih
      _ = (∑ j ∈ range m, baseDigitByH P j * hPoly ^ j) +
            (iterDivByH P m %ₘ hPoly + hPoly * (iterDivByH P m /ₘ hPoly)) * hPoly ^ m := by
          rw [hstep]
      _ = (∑ j ∈ range (m + 1), baseDigitByH P j * hPoly ^ j) +
            iterDivByH P (m + 1) * hPoly ^ (m + 1) := by
          rw [sum_range_succ]
          simp only [baseDigitByH, iterDivByH, pow_succ]
          ring

/-- `iterDivByH P j` has degree `P.natDegree - 2 * j`. -/
theorem natDegree_iterDivByH (P : ℤ[X]) (j : ℕ) :
    (iterDivByH P j).natDegree = P.natDegree - 2 * j := by
  induction j with
  | zero => simp only [iterDivByH, mul_zero, Nat.sub_zero]
  | succ j ih =>
    rw [iterDivByH, natDegree_divByMonic _ monic_hPoly, ih, natDegree_hPoly]
    omega

/-- `iterDivByH P j` vanishes once `P.natDegree < 2 * j` (or `P = 0`). -/
theorem iterDivByH_eq_zero_of_natDegree_lt {P : ℤ[X]} {j : ℕ}
    (h : P = 0 ∨ P.natDegree < 2 * j) :
    iterDivByH P j = 0 := by
  induction j with
  | zero =>
    rcases h with rfl | hlt
    · rfl
    · omega
  | succ j ih =>
    by_cases h0 : iterDivByH P j = 0
    · simp only [iterDivByH, h0, zero_divByMonic]
    · rw [iterDivByH, (divByMonic_eq_zero_iff monic_hPoly).mpr]
      rw [degree_eq_natDegree h0, degree_eq_natDegree monic_hPoly.ne_zero, Nat.cast_lt,
        natDegree_iterDivByH, natDegree_hPoly]
      rcases h with rfl | hlt
      · exfalso
        apply h0
        exact ih (Or.inl rfl)
      · omega

private theorem natDegree_paritySeriesAux_le (m K : ℕ) :
    (paritySeriesAux m K).natDegree ≤ K - 1 := by
  refine natDegree_sum_le_of_forall_le (range K) _ fun j hj => ?_
  rw [mem_range] at hj
  refine natDegree_mul_le.trans ?_
  rw [natDegree_natCast, zero_add, natDegree_X_pow]
  omega

/-- `parityKernel ℓ` has degree at most `ℓ - 1`. -/
theorem natDegree_parityKernel_le (ℓ : ℕ) :
    (parityKernel ℓ).natDegree ≤ ℓ - 1 :=
  natDegree_paritySeriesAux_le (ℓ - 1) ℓ

/-- `parityAmplifier ℓ` has degree at most `2 * ℓ - 1`. -/
theorem natDegree_parityAmplifier_le (ℓ : ℕ) :
    (parityAmplifier ℓ).natDegree ≤ 2 * ℓ - 1 := by
  rw [parityAmplifier]
  refine natDegree_mul_le.trans ?_
  have h1 : ((1 - X : ℤ[X]) ^ ℓ).natDegree ≤ ℓ := by
    refine natDegree_pow_le.trans ?_
    have h1X : (1 - X : ℤ[X]).natDegree ≤ 1 := by
      refine (natDegree_sub_le 1 X).trans ?_
      simp only [natDegree_one, natDegree_X, max_le_iff, zero_le, le_refl, and_self]
    nlinarith
  have h2 := natDegree_parityKernel_le ℓ
  omega

/-- After `ℓ` divisions by `hPoly`, the quotient of `parityAmplifier ℓ` is `0`. -/
theorem iterDivByH_parityAmplifier_self (ℓ : ℕ) :
    iterDivByH (parityAmplifier ℓ) ℓ = 0 := by
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
  · exact iterDivByH_eq_zero_of_natDegree_lt (Or.inl parityAmplifier_zero)
  · apply iterDivByH_eq_zero_of_natDegree_lt
    right
    have := natDegree_parityAmplifier_le ℓ
    omega

/-- **Lemma 5.1 (base-`h` decomposition)**: for every `ℓ : ℕ`,
`parityAmplifier ℓ = ∑ j ∈ range ℓ, parityBaseDigit ℓ j * hPoly ^ j`. -/
theorem parityAmplifier_eq_sum_baseDigit (ℓ : ℕ) :
    parityAmplifier ℓ = ∑ j ∈ range ℓ, parityBaseDigit ℓ j * hPoly ^ j := by
  have h := eq_sum_baseDigitByH_add_iterDivByH (parityAmplifier ℓ) ℓ
  rw [iterDivByH_parityAmplifier_self, zero_mul, add_zero] at h
  exact h

/-- Evaluation of `parityAmplifier ℓ` in any commutative ring `A` via `parityBaseDigit`. -/
theorem evalInt_parityAmplifier_eq_sum {A : Type*} [CommRing A] (ℓ : ℕ) (y : A) :
    evalInt y (parityAmplifier ℓ) =
      ∑ j ∈ range ℓ, evalInt y (parityBaseDigit ℓ j) * (y ^ 2 - y) ^ j := by
  unfold evalInt
  rw [← coe_eval₂RingHom]
  conv_lhs => rw [parityAmplifier_eq_sum_baseDigit ℓ]
  rw [map_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [map_mul, map_pow, coe_eval₂RingHom]
  congr 2
  exact evalInt_hPoly y

/-! ### 3. Coefficient and `ℓ₁`-norm bounds (Lemma B.1) -/

private theorem sum_range_choose_add (m k : ℕ) :
    ∑ j ∈ range (k + 1), Nat.choose (m + j) j = Nat.choose (m + k + 1) k := by
  induction k with
  | zero =>
    change ∑ j ∈ range 1, Nat.choose (m + j) j = Nat.choose (m + 0 + 1) 0
    simp only [range_one, sum_singleton, add_zero, Nat.choose_zero_right]
  | succ k ih =>
    rw [sum_range_succ, ih]
    have hpas : Nat.choose (m + k + 1 + 1) (k + 1) =
        Nat.choose (m + k + 1) k + Nat.choose (m + k + 1) (k + 1) :=
      Nat.choose_succ_succ (m + k + 1) k
    have hm1 : m + (k + 1) = m + k + 1 := by omega
    rw [hm1, ← hpas]

/-- The `ℓ₁` norm of `parityKernel ℓ` is at most `2 ^ (2 * ℓ)`. -/
theorem coeffNorm1_parityKernel_le (ℓ : ℕ) :
    coeffNorm1 (parityKernel ℓ) ≤ 2 ^ (2 * ℓ) := by
  have hsum : ∀ K, coeffNorm1 (paritySeriesAux (ℓ - 1) K) ≤
      ∑ j ∈ range K, Nat.choose (ℓ - 1 + j) j := by
    intro K
    induction K with
    | zero =>
      simp only [paritySeriesAux, range_zero, sum_empty, coeffNorm1_zero, le_refl]
    | succ K ih =>
      rw [paritySeriesAux, sum_range_succ, ← paritySeriesAux, sum_range_succ]
      refine (coeffNorm1_add_le _ _).trans (add_le_add ih ?_)
      have hterm : ((Nat.choose (ℓ - 1 + K) K : ℤ[X]) * X ^ K) =
          C (Nat.choose (ℓ - 1 + K) K : ℤ) * X ^ K := by simp only [eq_intCast, Int.cast_natCast]
      rw [hterm]
      refine (coeffNorm1_mul_X_pow_le _ _).trans ?_
      rw [coeffNorm1_C, Int.natAbs_natCast]
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
  · exact (hsum 0).trans (by simp only [range_zero, sum_empty, zero_le])
  · obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
    refine (hsum (k + 1)).trans ?_
    simp only [add_tsub_cancel_right]
    rw [sum_range_choose_add k k]
    exact (Nat.choose_le_two_pow (k + k + 1) k).trans
      (Nat.pow_le_pow_right (by omega) (by omega))

/-- **Lemma B.1 (`ℓ₁`-norm of `p_ℓ`)**: `‖p_ℓ‖₁ ≤ 2 ^ (3 * ℓ)`. -/
theorem coeffNorm1_parityAmplifier_le (ℓ : ℕ) :
    coeffNorm1 (parityAmplifier ℓ) ≤ 2 ^ (3 * ℓ) := by
  rw [parityAmplifier]
  calc
    coeffNorm1 ((1 - X) ^ ℓ * parityKernel ℓ)
      ≤ 2 ^ ℓ * coeffNorm1 (parityKernel ℓ) := coeffNorm1_one_sub_X_pow_mul_le ℓ _
    _ ≤ 2 ^ ℓ * 2 ^ (2 * ℓ) := Nat.mul_le_mul_left (2 ^ ℓ) (coeffNorm1_parityKernel_le ℓ)
    _ = 2 ^ (3 * ℓ) := by
      rw [← pow_add]
      congr 1
      omega

/-- Recurrence for the coefficients of the quotient `p /ₘ hPoly`. -/
theorem coeff_divByMonic_hPoly_rec (p : ℤ[X]) (n : ℕ) :
    (p /ₘ hPoly).coeff n = p.coeff (n + 2) + (p /ₘ hPoly).coeff (n + 1) := by
  have h := congr_arg (fun q : ℤ[X] => q.coeff (n + 2)) (modByMonic_add_div p hPoly)
  rw [coeff_add] at h
  have hmod : (p %ₘ hPoly).coeff (n + 2) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    have := natDegree_modByMonic_hPoly_le p
    omega
  have hmul : (hPoly * (p /ₘ hPoly)).coeff (n + 2) =
      (p /ₘ hPoly).coeff n - (p /ₘ hPoly).coeff (n + 1) := by
    have hEq : hPoly * (p /ₘ hPoly) = (p /ₘ hPoly) * X ^ 2 - (p /ₘ hPoly) * X := by
      rw [hPoly]
      ring
    rw [hEq, coeff_sub, coeff_mul_X_pow, coeff_mul_X]
  linarith

/-- Telescoping sum formula for the coefficients of `p /ₘ hPoly`. -/
theorem coeff_divByMonic_hPoly_sum (p : ℤ[X]) (n m : ℕ) :
    (p /ₘ hPoly).coeff n =
      (∑ t ∈ range m, p.coeff (n + 2 + t)) + (p /ₘ hPoly).coeff (n + m) := by
  induction m with
  | zero => simp only [range_zero, sum_empty, add_zero, zero_add]
  | succ m ih =>
    rw [sum_range_succ, ih, coeff_divByMonic_hPoly_rec p (n + m)]
    have hidx : n + m + 2 = n + 2 + m := by omega
    have hidx2 : n + (m + 1) = n + m + 1 := by omega
    rw [hidx, hidx2]
    ring

/-- The constant coefficient of `p %ₘ hPoly` equals `p.coeff 0`. -/
theorem coeff_modByMonic_hPoly_zero (p : ℤ[X]) :
    (p %ₘ hPoly).coeff 0 = p.coeff 0 := by
  have h := congr_arg (fun q : ℤ[X] => q.coeff 0) (modByMonic_add_div p hPoly)
  rw [coeff_add] at h
  have hmul : (hPoly * (p /ₘ hPoly)).coeff 0 = 0 := by
    have hEq : hPoly * (p /ₘ hPoly) = (p /ₘ hPoly) * X * X - (p /ₘ hPoly) * X := by
      rw [hPoly]
      ring
    rw [hEq, coeff_sub, coeff_mul_X_zero, coeff_mul_X_zero, sub_self]
  linarith

/-- The linear coefficient of `p %ₘ hPoly` equals `p.coeff 1 + (p /ₘ hPoly).coeff 0`. -/
theorem coeff_modByMonic_hPoly_one (p : ℤ[X]) :
    (p %ₘ hPoly).coeff 1 = p.coeff 1 + (p /ₘ hPoly).coeff 0 := by
  have h := congr_arg (fun q : ℤ[X] => q.coeff 1) (modByMonic_add_div p hPoly)
  rw [coeff_add] at h
  have hmul : (hPoly * (p /ₘ hPoly)).coeff 1 = -(p /ₘ hPoly).coeff 0 := by
    have hEq : hPoly * (p /ₘ hPoly) = (p /ₘ hPoly) * X ^ 2 - (p /ₘ hPoly) * X := by
      rw [hPoly]
      ring
    rw [hEq, coeff_sub, coeff_mul_X]
    have hsq : ((p /ₘ hPoly) * X ^ 2).coeff 1 = 0 := by
      rw [mul_comm, coeff_X_pow_mul']
      simp only [Nat.not_le_of_gt (by decide : 1 < 2), ↓reduceIte]
    rw [hsq, zero_sub]
  linarith

/-- Every coefficient of `p /ₘ hPoly` has absolute value at most `coeffNorm1 p`. -/
theorem natAbs_coeff_divByMonic_hPoly_le (p : ℤ[X]) (n : ℕ) :
    ((p /ₘ hPoly).coeff n).natAbs ≤ coeffNorm1 p := by
  rw [coeff_divByMonic_hPoly_sum p n (p.natDegree + 1)]
  have htail : (p /ₘ hPoly).coeff (n + (p.natDegree + 1)) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [natDegree_divByMonic p monic_hPoly, natDegree_hPoly]
    omega
  rw [htail, add_zero]
  refine (Int.natAbs_sum_le _ _).trans ?_
  let emb : ℕ ↪ ℕ := ⟨fun t => n + 2 + t, add_right_injective (n + 2)⟩
  have hmap : ∑ t ∈ range (p.natDegree + 1), (p.coeff (n + 2 + t)).natAbs =
      ∑ i ∈ (range (p.natDegree + 1)).map emb, (p.coeff i).natAbs := by
    rw [sum_map]
    rfl
  rw [hmap]
  exact sum_natAbs_coeff_le_coeffNorm1 p _

/-- Every coefficient of `p %ₘ hPoly` has absolute value at most `coeffNorm1 p`. -/
theorem natAbs_coeff_modByMonic_hPoly_le (p : ℤ[X]) (k : ℕ) :
    ((p %ₘ hPoly).coeff k).natAbs ≤ coeffNorm1 p := by
  rcases k with _ | _ | k
  · rw [coeff_modByMonic_hPoly_zero]
    exact natAbs_coeff_le_coeffNorm1 p 0
  · rw [coeff_modByMonic_hPoly_one, coeff_divByMonic_hPoly_sum p 0 (p.natDegree + 1)]
    have htail : (p /ₘ hPoly).coeff (0 + (p.natDegree + 1)) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [natDegree_divByMonic p monic_hPoly, natDegree_hPoly]
      omega
    rw [htail, add_zero]
    have hsum : p.coeff 1 + ∑ t ∈ range (p.natDegree + 1), p.coeff (0 + 2 + t) =
        ∑ t ∈ range (p.natDegree + 2), p.coeff (1 + t) := by
      rw [sum_range_succ' (fun t => p.coeff (1 + t)) (p.natDegree + 1), add_zero, add_comm]
      congr 1
      refine sum_congr rfl fun t _ => ?_
      congr 1
      omega
    rw [hsum]
    refine (Int.natAbs_sum_le _ _).trans ?_
    let emb : ℕ ↪ ℕ := ⟨fun t => 1 + t, add_right_injective 1⟩
    have hmap : ∑ t ∈ range (p.natDegree + 2), (p.coeff (1 + t)).natAbs =
        ∑ i ∈ (range (p.natDegree + 2)).map emb, (p.coeff i).natAbs := by
      rw [sum_map]
      rfl
    rw [hmap]
    exact sum_natAbs_coeff_le_coeffNorm1 p _
  · have h0 : (p %ₘ hPoly).coeff (k + 2) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have := natDegree_modByMonic_hPoly_le p
      omega
    rw [h0, Int.natAbs_zero]
    exact Nat.zero_le _

/-- The `ℓ₁` norm of `p %ₘ hPoly` is at most `2 * coeffNorm1 p`. -/
theorem coeffNorm1_modByMonic_hPoly_le (p : ℤ[X]) :
    coeffNorm1 (p %ₘ hPoly) ≤ 2 * coeffNorm1 p := by
  have hsub : (p %ₘ hPoly).support ⊆ range 2 := by
    intro i hi
    rw [mem_support_iff] at hi
    rw [mem_range]
    by_contra hge
    apply hi
    apply coeff_eq_zero_of_natDegree_lt
    have := natDegree_modByMonic_hPoly_le p
    omega
  calc
    coeffNorm1 (p %ₘ hPoly) ≤ ∑ i ∈ range 2, ((p %ₘ hPoly).coeff i).natAbs :=
      sum_le_sum_of_subset hsub
    _ ≤ ∑ _i ∈ range 2, coeffNorm1 p :=
      sum_le_sum fun i _ => natAbs_coeff_modByMonic_hPoly_le p i
    _ = 2 * coeffNorm1 p := by
      rw [sum_const, card_range, smul_eq_mul]

/-- The `ℓ₁` norm of `p /ₘ hPoly` is at most `p.natDegree * coeffNorm1 p`. -/
theorem coeffNorm1_divByMonic_hPoly_le (p : ℤ[X]) :
    coeffNorm1 (p /ₘ hPoly) ≤ p.natDegree * coeffNorm1 p := by
  by_cases hdiv : p /ₘ hPoly = 0
  · rw [hdiv, coeffNorm1_zero]
    exact Nat.zero_le _
  · have hdeg : 2 ≤ p.natDegree := by
      by_contra hlt
      apply hdiv
      rw [divByMonic_eq_zero_iff monic_hPoly]
      by_cases hp0 : p = 0
      · subst hp0
        rw [degree_zero, degree_eq_natDegree monic_hPoly.ne_zero]
        exact WithBot.bot_lt_coe _
      · rw [degree_eq_natDegree hp0, degree_eq_natDegree monic_hPoly.ne_zero, Nat.cast_lt,
          natDegree_hPoly]
        omega
    have hsub : (p /ₘ hPoly).support ⊆ range p.natDegree := by
      intro i hi
      rw [mem_support_iff] at hi
      rw [mem_range]
      by_contra hge
      apply hi
      apply coeff_eq_zero_of_natDegree_lt
      rw [natDegree_divByMonic p monic_hPoly, natDegree_hPoly]
      omega
    calc
      coeffNorm1 (p /ₘ hPoly) ≤ ∑ i ∈ range p.natDegree, ((p /ₘ hPoly).coeff i).natAbs :=
        sum_le_sum_of_subset hsub
      _ ≤ ∑ _i ∈ range p.natDegree, coeffNorm1 p :=
        sum_le_sum fun i _ => natAbs_coeff_divByMonic_hPoly_le p i
      _ = p.natDegree * coeffNorm1 p := by
        rw [sum_const, card_range, smul_eq_mul]

/-- After `j` monic divisions by `hPoly`, `coeffNorm1 (iterDivByH p j)` is at most
`p.natDegree ^ j * coeffNorm1 p`. -/
theorem coeffNorm1_iterDivByH_le (p : ℤ[X]) (j : ℕ) :
    coeffNorm1 (iterDivByH p j) ≤ p.natDegree ^ j * coeffNorm1 p := by
  induction j with
  | zero => simp only [iterDivByH, pow_zero, one_mul, le_refl]
  | succ j ih =>
    rw [iterDivByH]
    calc
      coeffNorm1 (iterDivByH p j /ₘ hPoly)
        ≤ (iterDivByH p j).natDegree * coeffNorm1 (iterDivByH p j) :=
          coeffNorm1_divByMonic_hPoly_le _
      _ ≤ p.natDegree * (p.natDegree ^ j * coeffNorm1 p) := by
          refine Nat.mul_le_mul ?_ ih
          rw [natDegree_iterDivByH]
          omega
      _ = p.natDegree ^ (j + 1) * coeffNorm1 p := by
          rw [pow_succ']
          ring

/-- **Lemma B.1 (coefficient bound for `e_j`)**: every coefficient of `parityBaseDigit ℓ j` has
absolute value at most `(2 * ℓ) ^ j * 2 ^ (3 * ℓ)`. -/
theorem natAbs_coeff_parityBaseDigit_le (ℓ j k : ℕ) :
    ((parityBaseDigit ℓ j).coeff k).natAbs ≤ (2 * ℓ) ^ j * 2 ^ (3 * ℓ) := by
  rw [parityBaseDigit, baseDigitByH]
  calc
    ((iterDivByH (parityAmplifier ℓ) j %ₘ hPoly).coeff k).natAbs
      ≤ coeffNorm1 (iterDivByH (parityAmplifier ℓ) j) :=
        natAbs_coeff_modByMonic_hPoly_le _ k
    _ ≤ (parityAmplifier ℓ).natDegree ^ j * coeffNorm1 (parityAmplifier ℓ) :=
        coeffNorm1_iterDivByH_le _ j
    _ ≤ (2 * ℓ) ^ j * 2 ^ (3 * ℓ) := by
        refine Nat.mul_le_mul (Nat.pow_le_pow_left ?_ j) (coeffNorm1_parityAmplifier_le ℓ)
        have := natDegree_parityAmplifier_le ℓ
        omega

/-- **Lemma B.1 (`ℓ₁`-norm bound for `e_j`)**: `‖parityBaseDigit ℓ j‖₁` is at most
`2 * ((2 * ℓ) ^ j * 2 ^ (3 * ℓ))`. -/
theorem coeffNorm1_parityBaseDigit_le (ℓ j : ℕ) :
    coeffNorm1 (parityBaseDigit ℓ j) ≤ 2 * ((2 * ℓ) ^ j * 2 ^ (3 * ℓ)) := by
  rw [parityBaseDigit, baseDigitByH]
  calc
    coeffNorm1 (iterDivByH (parityAmplifier ℓ) j %ₘ hPoly)
      ≤ 2 * coeffNorm1 (iterDivByH (parityAmplifier ℓ) j) :=
        coeffNorm1_modByMonic_hPoly_le _
    _ ≤ 2 * ((parityAmplifier ℓ).natDegree ^ j * coeffNorm1 (parityAmplifier ℓ)) :=
        Nat.mul_le_mul_left 2 (coeffNorm1_iterDivByH_le _ j)
    _ ≤ 2 * ((2 * ℓ) ^ j * 2 ^ (3 * ℓ)) := by
        refine Nat.mul_le_mul_left 2
          (Nat.mul_le_mul (Nat.pow_le_pow_left ?_ j) (coeffNorm1_parityAmplifier_le ℓ))
        have := natDegree_parityAmplifier_le ℓ
        omega

/-! ### 4. Shared-total-order truncation and multivariate total-degree bound (Lemma 5.2) -/

/-- The `V`-series factor `B(y; V) = ∑ j ∈ range ℓ, e_j(y) h(y)^j V^j` in `A[X]`, where the
polynomial indeterminate `X` represents the shared formal truncation marker `V`. -/
def parityFactor {A : Type*} [CommRing A] (ℓ : ℕ) (y : A) : A[X] :=
  ∑ j ∈ range ℓ, C (evalInt y (parityBaseDigit ℓ j) * evalInt y hPoly ^ j) * X ^ j

/-- The linear map `S_ℓ(∑_s b_s V^s) = ∑ s ∈ range ℓ, b_s` summing the coefficients of
`V ^ 0, …, V ^ (ℓ - 1)`. -/
def sumCoeffsBelow {A : Type*} [Semiring A] (ℓ : ℕ) (P : A[X]) : A :=
  ∑ s ∈ range ℓ, P.coeff s

/-- The `s`-th coefficient of `parityFactor ℓ y` is `e_s(y) h(y)^s` for `s < ℓ` and `0`
otherwise. -/
theorem coeff_parityFactor {A : Type*} [CommRing A] (ℓ : ℕ) (y : A) (s : ℕ) :
    (parityFactor ℓ y).coeff s =
      if s < ℓ then evalInt y (parityBaseDigit ℓ s) * evalInt y hPoly ^ s else 0 := by
  rw [parityFactor, finsetSum_coeff]
  simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  by_cases hs : s < ℓ
  · rw [ite_eq_left hs, sum_eq_single s]
    · simp only [↓reduceIte]
    · intro j _ hjs
      exact ite_eq_right (Ne.symm hjs)
    · intro hns
      exact absurd (mem_range.mpr hs) hns
  · rw [ite_eq_right hs]
    refine sum_eq_zero fun j hj => ?_
    rw [mem_range] at hj
    exact ite_eq_right (by omega)

/-- Evaluating `parityFactor ℓ y` at `V = 1` recovers `p_ℓ(y)`. -/
theorem eval_one_parityFactor {A : Type*} [CommRing A] (ℓ : ℕ) (y : A) :
    (parityFactor ℓ y).eval 1 = evalInt y (parityAmplifier ℓ) := by
  rw [parityFactor, ← coe_evalRingHom, map_sum, evalInt_parityAmplifier_eq_sum]
  refine sum_congr rfl fun j _ => ?_
  simp only [coe_evalRingHom, eval_mul, eval_C, eval_pow, eval_X, one_pow, mul_one, evalInt_hPoly]

/-- At an integer `y`, the `s`-th coefficient of `parityFactor ℓ y` is divisible by `2 ^ s`. -/
theorem two_pow_dvd_coeff_parityFactor (ℓ : ℕ) (y : ℤ) (s : ℕ) :
    (2 : ℤ) ^ s ∣ (parityFactor ℓ y).coeff s := by
  rw [coeff_parityFactor]
  split_ifs with hs
  · rw [evalInt_int y hPoly]
    exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd (two_dvd_eval_hPoly y) s) _
  · exact dvd_zero _

/-- Graded divisibility `2 ^ s ∣ coeff s` is preserved under polynomial multiplication. -/
theorem two_pow_dvd_coeff_mul {P Q : ℤ[X]}
    (hP : ∀ s, (2 : ℤ) ^ s ∣ P.coeff s) (hQ : ∀ s, (2 : ℤ) ^ s ∣ Q.coeff s) (s : ℕ) :
    (2 : ℤ) ^ s ∣ (P * Q).coeff s := by
  rw [coeff_mul]
  refine dvd_sum fun ij hij => ?_
  rw [mem_antidiagonal] at hij
  rw [← hij, pow_add]
  exact mul_dvd_mul (hP ij.1) (hQ ij.2)

/-- Every `V ^ s`-coefficient of `∏ i ∈ I, parityFactor ℓ (y i)` at integer arguments `y i` is
divisible by `2 ^ s`. -/
theorem two_pow_dvd_coeff_prod_parityFactor {ι : Type*} (I : Finset ι) (ℓ : ℕ) (y : ι → ℤ)
    (s : ℕ) :
    (2 : ℤ) ^ s ∣ (∏ i ∈ I, parityFactor ℓ (y i)).coeff s := by
  classical
  induction I using Finset.induction_on generalizing s with
  | empty =>
    rw [prod_empty]
    rcases s with _ | s
    · simp only [pow_zero, coeff_one_zero, dvd_refl]
    · rw [coeff_one, ite_eq_right (Nat.succ_ne_zero s)]
      exact dvd_zero _
  | insert a I ha ih =>
    rw [prod_insert ha]
    exact two_pow_dvd_coeff_mul (two_pow_dvd_coeff_parityFactor ℓ (y a)) ih s

/-- If `2 ^ s ∣ P.coeff s` for all `s`, then `sumCoeffsBelow ℓ P ≡ P.eval 1 (mod 2 ^ ℓ)`. -/
theorem sumCoeffsBelow_modEq_eval_one {P : ℤ[X]} {ℓ : ℕ}
    (hP : ∀ s, (2 : ℤ) ^ s ∣ P.coeff s) :
    sumCoeffsBelow ℓ P ≡ P.eval 1 [ZMOD (2 : ℤ) ^ ℓ] := by
  have heval : P.eval 1 = ∑ s ∈ range (max ℓ (P.natDegree + 1)), P.coeff s := by
    rw [eval_eq_sum_range' (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right ℓ _))]
    simp only [one_pow, mul_one]
  have hsplit :
      ∑ s ∈ range (max ℓ (P.natDegree + 1)), P.coeff s =
        sumCoeffsBelow ℓ P + ∑ s ∈ Ico ℓ (max ℓ (P.natDegree + 1)), P.coeff s := by
    rw [sumCoeffsBelow, sum_range_add_sum_Ico _ (le_max_left ℓ _)]
  rw [heval, hsplit, Int.modEq_iff_dvd, add_sub_cancel_left]
  refine dvd_sum fun s hs => ?_
  rw [mem_Ico] at hs
  exact (pow_dvd_pow (2 : ℤ) hs.1).trans (hP s)

/-- **Lemma 5.2 (shared-`V` truncation congruence)**: for `ℓ ≥ 1` and integers `y i`,
`S_ℓ(∏ i ∈ I, B_i(V)) ≡ ∏ i ∈ I, (if Even (y i) then 1 else 0) (mod 2 ^ ℓ)`. -/
theorem sumCoeffsBelow_prod_parityFactor_modEq {ι : Type*} (I : Finset ι) {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (y : ι → ℤ) [∀ i, Decidable (Even (y i))] :
    sumCoeffsBelow ℓ (∏ i ∈ I, parityFactor ℓ (y i)) ≡
      (∏ i ∈ I, if Even (y i) then (1 : ℤ) else 0) [ZMOD (2 : ℤ) ^ ℓ] := by
  refine (sumCoeffsBelow_modEq_eval_one (two_pow_dvd_coeff_prod_parityFactor I ℓ y)).trans ?_
  rw [eval_prod]
  have heval : (∏ i ∈ I, (parityFactor ℓ (y i)).eval 1) =
      ∏ i ∈ I, (parityAmplifier ℓ).eval (y i) := by
    refine prod_congr rfl fun i _ => ?_
    rw [eval_one_parityFactor, evalInt_int]
  rw [heval]
  exact Int.ModEq.prod fun i _ => parityAmplifier_eval_modEq_two_pow hℓ (y i)

/-- Evaluating an affine integer polynomial (`natDegree ≤ 1`) at `y : MvPolynomial σ R` preserves
any upper bound `d` on `y.totalDegree`. -/
theorem totalDegree_evalInt_of_natDegree_le_one {σ R : Type*} [CommRing R] {q : ℤ[X]}
    (hq : q.natDegree ≤ 1) {y : MvPolynomial σ R} {d : ℕ} (hy : y.totalDegree ≤ d) :
    (evalInt y q).totalDegree ≤ d := by
  rw [evalInt, eq_X_add_C_of_natDegree_le_one hq, eval₂_add, eval₂_mul, eval₂_X, eval₂_C, eval₂_C]
  have hcast : ∀ a : ℤ, (Int.castRingHom (MvPolynomial σ R) a) = a • (1 : MvPolynomial σ R) := by
    intro a
    simp only [eq_intCast, zsmul_one]
  rw [hcast, hcast, smul_mul_assoc, one_mul]
  refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
  · exact (MvPolynomial.totalDegree_smul_le _ _).trans hy
  · exact (MvPolynomial.totalDegree_smul_le _ _).trans
      (by simp only [MvPolynomial.totalDegree_one, zero_le])

/-- Evaluating `hPoly = X ^ 2 - X` at `y : MvPolynomial σ R` of total degree at most `d` gives
a polynomial of total degree at most `2 * d`. -/
theorem totalDegree_evalInt_hPoly_le {σ R : Type*} [CommRing R] {y : MvPolynomial σ R} {d : ℕ}
    (hy : y.totalDegree ≤ d) :
    (evalInt y hPoly).totalDegree ≤ 2 * d := by
  rw [evalInt_hPoly]
  refine (MvPolynomial.totalDegree_sub (y ^ 2) y).trans (max_le ?_ (hy.trans (by omega)))
  exact (MvPolynomial.totalDegree_pow y 2).trans (Nat.mul_le_mul_left 2 hy)

/-- For `y : MvPolynomial σ R` of total degree at most `d`, the `V ^ s`-coefficient of
`parityFactor ℓ y` has total degree at most `d + 2 * d * s`. -/
theorem totalDegree_coeff_parityFactor_le {σ R : Type*} [CommRing R] (ℓ : ℕ)
    {y : MvPolynomial σ R} {d : ℕ} (hy : y.totalDegree ≤ d) (s : ℕ) :
    ((parityFactor ℓ y).coeff s).totalDegree ≤ d + 2 * d * s := by
  rw [coeff_parityFactor]
  split_ifs with hs
  · refine (MvPolynomial.totalDegree_mul _ _).trans (add_le_add ?_ ?_)
    · exact totalDegree_evalInt_of_natDegree_le_one (natDegree_parityBaseDigit_le ℓ s) hy
    · refine (MvPolynomial.totalDegree_pow _ s).trans ?_
      have h1 := Nat.mul_le_mul_left s (totalDegree_evalInt_hPoly_le hy)
      have h2 : s * (2 * d) = 2 * d * s := by ring
      omega
  · simp only [MvPolynomial.totalDegree_zero, zero_le]

/-- Graded total-degree bounds `totalDegree (coeff s) ≤ M + 2 * d * s` add in the offset `M`
under multiplication in `(MvPolynomial σ R)[X]`. -/
theorem totalDegree_coeff_mul_le {σ R : Type*} [CommRing R] {P Q : (MvPolynomial σ R)[X]}
    {M₁ M₂ d : ℕ}
    (hP : ∀ s, (P.coeff s).totalDegree ≤ M₁ + 2 * d * s)
    (hQ : ∀ s, (Q.coeff s).totalDegree ≤ M₂ + 2 * d * s) (s : ℕ) :
    ((P * Q).coeff s).totalDegree ≤ (M₁ + M₂) + 2 * d * s := by
  rw [coeff_mul]
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun ij hij => ?_)
  rw [mem_antidiagonal] at hij
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  have h1 := hP ij.1
  have h2 := hQ ij.2
  have hsum : 2 * d * ij.1 + 2 * d * ij.2 = 2 * d * s := by
    rw [← hij]
    ring
  linarith

/-- **Lemma 5.2 (graded total-degree bound)**: if every `y i` (`i ∈ I`) has multivariate total
degree at most `d`, then the `V ^ s`-coefficient of `∏ i ∈ I, parityFactor ℓ (y i)` has total
degree at most `d * (#I + 2 * s)`. -/
theorem totalDegree_coeff_prod_parityFactor_le {ι σ R : Type*} [CommRing R] (I : Finset ι)
    (ℓ : ℕ) {y : ι → MvPolynomial σ R} {d : ℕ} (hy : ∀ i ∈ I, (y i).totalDegree ≤ d) (s : ℕ) :
    ((∏ i ∈ I, parityFactor ℓ (y i)).coeff s).totalDegree ≤ d * (#I + 2 * s) := by
  classical
  induction I using Finset.induction_on generalizing s with
  | empty =>
    rw [prod_empty, card_empty, zero_add]
    rcases s with _ | s
    · simp only [coeff_one_zero, MvPolynomial.totalDegree_one, zero_le]
    · rw [coeff_one, ite_eq_right (Nat.succ_ne_zero s), MvPolynomial.totalDegree_zero]
      exact Nat.zero_le _
  | insert a I ha ih =>
    rw [prod_insert ha, card_insert_of_notMem ha]
    have hstep := totalDegree_coeff_mul_le (M₁ := d) (M₂ := d * #I) (d := d)
      (totalDegree_coeff_parityFactor_le ℓ (hy a (mem_insert_self a I)))
      (fun k => (ih (fun i hi => hy i (mem_insert_of_mem hi)) k).trans
        (le_of_eq (by ring)))
      s
    exact hstep.trans (le_of_eq (by ring))

/-- **Lemma 5.2 (retained coefficient total-degree bound)**: for `s < ℓ`, the `V ^ s`-coefficient
of `∏ i ∈ I, parityFactor ℓ (y i)` has total degree at most `d * (#I + 2 * (ℓ - 1))`. -/
theorem totalDegree_coeff_prod_parityFactor_le_of_lt {ι σ R : Type*} [CommRing R] (I : Finset ι)
    {ℓ s : ℕ} (hs : s < ℓ) {y : ι → MvPolynomial σ R} {d : ℕ}
    (hy : ∀ i ∈ I, (y i).totalDegree ≤ d) :
    ((∏ i ∈ I, parityFactor ℓ (y i)).coeff s).totalDegree ≤ d * (#I + 2 * (ℓ - 1)) := by
  refine (totalDegree_coeff_prod_parityFactor_le I ℓ hy s).trans ?_
  refine Nat.mul_le_mul_left d ?_
  omega

/-- **Lemma 5.2 (truncated sum total-degree bound)**: the truncated coefficient sum
`sumCoeffsBelow ℓ (∏ i ∈ I, parityFactor ℓ (y i))` has total degree at most
`d * (#I + 2 * (ℓ - 1))`. -/
theorem totalDegree_sumCoeffsBelow_prod_parityFactor_le {ι σ R : Type*} [CommRing R]
    (I : Finset ι) (ℓ : ℕ) {y : ι → MvPolynomial σ R} {d : ℕ}
    (hy : ∀ i ∈ I, (y i).totalDegree ≤ d) :
    (sumCoeffsBelow ℓ (∏ i ∈ I, parityFactor ℓ (y i))).totalDegree ≤
      d * (#I + 2 * (ℓ - 1)) := by
  rw [sumCoeffsBelow]
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun s hs => ?_)
  rw [mem_range] at hs
  exact totalDegree_coeff_prod_parityFactor_le_of_lt I hs hy

end Polynomial
