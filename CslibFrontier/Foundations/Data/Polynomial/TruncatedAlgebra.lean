/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib / Cslib, general truncated polynomial algebra `R[T]/(T^r)`)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.Polynomial.CoeffList
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Tactic.Ring

/-!
# General truncated polynomial algebra `R[T] / (T ^ r)`

Defines the truncated polynomial algebra
`Polynomial.Truncated R r := R[X] ⧸ Ideal.span {(X : R[X]) ^ r}` over an arbitrary commutative
ring `R` and truncation order `r : ℕ`, together with coefficient extraction, canonical truncated
representatives, explicit sum/product formulas, geometric unit inversion, and substitution.

## Main definitions

* `Polynomial.Truncated`: quotient algebra `R[X] ⧸ Ideal.span {(X : R[X]) ^ r}`.
* `Polynomial.Truncated.mk`, `Polynomial.Truncated.var`: quotient map `R[X] →ₐ[R] Truncated R r`
  and distinguished nilpotent indeterminate `T`.
* `Polynomial.Truncated.coeff`, `Polynomial.Truncated.toPoly`: coefficient extraction below `r`
  and canonical degree `< r` polynomial representative.
* `Polynomial.Truncated.geomInv`, `Polynomial.Truncated.unitInv`: finite geometric series inverse
  of `1 - y` when `coeff 0 y = 0` and general inverse when `coeff 0 x` is a unit.
* `Polynomial.Truncated.liftAlgHom`, `Polynomial.Truncated.subst`,
  `Polynomial.Truncated.substZeroConst`: algebraic substitution for nilpotent images `g ^ r = 0`
  (in particular whenever `coeff 0 g = 0`).
* `Polynomial.Truncated.proj`, `Polynomial.Truncated.map`,
  `Polynomial.Truncated.equivAdjoinRoot`: truncation-order projection, base-change functoriality,
  and equivalence with `AdjoinRoot ((X : R[X]) ^ r)`.

## Main results

* `Polynomial.Truncated.ext`, `Polynomial.Truncated.mk_eq_mk_iff`: equality in `Truncated R r` is
  agreement of coefficients below `r`.
* `Polynomial.Truncated.coeff_mul`, `Polynomial.Truncated.coeff_sum`,
  `Polynomial.Truncated.mk_trunc_mul_trunc`: exact truncated sum and Cauchy-product identities.
* `Polynomial.Truncated.isUnit_iff`, `Polynomial.Truncated.one_sub_mul_geomInv`: unit
  characterization via constant coefficients and geometric inverse verification.
* `Polynomial.Truncated.subst_comp`, `Polynomial.Truncated.coeff_subst_of_coeff_zero`,
  `Polynomial.Truncated.mk_comp_eq_subst`, `Polynomial.Truncated.mk_trunc_subst_eq_subst`:
  substitution composition law, finite coefficient formula, and agreement with `Polynomial.comp`
  and `PowerSeries.subst` modulo `T ^ r`.
-/

public section

namespace Polynomial

/-- The truncated polynomial algebra `R[T] / (T ^ r)` realized as `R[X] ⧸ Ideal.span {X ^ r}`. -/
abbrev Truncated (R : Type*) [CommRing R] (r : ℕ) : Type _ :=
  R[X] ⧸ Ideal.span {(X : R[X]) ^ r}

namespace Truncated

noncomputable section

open Finset Ideal
open scoped PowerSeries

section Basic

variable {R : Type*} [CommRing R] {r : ℕ}

/-- Canonical `R`-algebra quotient map `R[X] →ₐ[R] Truncated R r`. -/
def mk (r : ℕ) : R[X] →ₐ[R] Truncated R r :=
  Ideal.Quotient.mkₐ R (Ideal.span {(X : R[X]) ^ r})

/-- The indeterminate `T` in `Truncated R r`. -/
def var (R : Type*) [CommRing R] (r : ℕ) : Truncated R r := mk r X

theorem var_eq_mk_X (R : Type*) [CommRing R] (r : ℕ) : var R r = mk r X := by
  simp only [var]

theorem mk_apply (p : R[X]) : mk r p = Ideal.Quotient.mk (Ideal.span {(X : R[X]) ^ r}) p := by
  simp only [mk]
  rfl

@[elab_as_elim]
theorem induction_on {P : Truncated R r → Prop} (x : Truncated R r) (hp : ∀ p : R[X], P (mk r p)) :
    P x :=
  Quotient.inductionOn' x fun p => hp p

/-- Two polynomials have the same image in `Truncated R r` iff their coefficients below `r`
agree. -/
theorem mk_eq_mk_iff {p q : R[X]} : mk r p = mk r q ↔ ∀ i < r, p.coeff i = q.coeff i := by
  rw [mk_apply, mk_apply, Ideal.Quotient.eq, Ideal.mem_span_singleton, Polynomial.X_pow_dvd_iff]
  refine forall₂_congr fun i _ => ?_
  rw [Polynomial.coeff_sub, sub_eq_zero]

/-- `T ^ r = 0` in `Truncated R r`. -/
@[simp]
theorem var_pow_eq_zero : (var R r) ^ r = 0 := by
  rw [var, ← map_pow, mk_apply, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_span_singleton_self ((X : R[X]) ^ r)

/-- `mk r ((X : R[X]) ^ k) = 0` whenever `r ≤ k`. -/
theorem mk_X_pow_eq_zero_of_le {k : ℕ} (hk : r ≤ k) : mk r ((X : R[X]) ^ k) = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [pow_add, map_mul]
  change (var R r) ^ r * mk r ((X : R[X]) ^ m) = 0
  rw [var_pow_eq_zero, zero_mul]

/-- Extract the coefficient of `T ^ i` (`0` for `i ≥ r`) from an element of `Truncated R r`. -/
def coeff (i : ℕ) (x : Truncated R r) : R :=
  Quotient.liftOn' x (fun p : R[X] => if i < r then p.coeff i else 0) fun p q hpq => by
    have h : p - q ∈ Ideal.span {(X : R[X]) ^ r} := Ideal.Quotient.eq.mp (Quotient.sound hpq)
    rw [Ideal.mem_span_singleton, Polynomial.X_pow_dvd_iff] at h
    split_ifs with hi
    · rw [← sub_eq_zero, ← Polynomial.coeff_sub]
      exact h i hi
    · rfl

@[simp]
theorem coeff_mk (i : ℕ) (p : R[X]) : coeff i (mk r p) = if i < r then p.coeff i else 0 := by
  rw [coeff, mk_apply]
  rfl

theorem coeff_mk_of_lt {i : ℕ} (hi : i < r) (p : R[X]) : coeff i (mk r p) = p.coeff i := by
  simp only [coeff_mk, hi, ↓reduceIte]

theorem coeff_eq_zero_of_le {i : ℕ} (hi : r ≤ i) (x : Truncated R r) : coeff i x = 0 := by
  induction x using induction_on with
  | hp p => simp only [coeff_mk, not_lt_of_ge hi, ↓reduceIte]

@[ext]
theorem ext {x y : Truncated R r} (h : ∀ i < r, coeff i x = coeff i y) : x = y := by
  induction x using induction_on with
  | hp p =>
    induction y using induction_on with
    | hp q =>
      rw [mk_eq_mk_iff]
      intro i hi
      simpa only [coeff_mk, hi, ↓reduceIte] using h i hi

@[simp]
theorem coeff_zero (i : ℕ) : coeff i (0 : Truncated R r) = 0 := by
  rw [← map_zero (mk r), coeff_mk]
  split_ifs <;> simp

@[simp]
theorem coeff_one (i : ℕ) : coeff i (1 : Truncated R r) = if i = 0 ∧ 0 < r then 1 else 0 := by
  rw [← map_one (mk r), coeff_mk, Polynomial.coeff_one]
  by_cases hi0 : i = 0
  · subst hi0; simp
  · simp [hi0]

theorem coeff_C (a : R) (i : ℕ) :
    coeff i (mk r (C a)) = if i = 0 ∧ 0 < r then a else 0 := by
  rw [coeff_mk, Polynomial.coeff_C]
  by_cases hi0 : i = 0
  · subst hi0; simp
  · simp [hi0]

@[simp]
theorem coeff_algebraMap (a : R) (i : ℕ) :
    coeff i (algebraMap R (Truncated R r) a) = if i = 0 ∧ 0 < r then a else 0 := by
  rw [← AlgHom.commutes (mk r) a, Polynomial.algebraMap_eq, coeff_C]

@[simp]
theorem coeff_var (i : ℕ) : coeff i (var R r) = if i = 1 ∧ 1 < r then 1 else 0 := by
  rw [var, coeff_mk, Polynomial.coeff_X]
  by_cases hi : i = 1
  · subst hi; simp
  · by_cases hir : i < r <;> simp [hi, hir, eq_comm]

@[simp]
theorem coeff_var_pow (k i : ℕ) :
    coeff i ((var R r) ^ k) = if i = k ∧ k < r then 1 else 0 := by
  rw [var, ← map_pow, coeff_mk, Polynomial.coeff_X_pow]
  by_cases hik : i = k
  · subst hik; simp
  · by_cases hir : i < r <;> simp [hik, hir]

@[simp]
theorem coeff_add (i : ℕ) (x y : Truncated R r) :
    coeff i (x + y) = coeff i x + coeff i y := by
  induction x using induction_on with
  | hp p =>
    induction y using induction_on with
    | hp q =>
      rw [← map_add, coeff_mk, coeff_mk, coeff_mk, Polynomial.coeff_add]
      split_ifs <;> simp

@[simp]
theorem coeff_neg (i : ℕ) (x : Truncated R r) : coeff i (-x) = -coeff i x := by
  induction x using induction_on with
  | hp p =>
    rw [← map_neg, coeff_mk, coeff_mk, Polynomial.coeff_neg]
    split_ifs <;> simp

@[simp]
theorem coeff_sub (i : ℕ) (x y : Truncated R r) :
    coeff i (x - y) = coeff i x - coeff i y := by
  rw [sub_eq_add_neg, coeff_add, coeff_neg, sub_eq_add_neg]

@[simp]
theorem coeff_smul (i : ℕ) (a : R) (x : Truncated R r) :
    coeff i (a • x) = a * coeff i x := by
  induction x using induction_on with
  | hp p =>
    rw [← map_smul, coeff_mk, coeff_mk, Polynomial.coeff_smul, smul_eq_mul]
    split_ifs <;> simp

theorem coeff_smul_algebra {S : Type*} [CommRing S] [Algebra R S] (i : ℕ) (a : R)
    (x : Truncated S r) : coeff i (a • x) = algebraMap R S a * coeff i x := by
  rw [← IsScalarTower.algebraMap_smul S a x, coeff_smul]

/-- Coefficient extraction at degree `i` as an `R`-linear map. -/
def coeffLinearMap (r i : ℕ) : Truncated R r →ₗ[R] R where
  toFun := coeff i
  map_add' := coeff_add i
  map_smul' a x := by simp

@[simp]
theorem coeffLinearMap_apply (r i : ℕ) (x : Truncated R r) :
    coeffLinearMap r i x = coeff i x := by
  simp only [coeffLinearMap, LinearMap.coe_mk, AddHom.coe_mk]

@[simp]
theorem coeff_sum {ι : Type*} (s : Finset ι) (f : ι → Truncated R r) (i : ℕ) :
    coeff i (∑ k ∈ s, f k) = ∑ k ∈ s, coeff i (f k) :=
  map_sum (coeffLinearMap r i) f s

theorem coeff_nsmul (i n : ℕ) (x : Truncated R r) :
    coeff i (n • x) = n • coeff i x :=
  map_nsmul (coeffLinearMap r i) n x

theorem coeff_zsmul (i : ℕ) (k : ℤ) (x : Truncated R r) :
    coeff i (k • x) = k • coeff i x :=
  map_zsmul (coeffLinearMap r i) k x

/-- Truncated Cauchy product formula for `coeff i (x * y)` when `i < r`. -/
theorem coeff_mul {i : ℕ} (hi : i < r) (x y : Truncated R r) :
    coeff i (x * y) = ∑ k ∈ Finset.antidiagonal i, coeff k.1 x * coeff k.2 y := by
  induction x using induction_on with
  | hp p =>
    induction y using induction_on with
    | hp q =>
      rw [← map_mul, coeff_mk_of_lt hi, Polynomial.coeff_mul]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hsum : k.1 + k.2 = i := Finset.mem_antidiagonal.mp hk
      rw [coeff_mk_of_lt (by omega), coeff_mk_of_lt (by omega)]

/-- Index-range Cauchy product formula for `coeff i (x * y)` when `i < r`. -/
theorem coeff_mul_range {i : ℕ} (hi : i < r) (x y : Truncated R r) :
    coeff i (x * y) = ∑ j ∈ Finset.range (i + 1), coeff j x * coeff (i - j) y := by
  rw [coeff_mul hi,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => coeff a x * coeff b y)]

/-- Canonical degree `< r` polynomial representative of `x : Truncated R r`. -/
@[expose] def toPoly (x : Truncated R r) : R[X] :=
  ∑ i ∈ Finset.range r, C (coeff i x) * X ^ i

theorem toPoly_def (x : Truncated R r) :
    toPoly x = ∑ i ∈ Finset.range r, C (coeff i x) * X ^ i :=
  rfl

@[simp]
theorem coeff_toPoly (x : Truncated R r) (i : ℕ) : (toPoly x).coeff i = coeff i x := by
  rw [toPoly, ← Polynomial.lcoeff_apply, map_sum]
  simp only [Polynomial.lcoeff_apply, Polynomial.coeff_C_mul_X_pow]
  by_cases hi : i < r
  · rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hbi
      simp [hbi.symm]
    · intro hnot
      exact False.elim (hnot (Finset.mem_range.mpr hi))
  · rw [coeff_eq_zero_of_le (not_lt.mp hi)]
    refine Finset.sum_eq_zero fun b hb => ?_
    have hb_lt : b < r := Finset.mem_range.mp hb
    have hne : i ≠ b := fun h => hi (h ▸ hb_lt)
    simp [hne]

@[simp]
theorem mk_toPoly (x : Truncated R r) : mk r (toPoly x) = x := by
  ext i hi
  rw [coeff_mk_of_lt hi, coeff_toPoly]

theorem toPoly_mk (p : R[X]) :
    toPoly (mk r p) = ∑ i ∈ Finset.range r, C (p.coeff i) * X ^ i := by
  ext i
  rw [coeff_toPoly, coeff_mk]
  conv_rhs => rw [← Polynomial.lcoeff_apply, map_sum]
  simp only [Polynomial.lcoeff_apply, Polynomial.coeff_C_mul_X_pow]
  by_cases hi : i < r
  · simp only [hi, ↓reduceIte]
    symm
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hbi
      simp [hbi.symm]
    · intro hnot
      exact False.elim (hnot (Finset.mem_range.mpr hi))
  · simp only [hi, ↓reduceIte]
    symm
    exact Finset.sum_eq_zero fun b hb => by
      have hne : i ≠ b := fun h => hi (h ▸ Finset.mem_range.mp hb)
      simp [hne]

theorem natDegree_toPoly_lt (hr : 0 < r) (x : Truncated R r) : (toPoly x).natDegree < r := by
  by_cases h0 : toPoly x = 0
  · rw [h0, Polynomial.natDegree_zero]
    exact hr
  · rw [Polynomial.natDegree_lt_iff_degree_lt h0, Polynomial.degree_lt_iff_coeff_zero]
    intro m hm
    rw [coeff_toPoly, coeff_eq_zero_of_le hm]

theorem toPoly_mk_eq_trunc (p : R[X]) : toPoly (mk r p) = PowerSeries.trunc r (p : R⟦X⟧) := by
  ext i
  rw [coeff_toPoly, coeff_mk, PowerSeries.coeff_trunc, Polynomial.coeff_coe]

/-- Canonical basis expansion `x = ∑ i < r, coeff i x • T ^ i`. -/
theorem sum_coeff_mul_var_pow (x : Truncated R r) :
    ∑ i ∈ Finset.range r, coeff i x • (var R r) ^ i = x := by
  conv_rhs => rw [← mk_toPoly x, toPoly]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.smul_def (coeff i x) (var R r ^ i), map_mul, map_pow, var,
    ← AlgHom.commutes (mk r) (coeff i x), Polynomial.algebraMap_eq]

/-- Canonical length-`r` coefficient list of `x : Truncated R r`. -/
@[expose] def coeffs (x : Truncated R r) : List R :=
  (toPoly x).coeffsBelow r

theorem coeffs_def (x : Truncated R r) : coeffs x = (toPoly x).coeffsBelow r :=
  rfl

@[simp]
theorem length_coeffs (x : Truncated R r) : (coeffs x).length = r := by
  rw [coeffs, Polynomial.length_coeffsBelow]

theorem ofCoeffList_coeffs (x : Truncated R r) : Polynomial.ofCoeffList (coeffs x) = toPoly x := by
  by_cases hr : r = 0
  · subst hr
    have hnil : coeffs x = [] := List.eq_nil_of_length_eq_zero (length_coeffs x)
    rw [hnil, Polynomial.ofCoeffList_nil, toPoly, Finset.range_zero, Finset.sum_empty]
  · exact Polynomial.ofCoeffList_coeffsBelow (natDegree_toPoly_lt (Nat.pos_of_ne_zero hr) x)

theorem getD_coeffs (x : Truncated R r) (i : ℕ) : (coeffs x).getD i 0 = coeff i x := by
  rw [← Polynomial.coeff_ofCoeffList, ofCoeffList_coeffs, coeff_toPoly]

/-- Truncating two power series before multiplying and projecting to `Truncated R r` equals
projecting the truncation of their power-series product. -/
theorem mk_trunc_mul_trunc (f g : R⟦X⟧) :
    mk r ((PowerSeries.trunc r f : R[X]) * (PowerSeries.trunc r g : R[X])) =
      mk r (PowerSeries.trunc r (f * g)) := by
  rw [mk_eq_mk_iff]
  intro i hi
  rw [← Polynomial.coeff_coe, Polynomial.coe_mul,
    ← PowerSeries.coeff_mul_eq_coeff_trunc_mul_trunc f g hi, PowerSeries.coeff_trunc]
  simp only [hi, ↓reduceIte]

/-- Truncating a power series before raising to a power and projecting to `Truncated R r` equals
projecting the truncation of the power. -/
theorem mk_trunc_pow (f : R⟦X⟧) (n : ℕ) :
    mk r ((PowerSeries.trunc r f : R[X]) ^ n) = mk r (PowerSeries.trunc r (f ^ n)) := by
  rw [mk_eq_mk_iff]
  intro i hi
  have h := congrArg (fun p : R[X] => p.coeff i) (PowerSeries.trunc_trunc_pow f r n)
  rw [← Polynomial.coeff_coe, Polynomial.coe_pow]
  simpa only [PowerSeries.coeff_trunc, hi, ↓reduceIte, Polynomial.coeff_coe] using h

end Basic

section UnitsAndNilpotency

variable {R : Type*} [CommRing R] {r : ℕ}

/-- Any element with vanishing constant term satisfies `y ^ r = 0`. -/
theorem pow_eq_zero_of_coeff_zero {y : Truncated R r} (hy : coeff 0 y = 0) : y ^ r = 0 := by
  rw [← mk_toPoly y, ← map_pow, mk_apply, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton]
  have hdvd : (X : R[X]) ∣ toPoly y := by
    rw [Polynomial.X_dvd_iff, coeff_toPoly, hy]
  simpa only [one_pow] using pow_dvd_pow_of_dvd hdvd r

/-- All coefficients of `y ^ d` below degree `d` vanish whenever `coeff 0 y = 0`. -/
theorem coeff_pow_eq_zero_of_lt {y : Truncated R r} (hy : coeff 0 y = 0) {d i : ℕ} (hi : i < d) :
    coeff i (y ^ d) = 0 := by
  by_cases hir : i < r
  · rw [← mk_toPoly y, ← map_pow, coeff_mk_of_lt hir]
    have hdvd : (X : R[X]) ^ d ∣ (toPoly y) ^ d :=
      pow_dvd_pow_of_dvd (Polynomial.X_dvd_iff.mpr (by simpa only [coeff_toPoly] using hy)) d
    exact (Polynomial.X_pow_dvd_iff.mp hdvd) i hi
  · exact coeff_eq_zero_of_le (not_lt.mp hir) _

/-- Finite geometric series `∑ k < r, y ^ k` inverting `1 - y` when `coeff 0 y = 0`. -/
@[expose] def geomInv (y : Truncated R r) : Truncated R r :=
  ∑ k ∈ Finset.range r, y ^ k

theorem geomInv_def (y : Truncated R r) : geomInv y = ∑ k ∈ Finset.range r, y ^ k :=
  rfl

/-- `(1 - y) * geomInv y = 1` whenever `coeff 0 y = 0`. -/
theorem one_sub_mul_geomInv {y : Truncated R r} (hy : coeff 0 y = 0) :
    (1 - y) * geomInv y = 1 := by
  rw [geomInv, mul_neg_geom_sum, pow_eq_zero_of_coeff_zero hy, sub_zero]

/-- `(1 + y) * geomInv (-y) = 1` whenever `coeff 0 y = 0`. -/
theorem one_add_mul_geomInv_neg {y : Truncated R r} (hy : coeff 0 y = 0) :
    (1 + y) * geomInv (-y) = 1 := by
  simpa only [sub_neg_eq_add] using one_sub_mul_geomInv (y := -y) (by simp [hy])

/-- Explicit inverse of `x : Truncated R r` given a unit witness `u` for `coeff 0 x`. -/
@[expose] def unitInv (u : Rˣ) (x : Truncated R r) : Truncated R r :=
  algebraMap R (Truncated R r) (u⁻¹ : Rˣ) *
    geomInv (1 - algebraMap R (Truncated R r) (u⁻¹ : Rˣ) * x)

theorem unitInv_def (u : Rˣ) (x : Truncated R r) :
    unitInv u x =
      algebraMap R (Truncated R r) (u⁻¹ : Rˣ) *
        geomInv (1 - algebraMap R (Truncated R r) (u⁻¹ : Rˣ) * x) :=
  rfl

/-- `x * unitInv u x = 1` whenever `coeff 0 x = u`. -/
theorem mul_unitInv {x : Truncated R r} {u : Rˣ} (hu : coeff 0 x = u) :
    x * unitInv u x = 1 := by
  by_cases hr : r = 0
  · subst hr
    have hsub : Subsingleton (Truncated R 0) :=
      Ideal.Quotient.subsingleton_iff.mpr (by simp)
    exact Subsingleton.elim _ _
  · have hrpos : 0 < r := Nat.pos_of_ne_zero hr
    let y : Truncated R r := 1 - algebraMap R (Truncated R r) (u⁻¹ : Rˣ) * x
    have hy0 : coeff 0 y = 0 := by
      simp only [y, coeff_sub, coeff_one, hrpos, and_self, ↓reduceIte]
      rw [coeff_mul_range hrpos, Finset.sum_range_one, Nat.sub_zero, coeff_algebraMap]
      simp only [hrpos, and_self, ↓reduceIte, hu]
      simp [Units.inv_mul]
    have hinv := one_sub_mul_geomInv hy0
    have h1y : 1 - y = algebraMap R (Truncated R r) (u⁻¹ : Rˣ) * x := sub_sub_cancel 1 _
    rw [h1y] at hinv
    change x * (algebraMap R (Truncated R r) (u⁻¹ : Rˣ) * geomInv y) = 1
    linear_combination hinv

/-- An element of `Truncated R r` (for `r > 0`) is a unit iff its constant coefficient is a unit
in `R`. -/
theorem isUnit_iff (hr : 0 < r) {x : Truncated R r} : IsUnit x ↔ IsUnit (coeff 0 x) := by
  constructor
  · rintro ⟨u, hu⟩
    have hcoeff : coeff 0 (u : Truncated R r) * coeff 0 ((u⁻¹ : (Truncated R r)ˣ) : Truncated R r) =
        1 := by
      have h1 := congrArg (coeff 0) u.mul_inv
      rw [coeff_one, coeff_mul_range hr, Finset.sum_range_one, Nat.sub_zero] at h1
      simpa only [hr, and_self, ↓reduceIte] using h1
    rw [hu] at hcoeff
    exact isUnit_iff_exists_inv.mpr ⟨_, hcoeff⟩
  · rintro ⟨u, hu⟩
    exact isUnit_iff_exists_inv.mpr ⟨unitInv u x, mul_unitInv hu.symm⟩

end UnitsAndNilpotency

section Substitution

variable {R : Type*} [CommRing R] {r : ℕ}

/-- Substitute any element `g` satisfying `g ^ r = 0` into `Truncated R r`. -/
def liftAlgHom {B : Type*} [CommRing B] [Algebra R B] {g : B} (hg : g ^ r = 0) :
    Truncated R r →ₐ[R] B :=
  Ideal.Quotient.liftₐ (Ideal.span {(X : R[X]) ^ r}) (Polynomial.aeval g) fun p hp => by
    rw [Ideal.mem_span_singleton] at hp
    rcases hp with ⟨q, rfl⟩
    simp only [map_mul, map_pow, Polynomial.aeval_X, hg, zero_mul]

@[simp]
theorem liftAlgHom_mk {B : Type*} [CommRing B] [Algebra R B] {g : B} (hg : g ^ r = 0)
    (p : R[X]) : liftAlgHom hg (mk r p) = Polynomial.aeval g p := by
  rw [liftAlgHom, mk_apply]
  rfl

@[simp]
theorem liftAlgHom_var {B : Type*} [CommRing B] [Algebra R B] {g : B} (hg : g ^ r = 0) :
    liftAlgHom hg (var R r) = g := by
  simp [var]

theorem liftAlgHom_eq_sum {B : Type*} [CommRing B] [Algebra R B] {g : B} (hg : g ^ r = 0)
    (f : Truncated R r) : liftAlgHom hg f = ∑ i ∈ Finset.range r, coeff i f • g ^ i := by
  conv_lhs => rw [← sum_coeff_mul_var_pow f, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, map_pow, liftAlgHom_var]

/-- Substitution `f ↦ f(g)` into `Truncated S r` for any `g` with `g ^ r = 0`. -/
@[expose] def subst {S : Type*} [CommRing S] [Algebra R S] {g : Truncated S r} (hg : g ^ r = 0) :
    Truncated R r →ₐ[R] Truncated S r :=
  liftAlgHom hg

/-- Substitution `f ↦ f(g)` into `Truncated S r` when `coeff 0 g = 0`. -/
@[expose] def substZeroConst {S : Type*} [CommRing S] [Algebra R S] {g : Truncated S r}
    (hg0 : coeff 0 g = 0) : Truncated R r →ₐ[R] Truncated S r :=
  subst (pow_eq_zero_of_coeff_zero hg0)

theorem subst_apply {S : Type*} [CommRing S] [Algebra R S] {g : Truncated S r} (hg : g ^ r = 0)
    (f : Truncated R r) : subst hg f = liftAlgHom hg f :=
  rfl

theorem subst_eq_sum {S : Type*} [CommRing S] [Algebra R S] {g : Truncated S r} (hg : g ^ r = 0)
    (f : Truncated R r) : subst hg f = ∑ i ∈ Finset.range r, coeff i f • g ^ i :=
  liftAlgHom_eq_sum hg f

theorem substZeroConst_eq_sum {S : Type*} [CommRing S] [Algebra R S] {g : Truncated S r}
    (hg0 : coeff 0 g = 0) (f : Truncated R r) :
    substZeroConst hg0 f = ∑ i ∈ Finset.range r, coeff i f • g ^ i :=
  liftAlgHom_eq_sum (pow_eq_zero_of_coeff_zero hg0) f

@[simp]
theorem subst_mk {S : Type*} [CommRing S] [Algebra R S] {g : Truncated S r} (hg : g ^ r = 0)
    (p : R[X]) : subst hg (mk r p) = Polynomial.aeval g p := by
  rw [subst, liftAlgHom_mk]

@[simp]
theorem subst_var {S : Type*} [CommRing S] [Algebra R S] {g : Truncated S r} (hg : g ^ r = 0) :
    subst hg (var R r) = g := by
  rw [subst, liftAlgHom_var]

@[simp]
theorem substZeroConst_var {S : Type*} [CommRing S] [Algebra R S] {g : Truncated S r}
    (hg0 : coeff 0 g = 0) : substZeroConst hg0 (var R r) = g :=
  subst_var _

theorem substZeroConst_apply {S : Type*} [CommRing S] [Algebra R S] {g : Truncated S r}
    (hg0 : coeff 0 g = 0) (x : Truncated R r) :
    substZeroConst hg0 x = subst (pow_eq_zero_of_coeff_zero hg0) x := by
  simp only [substZeroConst]

@[simp]
theorem substZeroConst_mk {S : Type*} [CommRing S] [Algebra R S] {g : Truncated S r}
    (hg0 : coeff 0 g = 0) (p : R[X]) : substZeroConst hg0 (mk r p) = Polynomial.aeval g p := by
  rw [substZeroConst_apply, subst_mk]

/-- Composition law for nilpotent substitution: `(f(g))(h) = f(g(h))`. -/
theorem subst_comp {S T : Type*} [CommRing S] [CommRing T] [Algebra R S] [Algebra S T]
    [Algebra R T] [IsScalarTower R S T] {g : Truncated S r} (hg : g ^ r = 0)
    {h : Truncated T r} (hh : h ^ r = 0) :
    ((subst hh).restrictScalars R).comp (subst hg) =
      subst (by rw [← map_pow, hg, map_zero] : (subst hh g) ^ r = 0) := by
  refine AlgHom.ext fun f => ?_
  induction f using induction_on with
  | hp p =>
    simp only [AlgHom.comp_apply, AlgHom.coe_restrictScalars', subst_mk]
    exact (Polynomial.aeval_algHom_apply ((subst hh).restrictScalars R) g p).symm

/-- Finite coefficient formula for `substZeroConst`: only terms up to degree `i` contribute. -/
theorem coeff_subst_of_coeff_zero {S : Type*} [CommRing S] [Algebra R S] {g : Truncated S r}
    (hg0 : coeff 0 g = 0) {i : ℕ} (hi : i < r) (f : Truncated R r) :
    coeff i (substZeroConst hg0 f) =
      ∑ d ∈ Finset.range (i + 1), algebraMap R S (coeff d f) * coeff i (g ^ d) := by
  rw [substZeroConst, subst, liftAlgHom_eq_sum _ f, coeff_sum,
    ← Finset.sum_subset (Finset.range_mono (by omega : i + 1 ≤ r))]
  · refine Finset.sum_congr rfl fun d _ => ?_
    exact coeff_smul_algebra i (coeff d f) (g ^ d)
  · intro d _ hd
    rw [Finset.mem_range, not_lt] at hd
    rw [coeff_smul_algebra, coeff_pow_eq_zero_of_lt hg0 hd, mul_zero]

/-- Truncated substitution agrees with polynomial composition `p.comp q` modulo `T ^ r` whenever
`(mk r q) ^ r = 0` (in particular whenever `q.coeff 0 = 0`). -/
theorem mk_comp_eq_subst (p q : R[X]) (hq : (mk r q) ^ r = 0) :
    mk r (p.comp q) = subst hq (mk r p) := by
  rw [subst_mk, Polynomial.comp_eq_aeval]
  exact (Polynomial.aeval_algHom_apply (mk r) q p).symm

private theorem coeff_pow_eq_zero_of_constantCoeff_zero {g : R⟦X⟧}
    (hg0 : PowerSeries.constantCoeff g = 0) {d i : ℕ} (hi : i < d) :
    PowerSeries.coeff i (g ^ d) = 0 :=
  PowerSeries.X_pow_dvd_iff.mp (pow_dvd_pow_of_dvd (PowerSeries.X_dvd_iff.mpr hg0) d) i hi

/-- Truncating `PowerSeries.subst g f` modulo `T ^ r` equals truncated substitution of the
truncations in `Truncated R r`, when `PowerSeries.constantCoeff g = 0`. -/
theorem mk_trunc_subst_eq_subst (f g : R⟦X⟧) (hg0 : PowerSeries.constantCoeff g = 0) :
    mk r (PowerSeries.trunc r (PowerSeries.subst g f)) =
      substZeroConst (g := mk r (PowerSeries.trunc r g))
        (by
          by_cases hr : 0 < r
          · rw [coeff_mk_of_lt hr, PowerSeries.coeff_trunc]
            simp only [hr, ↓reduceIte, PowerSeries.coeff_zero_eq_constantCoeff, hg0]
          · have hr0 : r = 0 := by omega
            subst hr0
            exact coeff_eq_zero_of_le (le_refl 0) _)
        (mk r (PowerSeries.trunc r f)) := by
  ext i hi
  have h0r : 0 < r := Nat.zero_lt_of_lt hi
  have hg_trunc0 : coeff 0 (mk r (PowerSeries.trunc r g)) = 0 := by
    rw [coeff_mk_of_lt h0r, PowerSeries.coeff_trunc]
    simp only [h0r, ↓reduceIte, PowerSeries.coeff_zero_eq_constantCoeff, hg0]
  rw [coeff_mk_of_lt hi, PowerSeries.coeff_trunc]
  simp only [hi, ↓reduceIte]
  rw [PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero hg0),
    coeff_subst_of_coeff_zero hg_trunc0 hi]
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range (i + 1))]
  · refine Finset.sum_congr rfl fun d hd => ?_
    have hdr : d < r := lt_of_lt_of_le (Finset.mem_range.mp hd) hi
    rw [Algebra.algebraMap_self, RingHom.id_apply, coeff_mk_of_lt hdr, PowerSeries.coeff_trunc]
    simp only [hdr, ↓reduceIte]
    rw [← map_pow, mk_trunc_pow, coeff_mk_of_lt hi, PowerSeries.coeff_trunc]
    simp only [hi, ↓reduceIte, smul_eq_mul]
  · intro d hd
    rw [Function.mem_support, ne_eq] at hd
    by_contra hid
    have hlt : i < d := by
      simp only [Finset.mem_coe, Finset.mem_range, not_lt] at hid
      omega
    exact hd (by rw [coeff_pow_eq_zero_of_constantCoeff_zero hg0 hlt, smul_zero])

end Substitution

section FunctorialityAndAdjoinRoot

variable {R : Type*} [CommRing R]

/-- Projection homomorphism `Truncated R r →ₐ[R] Truncated R s` for `s ≤ r`. -/
def proj {s r : ℕ} (hsr : s ≤ r) : Truncated R r →ₐ[R] Truncated R s :=
  Ideal.Quotient.factorₐ R <| by
    rw [Ideal.span_singleton_le_span_singleton]
    exact pow_dvd_pow X hsr

@[simp]
theorem proj_mk {s r : ℕ} (hsr : s ≤ r) (p : R[X]) :
    proj hsr (mk r p) = mk s p := by
  rw [proj, mk_apply, mk_apply, Ideal.Quotient.factorₐ_apply_mk]

@[simp]
theorem proj_var {s r : ℕ} (hsr : s ≤ r) :
    proj hsr (var R r) = var R s := by
  rw [var, var, proj_mk]

@[simp]
theorem coeff_proj {s r : ℕ} (hsr : s ≤ r) {i : ℕ} (hi : i < s) (x : Truncated R r) :
    coeff i (proj hsr x) = coeff i x := by
  induction x using induction_on with
  | hp p =>
    rw [proj_mk, coeff_mk_of_lt hi, coeff_mk_of_lt (lt_of_lt_of_le hi hsr)]

/-- Truncation projection commutes with nilpotent substitution. -/
theorem proj_subst {S : Type*} [CommRing S] [Algebra R S] {s r : ℕ} (hsr : s ≤ r)
    {g : Truncated S r} (hg : g ^ r = 0) {hg' : (proj hsr g) ^ s = 0} (f : Truncated R r) :
    proj hsr (subst hg f) = subst hg' (proj hsr f) := by
  induction f using induction_on with
  | hp p =>
    rw [subst_mk, proj_mk, subst_mk]
    exact (Polynomial.aeval_algHom_apply ((proj hsr).restrictScalars R) g p).symm

/-- Ring homomorphism `Truncated R r →+* Truncated S r` induced by `φ : R →+* S`. -/
def map {S : Type*} [CommRing S] (φ : R →+* S) (r : ℕ) : Truncated R r →+* Truncated S r :=
  Ideal.Quotient.lift (Ideal.span {(X : R[X]) ^ r})
    ((mk r).toRingHom.comp (Polynomial.mapRingHom φ)) fun p hp => by
      rw [Ideal.mem_span_singleton] at hp
      rcases hp with ⟨q, rfl⟩
      simp only [map_mul, RingHom.comp_apply, coe_mapRingHom, Polynomial.map_pow, Polynomial.map_X,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      change (var S r) ^ r * mk r (q.map φ) = 0
      rw [var_pow_eq_zero, zero_mul]

@[simp]
theorem map_mk {S : Type*} [CommRing S] (φ : R →+* S) (r : ℕ) (p : R[X]) :
    map φ r (mk r p) = mk r (p.map φ) := by
  rw [map, mk_apply, Ideal.Quotient.lift_mk]
  rfl

@[simp]
theorem map_var {S : Type*} [CommRing S] (φ : R →+* S) (r : ℕ) :
    map φ r (var R r) = var S r := by
  rw [var, var, map_mk, Polynomial.map_X]

@[simp]
theorem coeff_map {S : Type*} [CommRing S] (φ : R →+* S) (r i : ℕ) (x : Truncated R r) :
    coeff i (map φ r x) = φ (coeff i x) := by
  induction x using induction_on with
  | hp p =>
    simp only [map_mk, coeff_mk, Polynomial.coeff_map]
    split_ifs <;> simp

private noncomputable def toAdjoinRootAlgHom (R : Type*) [CommRing R] (r : ℕ) :
    Truncated R r →ₐ[R] AdjoinRoot ((X : R[X]) ^ r) :=
  Ideal.Quotient.liftₐ (Ideal.span {(X : R[X]) ^ r}) (AdjoinRoot.mkₐ _) fun p hp => by
    rw [Ideal.mem_span_singleton] at hp
    rcases hp with ⟨q, rfl⟩
    simp [AdjoinRoot.mk_self]

/-- Canonical `R`-algebra equivalence between `Truncated R r` and Mathlib's
`AdjoinRoot ((X : R[X]) ^ r)`. -/
def equivAdjoinRoot (R : Type*) [CommRing R] (r : ℕ) :
    Truncated R r ≃ₐ[R] AdjoinRoot ((X : R[X]) ^ r) :=
  let invHom : AdjoinRoot ((X : R[X]) ^ r) →ₐ[R] Truncated R r :=
    AdjoinRoot.liftAlgHom ((X : R[X]) ^ r) (Algebra.ofId R (Truncated R r)) (var R r)
      (by simp [Polynomial.eval₂_X_pow])
  { toFun := toAdjoinRootAlgHom R r
    invFun := invHom
    left_inv x := by
      induction x using induction_on with
      | hp p =>
        have hto : toAdjoinRootAlgHom R r (Ideal.Quotient.mk _ p) = AdjoinRoot.mk _ p := by
          simp only [toAdjoinRootAlgHom, Ideal.Quotient.liftₐ_apply]
          rfl
        change invHom (toAdjoinRootAlgHom R r (Ideal.Quotient.mk _ p)) = Ideal.Quotient.mk _ p
        rw [hto]
        change AdjoinRoot.liftAlgHom ((X : R[X]) ^ r) (Algebra.ofId R (Truncated R r)) (var R r) _
          (AdjoinRoot.mk _ p) = mk r p
        rw [AdjoinRoot.liftAlgHom_mk]
        change Polynomial.eval₂ (algebraMap R (Truncated R r)) (var R r) p = mk r p
        rw [← Polynomial.aeval_def, var, Polynomial.aeval_algHom_apply (mk r) X p,
          Polynomial.aeval_X_left]
        rfl
    right_inv y := by
      induction y using AdjoinRoot.induction_on with
      | ih p =>
        have hinv : invHom (AdjoinRoot.mk _ p) = mk r p := by
          change AdjoinRoot.liftAlgHom ((X : R[X]) ^ r) (Algebra.ofId R (Truncated R r)) (var R r) _
            (AdjoinRoot.mk _ p) = mk r p
          rw [AdjoinRoot.liftAlgHom_mk]
          change Polynomial.eval₂ (algebraMap R (Truncated R r)) (var R r) p = mk r p
          rw [← Polynomial.aeval_def, var, Polynomial.aeval_algHom_apply (mk r) X p,
            Polynomial.aeval_X_left]
          rfl
        rw [hinv, mk_apply]
        simp only [toAdjoinRootAlgHom, Ideal.Quotient.liftₐ_apply]
        rfl
    map_mul' := (toAdjoinRootAlgHom R r).map_mul
    map_add' := (toAdjoinRootAlgHom R r).map_add
    commutes' := (toAdjoinRootAlgHom R r).commutes }

@[simp]
theorem equivAdjoinRoot_mk (R : Type*) [CommRing R] (r : ℕ) (p : R[X]) :
    equivAdjoinRoot R r (mk r p) = AdjoinRoot.mk ((X : R[X]) ^ r) p := by
  change toAdjoinRootAlgHom R r (mk r p) = AdjoinRoot.mk _ p
  rw [toAdjoinRootAlgHom, mk_apply]
  rfl

@[simp]
theorem equivAdjoinRoot_symm_mk (R : Type*) [CommRing R] (r : ℕ) (p : R[X]) :
    (equivAdjoinRoot R r).symm (AdjoinRoot.mk ((X : R[X]) ^ r) p) = mk r p :=
  (equivAdjoinRoot R r).symm_apply_eq.mpr (equivAdjoinRoot_mk R r p).symm

end FunctorialityAndAdjoinRoot

end

end Truncated

end Polynomial
