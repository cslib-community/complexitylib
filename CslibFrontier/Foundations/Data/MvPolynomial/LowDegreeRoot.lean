/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Algebra.Polynomial.LagrangeInversion
public import CslibFrontier.Foundations.Data.MvPolynomial.Shift
public import CslibFrontier.Foundations.Data.MvPolynomial.Substitution
public import CslibFrontier.Foundations.Data.MvPolynomial.TruncateTotalDegree
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# A closed formula for the low-degree part of a root

Let `P (x, y)` be a polynomial over a field `F` of characteristic zero and `f (x)` a polynomial
with `P (x, f) = 0`.

**Simple root at the origin** (`MvPolynomial.truncateTotalDegree_root_eq`). If `f (0) = 0` and
`a = (∂P/∂y) (0, 0) ≠ 0`, then for every `D`, with `G = y - P / a`,

`f_{≤ D} = (∑ m ∈ {1, …, 2 D + 2}, (1 / m) [y ^ (m - 1)] G ^ m)_{≤ D}`,

where the subscript is the truncation to total degree at most `D`
(`MvPolynomial.truncateTotalDegree`) and `[y ^ j]` is the coefficient of `y ^ j`. This is
Lagrange inversion (`Polynomial.sub_sum_coeff_pow_mem_of_eval_eq`) for the ideal of the
variables, whose `n`-th power consists of the polynomials vanishing to order `n` at the origin
(Mathlib's `MvPolynomial.idealOfVars`). It is the formula for power-series roots of
Bhattacharjee, Kumar, Rai, Ramanathan, Saptharishi and Saraf
[BhattacharjeeEtAl2025, Corollary 3.3 and Theorem 4.1], for a polynomial root and without the
scaling `x ↦ t x`.

**Any root** (`MvPolynomial.exists_shift_eq_truncate_sum_of_root`). For `P ≠ 0` some iterated
`y`-derivative of `P` has `f` as a root with nonvanishing next derivative
(`exists_iterate_derivative_eval_ne_zero`); shifting `x` to a point `x₀` where that derivative
does not vanish at `f`, and `y` by `f (x₀)`, reduces to the first case.

The point of the formula for circuit complexity is that the root is obtained from `P` by
powers, coefficients in `y` and a truncation, with no iteration: a root of a polynomial with a
small formula of constant depth has a small formula of constant depth.

## Main results

* `MvPolynomial.truncateTotalDegree_root_eq`: the formula for a simple root at the origin.
* `MvPolynomial.exists_shift_eq_truncate_sum_of_root`: the formula for any root of a nonzero
  polynomial, after differentiating in `y` and shifting.

## References

* [S. Bhattacharjee, M. Kumar, S. Rai, V. Ramanathan, R. Saptharishi, S. Saraf, *Closure under
  factorization from a result of Furstenberg*][BhattacharjeeEtAl2025], Corollary 3.3 and
  Theorem 4.1 (unrefereed preprint)
* [Z. Dvir, A. Shpilka, A. Yehudayoff, *Hardness-randomness tradeoffs for bounded depth
  arithmetic circuits*][DvirShpilkaYehudayoff2009], for the reduction of a multiple root to a
  simple one by derivatives and a shift
-/

public section

namespace MvPolynomial

open Finset

variable {σ F : Type*} [Field F]

/-! ### Order of vanishing at the origin -/

/-- A polynomial is in the ideal of the variables exactly when it has no constant term. -/
theorem mem_idealOfVars_iff_constantCoeff {p : MvPolynomial σ F} :
    p ∈ idealOfVars σ F ↔ constantCoeff p = 0 := by
  have h := mem_pow_idealOfVars_iff' (σ := σ) (R := F) 1 p
  rw [pow_one] at h
  rw [h, constantCoeff_eq]
  refine ⟨fun hp => hp 0 (by simp), fun hp x hx => ?_⟩
  obtain rfl : x = 0 := by
    rw [Nat.lt_one_iff, Finsupp.degree_eq_zero_iff] at hx
    exact hx
  exact hp

/-- Polynomials that agree to order `d + 1` have the same truncation to degree at most `d`. -/
theorem truncateTotalDegree_eq_of_sub_mem {d : ℕ} {p q : MvPolynomial σ F}
    (h : p - q ∈ idealOfVars σ F ^ (d + 1)) :
    truncateTotalDegree d p = truncateTotalDegree d q := by
  rw [mem_pow_idealOfVars_iff'] at h
  ext x
  rw [coeff_truncateTotalDegree, coeff_truncateTotalDegree]
  split_ifs with hx
  · have := h x (Nat.lt_succ_of_le hx)
    rwa [coeff_sub, sub_eq_zero] at this
  · rfl

/-! ### A simple root at the origin -/

/-- **The low-degree part of a simple root at the origin.** Let `P` be a polynomial in `y` over
`F[x]`, in characteristic zero, and `f` a polynomial without constant term with `P (f) = 0`.
If the constant term `a` of the coefficient of `y` in `P` is not zero, then the truncation of
`f` to degree at most `D` is the truncation of
`∑ m ∈ {1, …, 2 D + 2}, (1 / m) [y ^ (m - 1)] (y - P / a) ^ m`. -/
theorem truncateTotalDegree_root_eq [CharZero F] {P : Polynomial (MvPolynomial σ F)}
    {f : MvPolynomial σ F} (hf0 : constantCoeff f = 0) (hroot : P.eval f = 0)
    (ha : constantCoeff (P.coeff 1) ≠ 0) (D : ℕ) :
    truncateTotalDegree D f = truncateTotalDegree D (∑ m ∈ range (2 * (D + 1)),
      ((m : F) + 1)⁻¹ • ((Polynomial.X -
        Polynomial.C (C (constantCoeff (P.coeff 1))⁻¹) * P) ^ (m + 1)).coeff m) := by
  set a := constantCoeff (P.coeff 1) with haa
  set G : Polynomial (MvPolynomial σ F) := Polynomial.X - Polynomial.C (C a⁻¹) * P with hG
  have hP0 : constantCoeff (P.coeff 0) = 0 := by
    have h := congrArg constantCoeff hroot
    rw [map_zero, ← Polynomial.eval₂_id, Polynomial.hom_eval₂, RingHom.comp_id, hf0,
      Polynomial.eval₂_at_zero] at h
    exact h
  have h0 : G.coeff 0 ∈ idealOfVars σ F := by
    rw [mem_idealOfVars_iff_constantCoeff, hG, Polynomial.coeff_sub, Polynomial.coeff_X_zero,
      Polynomial.coeff_C_mul, map_sub, map_zero, map_mul, hP0, mul_zero, sub_zero]
  have h1 : G.coeff 1 ∈ idealOfVars σ F := by
    rw [mem_idealOfVars_iff_constantCoeff, hG, Polynomial.coeff_sub, Polynomial.coeff_X_one,
      Polynomial.coeff_C_mul, map_sub, map_one, map_mul, constantCoeff_C, ← haa,
      inv_mul_cancel₀ ha, sub_self]
  have hfix : G.eval f = f := by
    rw [hG, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_mul, hroot, mul_zero,
      sub_zero]
  exact truncateTotalDegree_eq_of_sub_mem (Polynomial.sub_sum_coeff_pow_mem_of_eval_eq
    (F := F) h0 h1 (mem_idealOfVars_iff_constantCoeff.2 hf0) hfix le_rfl)

/-! ### Any root -/

/-- In characteristic zero a root `f` of a nonzero polynomial `P` is a root of some iterated
derivative of `P` whose next derivative does not vanish at `f`. -/
theorem exists_iterate_derivative_eval_ne_zero [CharZero F] {P : Polynomial (MvPolynomial σ F)}
    (hP : P ≠ 0) {f : MvPolynomial σ F} (hroot : P.eval f = 0) :
    ∃ j : ℕ, (Polynomial.derivative^[j] P).eval f = 0 ∧
      (Polynomial.derivative^[j + 1] P).eval f ≠ 0 := by
  have hk : 0 < P.rootMultiplicity f := (Polynomial.rootMultiplicity_pos hP).2 hroot
  refine ⟨P.rootMultiplicity f - 1, ?_, ?_⟩
  · exact (Polynomial.lt_rootMultiplicity_iff_isRoot_iterate_derivative hP).1
      (Nat.sub_lt hk Nat.one_pos) _ le_rfl
  · intro h0
    refine lt_irrefl (P.rootMultiplicity f)
      ((Polynomial.lt_rootMultiplicity_iff_isRoot_iterate_derivative hP).2 fun m hm => ?_)
    rcases Nat.lt_or_ge m (P.rootMultiplicity f) with hlt | hge
    · exact (Polynomial.lt_rootMultiplicity_iff_isRoot_iterate_derivative hP).1 hlt m le_rfl
    · obtain rfl : m = P.rootMultiplicity f - 1 + 1 := by omega
      exact h0

/-- **The low-degree part of any root.** Let `P ≠ 0` be a polynomial in `y` over `F[x]`, in
characteristic zero, and `f` a polynomial with `P (f) = 0`. Then for some `j` and some point
`x₀`, with `Q` the `j`-th `y`-derivative of `P` shifted by `x₀` in `x` and by `f (x₀)` in `y`,
the constant term `a` of the coefficient of `y` in `Q` is not zero and, for every `D` at least
the total degree of `f`, `f (x + x₀) = f (x₀) +
(∑ m ∈ {1, …, 2 D + 2}, (1 / m) [y ^ (m - 1)] (y - Q / a) ^ m)_{≤ D}`. -/
theorem exists_shift_eq_truncate_sum_of_root [CharZero F]
    {P : Polynomial (MvPolynomial σ F)} (hP : P ≠ 0) {f : MvPolynomial σ F}
    (hroot : P.eval f = 0) :
    ∃ (j : ℕ) (x₀ : σ → F),
      constantCoeff ((Polynomial.taylor (C (eval x₀ f)) ((Polynomial.derivative^[j] P).map
        (shift x₀ : _ →ₐ[F] _).toRingHom)).coeff 1) ≠ 0 ∧
      ∀ D : ℕ, f.totalDegree ≤ D →
        shift x₀ f = C (eval x₀ f) + truncateTotalDegree D (∑ m ∈ range (2 * (D + 1)),
          ((m : F) + 1)⁻¹ • ((Polynomial.X - Polynomial.C (C (constantCoeff
            ((Polynomial.taylor (C (eval x₀ f)) ((Polynomial.derivative^[j] P).map
              (shift x₀ : _ →ₐ[F] _).toRingHom)).coeff 1))⁻¹) *
            Polynomial.taylor (C (eval x₀ f)) ((Polynomial.derivative^[j] P).map
              (shift x₀ : _ →ₐ[F] _).toRingHom)) ^ (m + 1)).coeff m) := by
  classical
  have : Infinite F := Infinite.of_injective Nat.cast Nat.cast_injective
  obtain ⟨j, hj0, hj1⟩ := exists_iterate_derivative_eval_ne_zero hP hroot
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : σ → F,
      eval x₀ ((Polynomial.derivative^[j + 1] P).eval f) ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hj1 (funext fun x => by rw [hall x, map_zero])
  set φ : MvPolynomial σ F →+* MvPolynomial σ F := (shift x₀ : _ →ₐ[F] _).toRingHom with hφ
  have hcc : ∀ p : MvPolynomial σ F, constantCoeff (φ p) = eval x₀ p := fun p => by
    rw [constantCoeff_eq]
    exact coeff_zero_shift x₀ p
  have hmapeval : ∀ R : Polynomial (MvPolynomial σ F),
      (R.map φ).eval (shift x₀ f) = φ (R.eval f) := fun R => by
    rw [Polynomial.eval_map]
    exact Polynomial.eval₂_hom φ f
  set α := eval x₀ f with hα
  set Q := Polynomial.taylor (C α) ((Polynomial.derivative^[j] P).map φ) with hQ
  set f₁ := shift x₀ f - C α with hf₁
  have hf₁0 : constantCoeff f₁ = 0 := by
    rw [hf₁, map_sub, constantCoeff_C]
    exact sub_eq_zero.2 (hcc f)
  have hQroot : Q.eval f₁ = 0 := by
    rw [hQ, Polynomial.taylor_eval, hf₁, sub_add_cancel, hmapeval, hj0, map_zero]
  have hcceval : ∀ (R : Polynomial (MvPolynomial σ F)) (z : MvPolynomial σ F),
      constantCoeff (R.eval z) = (R.map constantCoeff).eval (constantCoeff z) := fun R z => by
    rw [Polynomial.eval_map, Polynomial.eval₂_hom]
  have hder : constantCoeff (Q.coeff 1) ≠ 0 := by
    rw [hQ, Polynomial.taylor_coeff_one, ← Polynomial.iterate_derivative_map,
      ← Function.iterate_succ_apply' Polynomial.derivative, Polynomial.iterate_derivative_map]
    have hev : constantCoeff (((Polynomial.derivative^[j + 1] P).map φ).eval (C α)) =
        constantCoeff (((Polynomial.derivative^[j + 1] P).map φ).eval (shift x₀ f)) := by
      rw [hcceval, hcceval, constantCoeff_C, show constantCoeff (shift x₀ f) = α from hcc f]
    rw [hev, hmapeval, hcc]
    exact hx₀
  refine ⟨j, x₀, hder, fun D hD => ?_⟩
  have hdeg : f₁.totalDegree ≤ D := by
    refine (totalDegree_sub _ _).trans (max_le ((totalDegree_aeval_le (fun i =>
      (totalDegree_add _ _).trans (max_le (totalDegree_X i).le
        (by rw [totalDegree_C]; exact Nat.zero_le _))) f).trans hD) ?_)
    rw [totalDegree_C]
    exact Nat.zero_le _
  rw [← truncateTotalDegree_root_eq hf₁0 hQroot hder D, truncateTotalDegree_eq_self hdeg, hf₁,
    add_sub_cancel]

end MvPolynomial
