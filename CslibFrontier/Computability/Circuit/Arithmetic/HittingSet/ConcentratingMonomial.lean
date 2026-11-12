/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.MvPolynomial.InitialMonomial
public import CslibFrontier.Foundations.Data.MvPolynomial.SubstituteOne
public import Mathlib.Algebra.MvPolynomial.Supported
public import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Points with monomial coordinates: a count of initial monomials

Let `Y` be a set of `k` variables, `w < 2 ^ k`, and let `H = ∑ i, ρ i • p i` be a combination,
with coefficients `ρ i` in `F[τ]`, of `w` polynomials `p i` over the field `F` in the variables of
`Y`, of individual degree at most `δ`. Scale the variables by powers of `τ`:
`H̃ = H (τ ^ E v • X v)`, where the weights `E` separate the exponent vectors with entries at most
`δ`. If `H̃` becomes zero under each substitution `X j ↦ 1`, `j ∈ Y`, then `H = 0`
(`eq_zero_of_scale_X_pow_vanishing`).

This is the statement that the point `(τ ^ E v)` is concentrating
(`Cslib.Circuits.Arithmetic.IsConcentrating`), before the translation between shifts and scalings.
For points with monomial coordinates it replaces the rank-condenser argument of Forbes,
Saptharishi and Shpilka [ForbesSaptharishiShpilka2014, §3.2–3.3] by a count of initial monomials.
The argument is not taken from a source.

## Proof

Suppose `H ≠ 0`. Let `ν` be the least exponent of `τ` that occurs in a coefficient of `H̃`, and
`H̃₀`, a polynomial over `F`, the coefficient of `τ ^ ν` in `H̃`. It is nonzero, and it becomes zero
under each substitution `X j ↦ 1`, since these do not touch the coefficients. Hence `H̃₀` has at
least `2 ^ k` monomials (`MvPolynomial.two_pow_card_le_card_support`).

On the other hand, write `s b = ∑ j ∈ Y, b j * E j` for the weight of a monomial `b`, so that the
coefficient of `b` in `H̃` is `τ ^ s b` times its coefficient in `H`. For a monomial `b` of `H̃₀`,
the coefficient `v b` of `τ ^ (ν - s b)` in `H` is an `F`-combination of the `p i` that contains
`b`, and every monomial `m` of `v b` has `ν ≤ ν - s b + s m` by the choice of `ν`. So `b` is the
monomial of least weight of `v b`, strictly since the weights are distinct. Polynomials with
distinct initial monomials are linearly independent
(`MvPolynomial.linearIndependent_of_initial_monomial`), and the `v b` lie in the span of `w`
polynomials: `H̃₀` has at most `w` monomials.

## Main results

* `eq_zero_of_scale_X_pow_vanishing`: the statement above.

## References

* [M. A. Forbes, R. Saptharishi, A. Shpilka, *Pseudorandomness for multilinear read-once
  algebraic branching programs, in any order*][ForbesSaptharishiShpilka2014]
-/

public section

namespace Cslib.Circuits.Arithmetic

open Finset MvPolynomial

open scoped Polynomial

variable {σ R : Type*} [CommSemiring R]

/-- The coefficients of a polynomial after scaling each variable `X v` by `c v`. -/
private theorem coeff_aeval_C_mul_X (c : σ → R) (p : MvPolynomial σ R) (m : σ →₀ ℕ) :
    (aeval (fun v => C (c v) * X v) p).coeff m = p.coeff m * m.prod fun v e => c v ^ e := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial m' a =>
    have h : aeval (fun v => C (c v) * X v) (monomial m' a) =
        monomial m' (a * m'.prod fun v e => c v ^ e) := by
      rw [aeval_monomial, algebraMap_eq, monomial_eq (a := a * _), C_mul, mul_assoc]
      simp only [mul_pow, Finsupp.prod_mul, map_finsuppProd, C_pow]
    rw [h, coeff_monomial, coeff_monomial]
    split_ifs with hm
    · rw [hm]
    · rw [zero_mul]
  | add p q hp hq =>
    rw [map_add]
    exact (congrArg₂ (· + ·) hp hq).trans (add_mul _ _ _).symm

/-- **Points with monomial coordinates are concentrating.** Let `w < 2 ^ k`, let `Y` be a set of
`k` variables, and let the weights `E` separate the exponent vectors on `Y` with entries at most
`δ`. Let `H = ∑ i, ρ i • p i` be a combination, with coefficients in `F[τ]`, of `w` polynomials
over `F` in the variables of `Y`, of individual degree at most `δ`. If the scaled polynomial
`H (τ ^ E v • X v)` becomes zero under each substitution `X j ↦ 1`, `j ∈ Y`, then `H = 0`. -/
theorem eq_zero_of_scale_X_pow_vanishing {σ F : Type*} [DecidableEq σ] [Field F] {Y : Finset σ}
    {k w δ : ℕ} (hY : Y.card = k) (hw : w < 2 ^ k) {E : σ → ℕ}
    (hE : Set.InjOn (fun b : σ →₀ ℕ => ∑ j ∈ Y, b j * E j)
      {b | (b.support : Set σ) ⊆ Y ∧ ∀ j, b j ≤ δ})
    {p : Fin w → MvPolynomial σ F} (hp : ∀ i, p i ∈ supported F (Y : Set σ)) (ρ : Fin w → F[X])
    (hdeg : ∀ j, (∑ i, C (ρ i) * map (algebraMap F F[X]) (p i)).degreeOf j ≤ δ)
    (hvan : ∀ j ∈ Y, aeval (Function.update (X : σ → MvPolynomial σ F[X]) j 1)
      (aeval (fun v => C ((Polynomial.X : F[X]) ^ E v) * X v)
        (∑ i, C (ρ i) * map (algebraMap F F[X]) (p i))) = 0) :
    ∑ i, C (ρ i) * map (algebraMap F F[X]) (p i) = 0 := by
  set H : MvPolynomial σ F[X] := ∑ i, C (ρ i) * map (algebraMap F F[X]) (p i) with hH
  set Ht : MvPolynomial σ F[X] := aeval (fun v => C ((Polynomial.X : F[X]) ^ E v) * X v) H with hHt
  set s : (σ →₀ ℕ) → ℕ := fun b => ∑ j ∈ Y, b j * E j with hs
  by_contra hH0
  -- the monomials of `H` are exponent vectors on `Y` with entries at most `δ`
  have hmem : ∀ m ∈ H.support, m ∈ {b : σ →₀ ℕ | (b.support : Set σ) ⊆ Y ∧ ∀ j, b j ≤ δ} := by
    have hsup : H ∈ supported F[X] (Y : Set σ) := sum_mem fun i _ =>
      mul_mem (Subalgebra.algebraMap_mem _ _)
        (mem_supported.2 ((coe_subset.2 (vars_map _ _)).trans (mem_supported.1 (hp i))))
    exact fun m hm =>
      ⟨fun j hj => mem_supported.1 hsup ((mem_vars_iff_mem_support j).2 ⟨m, hm, hj⟩),
      fun j => (monomial_le_degreeOf j hm).trans (hdeg j)⟩
  have hcoeff : ∀ m, Ht.coeff m = H.coeff m * Polynomial.X ^ s m := fun m => by
    rw [hHt, coeff_aeval_C_mul_X]
    by_cases hm : m ∈ H.support
    · congr 1
      simp only [Finsupp.prod, ← pow_mul, prod_pow_eq_pow_sum, hs]
      congr 1
      refine (sum_subset (coe_subset.1 (hmem m hm).1) fun j _ hj => ?_).trans
        (sum_congr rfl fun j _ => mul_comm _ _)
      rw [Finsupp.notMem_support_iff.1 hj, mul_zero]
    · rw [notMem_support_iff.1 hm, zero_mul, zero_mul]
  have hcoeff' : ∀ m t, (Ht.coeff m).coeff (t + s m) = (H.coeff m).coeff t := fun m t => by
    rw [hcoeff, Polynomial.coeff_mul_X_pow]
  -- the least exponent `ν` of `τ` in `Ht`, and the coefficient `H0` of `τ ^ ν`
  have hex : ∃ n m, (Ht.coeff m).coeff n ≠ 0 := by
    obtain ⟨m, hm⟩ := support_nonempty.2 hH0
    have h0 : Ht.coeff m ≠ 0 := by
      rw [hcoeff]
      exact mul_ne_zero (mem_support_iff.1 hm) (pow_ne_zero _ Polynomial.X_ne_zero)
    exact ⟨_, m, Polynomial.leadingCoeff_ne_zero.2 h0⟩
  classical
  set ν := Nat.find hex with hν
  obtain ⟨m₀, hm₀⟩ := Nat.find_spec hex
  have hmin : ∀ m n, (Ht.coeff m).coeff n ≠ 0 → ν ≤ n := fun m n h => Nat.find_min' hex ⟨m, h⟩
  set H0 : MvPolynomial σ F := ∑ m ∈ Ht.support, monomial m ((Ht.coeff m).coeff ν) with hH0def
  have hH0c : ∀ m, H0.coeff m = (Ht.coeff m).coeff ν := fun m => by
    rw [hH0def, coeff_sum]
    simp only [coeff_monomial]
    rw [sum_ite_eq' Ht.support m]
    split_ifs with hm
    · rfl
    · rw [notMem_support_iff.1 hm, Polynomial.coeff_zero]
  have hH0sub : H0.support ⊆ Ht.support := fun m hm => by
    rw [mem_support_iff, hH0c] at hm
    exact mem_support_iff.2 fun h => hm (by rw [h, Polynomial.coeff_zero])
  -- `H0` has at least `2 ^ k` monomials
  have hlow : 2 ^ k ≤ H0.support.card := by
    rw [← hY]
    refine two_pow_card_le_card_support (fun h => hm₀ (by rw [← hH0c, h]; rfl)) fun j hj => ?_
    ext m'
    rw [coeff_aeval_update_X_one hH0sub]
    simp_rw [hH0c]
    rw [← Polynomial.finsetSum_coeff, ← coeff_aeval_update_X_one subset_rfl, hvan j hj]
    rfl
  -- `H0` has at most `w` monomials: they are the initial monomials of the polynomials `v b`
  have hb : ∀ b ∈ H0.support, s b ≤ ν ∧ (H.coeff b).coeff (ν - s b) ≠ 0 := fun b hb => by
    rw [mem_support_iff, hH0c, hcoeff, Polynomial.coeff_mul_X_pow'] at hb
    exact ⟨by_contra fun h => hb (ite_eq_right h), fun h => hb (by rw [h, ite_self])⟩
  let v : H0.support → MvPolynomial σ F := fun b => ∑ i, (ρ i).coeff (ν - s b) • p i
  have hvc : ∀ b m, (v b).coeff m = (H.coeff m).coeff (ν - s b) := fun b m => by
    simp [v, hH, Polynomial.finsetSum_coeff, coeff_map, Polynomial.coeff_mul_C]
  have hsupp : ∀ m t, (H.coeff m).coeff t ≠ 0 → m ∈ H.support := fun m t h =>
    mem_support_iff.2 fun h0 => h (by rw [h0, Polynomial.coeff_zero])
  have hli : LinearIndependent F v :=
    linearIndependent_of_initial_monomial s Subtype.val_injective
      (fun b => by rw [hvc]; exact (hb b b.2).2) fun b m hm hne => by
        rw [mem_support_iff, hvc] at hm
        have h1 := hmin m _ (by rwa [hcoeff'])
        have h2 := (hb b b.2).1
        refine lt_of_le_of_ne (by omega) fun h => hne ?_
        exact (hE (hmem _ (hsupp _ _ (hb b b.2).2)) (hmem m (hsupp _ _ hm)) h).symm
  have := Module.Finite.span_of_finite F (Set.finite_range p)
  have hup : H0.support.card ≤ w :=
    calc H0.support.card = Module.finrank F (Submodule.span F (Set.range v)) := by
          rw [finrank_span_eq_card hli, Fintype.card_coe]
      _ ≤ Module.finrank F (Submodule.span F (Set.range p)) :=
          Submodule.finrank_mono (Submodule.span_le.2 (by
            rintro _ ⟨b, rfl⟩
            exact sum_mem fun i _ => Submodule.smul_mem _ _
              (Submodule.subset_span (Set.mem_range_self i))))
      _ ≤ w := (finrank_range_le_card p).trans_eq (Fintype.card_fin w)
  omega

end Cslib.Circuits.Arithmetic
