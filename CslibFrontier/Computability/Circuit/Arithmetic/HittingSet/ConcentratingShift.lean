/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.MvPolynomial.Shift
public import CslibFrontier.Foundations.Data.MvPolynomial.SplitRank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Shifts that concentrate a multilinear polynomial on monomials of small support

Let `f` be a nonzero multilinear polynomial of split rank at most `w` across every set of `k`
variables (`MvPolynomial.SplitRankLE`), with `w < 2 ^ k`. The monomial `∏ᵢ Xᵢ` shows that `f`
itself may have no monomial with few variables. After a shift by a sufficiently generic point `γ`
it does: `f (X + γ)` has a monomial with fewer than `k` variables
(`exists_mem_support_shift_card_lt`).

Generic means that, for every set `Y` of `k` variables, the `2 ^ k` products `∏_{j ∈ T} γ j`,
`T ⊆ Y`, are linearly independent over the field of coefficients. The point `γ` has coordinates
in a domain `R` over that field, for instance a polynomial ring; an explicit set of shifts in the
field itself is obtained from such a point in
`CslibFrontier/Computability/Circuit/Arithmetic/HittingSet/ConcentratingShiftSet.lean`.

This is the case of individual degree one of the support concentration theorem of Forbes,
Saptharishi and Shpilka [ForbesSaptharishiShpilka2014, Theorem 4.1 with Corollary 3.22], in the
form quoted by Shpilka [Shpilka2026, Theorem 2.3]. Two things differ. The source treats
polynomials of any individual degree, by rank condensers built from codes; for multilinear
polynomials the direct argument below suffices and that machinery is not formalized. The source
bounds the support by `⌊lg w²⌋` because it works with a `w × w` matrix of polynomials; working
with the polynomial gives `⌊lg w⌋`.

## Proof

Take a monomial `m₀` of `G = f (X + γ)` with the fewest variables, and suppose it has `k`
variables `Y` among its variables. Substitute `Xⱼ ↦ Xⱼ - γⱼ` for `j ∈ Y`, `Xⱼ ↦ 1` for the other
variables of `m₀`, and `Xⱼ ↦ 0` for the rest. By minimality only `m₀` survives in `G`, which
becomes `c ∏_{j ∈ Y} (Xⱼ - γⱼ)` with `c ≠ 0`. Applied to `f = ∑ᵢ pᵢ qᵢ`, with `pᵢ` in the variables
`Y`, the composite substitution fixes `pᵢ` and turns `qᵢ` into a constant. So
`c ∏_{j ∈ Y} (Xⱼ - γⱼ)` is a combination of the `w` polynomials `pᵢ`. As `w < 2 ^ k`, some nonzero
functional on the multilinear monomials in `Y` kills every `pᵢ`; evaluated on the product it is a
nonzero combination of the products `∏_{j ∈ T} γⱼ`, which is nonzero by genericity.

## Main results

* `exists_mem_support_shift_card_lt`: a generic shift of a nonzero multilinear polynomial of
  small split rank has a monomial of small support.

## References

* [M. A. Forbes, R. Saptharishi, A. Shpilka, *Pseudorandomness for multilinear read-once
  algebraic branching programs, in any order*][ForbesSaptharishiShpilka2014]
* [A. Shpilka, *Polynomial-size hitting sets for multilinear any-order read-once algebraic
  branching programs and for set-multilinear depth-3 circuits with constant-size variable
  sets*][Shpilka2026] (unrefereed preprint)
-/

public section

namespace Cslib.Circuits.Arithmetic

open Finset MvPolynomial

variable {σ F R : Type*} [Field F] [CommRing R] [IsDomain R] [Algebra F R]

/-- The exponent vector of the product of the variables in `T`. -/
private noncomputable def ind (T : Finset σ) : σ →₀ ℕ := ∑ j ∈ T, Finsupp.single j 1

private theorem ind_apply [DecidableEq σ] (T : Finset σ) (j : σ) :
    ind T j = if j ∈ T then 1 else 0 := by
  simp [ind, Finsupp.single_apply]

private theorem ind_injective : Function.Injective (ind : Finset σ → σ →₀ ℕ) := by
  classical
  intro S T h
  ext j
  have := DFunLike.congr_fun h j
  rw [ind_apply, ind_apply] at this
  by_cases hS : j ∈ S <;> by_cases hT : j ∈ T <;> simp_all

omit [IsDomain R] in
private theorem coeff_ind_prod_X_add_C [DecidableEq σ] {Y T : Finset σ} (hT : T ⊆ Y)
    (b : σ → R) : (∏ j ∈ Y, (X j + C (b j))).coeff (ind T) = ∏ j ∈ Y \ T, b j := by
  rw [Finset.prod_add, coeff_sum, Finset.sum_eq_single T]
  · rw [← map_prod, show ∏ j ∈ T, (X j : MvPolynomial σ R) = monomial (ind T) 1 from
      (monomial_sum_one T _).symm, mul_comm, C_mul_monomial, mul_one, coeff_monomial,
      ite_eq_left rfl]
  · intro S _ hS
    rw [← map_prod, show ∏ j ∈ S, (X j : MvPolynomial σ R) = monomial (ind S) 1 from
      (monomial_sum_one S _).symm, mul_comm, C_mul_monomial, mul_one, coeff_monomial,
      ite_eq_right fun h => hS (ind_injective h)]
  · exact fun h => absurd (mem_powerset.2 hT) h

/-- **Small-support concentration under a generic shift.** Let `w < 2 ^ k` and let `γ` be a point
such that, for every set `Y` of `k` variables, the products of the coordinates of `γ` over the
subsets of `Y` are linearly independent over `F`. If `f` is a nonzero multilinear polynomial of
split rank at most `w` across every set of `k` variables, then `f (X + γ)` has a monomial with
fewer than `k` variables. -/
theorem exists_mem_support_shift_card_lt {γ : σ → R} {k w : ℕ} (hw : w < 2 ^ k)
    (hγ : ∀ Y : Finset σ, Y.card = k → ∀ c : Finset σ → F,
      ∑ T ∈ Y.powerset, c T • ∏ j ∈ T, γ j = 0 → ∀ T ∈ Y.powerset, c T = 0)
    {f : MvPolynomial σ F} (hf0 : f ≠ 0) (hmul : ∀ i, f.degreeOf i ≤ 1)
    (hf : ∀ Y : Finset σ, Y.card = k → SplitRankLE (Y : Set σ) w f) :
    ∃ m ∈ (shift γ f).support, m.support.card < k := by
  classical
  set G : MvPolynomial σ R := shift γ f with hG
  have hG0 : G ≠ 0 := fun h => hf0 (shift_injective (algebraMap F R).injective γ
    (h.trans (map_zero _).symm))
  obtain ⟨m₀, hm₀, hmin⟩ := Finset.exists_min_image G.support (fun m => m.support.card)
    (support_nonempty.2 hG0)
  refine ⟨m₀, hm₀, ?_⟩
  by_contra hk
  obtain ⟨Y, hYM, hYk⟩ := Finset.exists_subset_card_eq (not_lt.1 hk)
  obtain ⟨p, q, hp, hq, hfpq⟩ := hf Y hYk
  have hGmul : ∀ m ∈ G.support, ∀ i, m i ≤ 1 := fun m hm i =>
    (monomial_le_degreeOf i hm).trans ((degreeOf_shift_le γ f i).trans (hmul i))
  -- the substitution that undoes the shift on `Y`, sets the other variables of `m₀` to `1`,
  -- and the remaining variables to `0`
  let ψ : σ → MvPolynomial σ R := fun j =>
    if j ∈ Y then X j + C (-γ j) else if j ∈ m₀.support then 1 else 0
  have hΨ : aeval ψ G = C (G.coeff m₀) * ∏ j ∈ Y, (X j + C (-γ j)) := by
    rw [aeval_def, eval₂_eq, Finset.sum_eq_single m₀]
    · rw [algebraMap_eq]
      congr 1
      calc ∏ i ∈ m₀.support, ψ i ^ m₀ i = ∏ i ∈ m₀.support, ψ i :=
            Finset.prod_congr rfl fun i hi => by
              have h1 := hGmul m₀ hm₀ i
              have h2 := Finsupp.mem_support_iff.1 hi
              rw [show m₀ i = 1 by omega, pow_one]
        _ = ∏ i ∈ Y, ψ i := (Finset.prod_subset hYM fun i hiM hiY => by
            simp only [ψ, hiY, hiM, ite_true, ite_false]).symm
        _ = ∏ j ∈ Y, (X j + C (-γ j)) :=
            Finset.prod_congr rfl fun i hi => by simp only [ψ, hi, ite_true]
    · intro m hm hne
      obtain ⟨i, hi, hiM⟩ : ∃ i ∈ m.support, i ∉ m₀.support := by
        by_contra hcon
        push Not at hcon
        have hsupp : m.support = m₀.support :=
          Finset.eq_of_subset_of_card_le hcon (hmin m hm)
        refine hne (Finsupp.ext fun j => ?_)
        have h1 := hGmul m hm j
        have h2 := hGmul m₀ hm₀ j
        have h3 : m j ≠ 0 ↔ m₀ j ≠ 0 := by
          rw [← Finsupp.mem_support_iff, ← Finsupp.mem_support_iff, hsupp]
        omega
      rw [Finset.prod_eq_zero hi, mul_zero]
      have hiY : i ∉ Y := fun h => hiM (hYM h)
      simp only [ψ, hiY, hiM, ite_false]
      exact zero_pow (Finsupp.mem_support_iff.1 hi)
    · exact fun h => absurd hm₀ h
  -- the same substitution applied to `f`: the identity on `Y`, constants elsewhere
  have hΦ : aeval ψ G = aeval (fun j => ψ j + C (γ j)) f := by
    have h := DFunLike.congr_fun (comp_aeval (R := F)
      (f := fun i => (X i + C (γ i) : MvPolynomial σ R))
      ((aeval ψ : MvPolynomial σ R →ₐ[R] MvPolynomial σ R).restrictScalars F)) f
    simpa [hG, shift] using h
  let b : σ → R := fun j => (if j ∈ m₀.support then 1 else 0) + γ j
  have hpi : ∀ i, aeval (fun j => ψ j + C (γ j)) (p i) = map (algebraMap F R) (p i) := fun i => by
    rw [← aeval_X_eq_map]
    exact aeval_congr_of_mem_supported (hp i) fun j hj => by
      simp only [ψ, mem_coe.1 hj, ite_true, add_assoc, ← C_add, neg_add_cancel, C_0, add_zero]
  have hqi : ∀ i, aeval (fun j => ψ j + C (γ j)) (q i) = C (aeval b (q i)) := fun i => by
    have h := DFunLike.congr_fun (comp_aeval (R := F) (f := b)
      (IsScalarTower.toAlgHom F R (MvPolynomial σ R))) (q i)
    rw [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', algebraMap_eq] at h
    rw [h]
    exact aeval_congr_of_mem_supported (hq i) fun j hj => by
      have hjY : j ∉ Y := fun h => hj (mem_coe.2 h)
      simp only [ψ, b, hjY, ite_false]
      split_ifs <;> simp
  have hkey : ∑ i, C (aeval b (q i)) * map (algebraMap F R) (p i) =
      C (G.coeff m₀) * ∏ j ∈ Y, (X j + C (-γ j)) := by
    rw [← hΨ, hΦ, hfpq, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_mul, hpi, hqi, mul_comm]
  have hcoef : ∀ T ⊆ Y, ∑ i, aeval b (q i) * algebraMap F R ((p i).coeff (ind (Y \ T))) =
      G.coeff m₀ * ∏ j ∈ T, (-γ j) := fun T hT => by
    have h := congrArg (fun P => P.coeff (ind (Y \ T))) hkey
    simp only [coeff_sum, coeff_C_mul, coeff_map] at h
    rwa [coeff_ind_prod_X_add_C sdiff_subset, Finset.sdiff_sdiff_eq_self hT] at h
  -- a nonzero functional on the multilinear monomials in `Y` that kills every `p i`
  let Λ : (Y.powerset → F) →ₗ[F] (Fin w → F) := LinearMap.pi fun i =>
    ∑ T : Y.powerset, (p i).coeff (ind (Y \ (T : Finset σ))) • LinearMap.proj T
  have hker : LinearMap.ker Λ ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
      Fintype.card_coe, Fintype.card_fin, card_powerset, hYk]
    exact hw)
  obtain ⟨c, hc, hc0⟩ := (Submodule.ne_bot_iff _).1 hker
  have hΛ : ∀ i, ∑ T : Y.powerset, (p i).coeff (ind (Y \ (T : Finset σ))) * c T = 0 :=
    fun i => by
      have h := congrFun (LinearMap.mem_ker.1 hc) i
      simpa [Λ, LinearMap.sum_apply] using h
  have hsum : ∑ T : Y.powerset, c T • ∏ j ∈ (T : Finset σ), (-γ j) = 0 := by
    refine (mul_eq_zero.1 ?_).resolve_left (mem_support_iff.1 hm₀)
    calc G.coeff m₀ * ∑ T : Y.powerset, c T • ∏ j ∈ (T : Finset σ), (-γ j)
        = ∑ T : Y.powerset, c T • (G.coeff m₀ * ∏ j ∈ (T : Finset σ), (-γ j)) := by
          rw [mul_sum]
          exact sum_congr rfl fun T _ => mul_smul_comm _ _ _
      _ = ∑ T : Y.powerset, c T •
            ∑ i, aeval b (q i) * algebraMap F R ((p i).coeff (ind (Y \ (T : Finset σ)))) :=
          sum_congr rfl fun T _ => by rw [hcoef T (mem_powerset.1 T.2)]
      _ = ∑ i, algebraMap F R (∑ T : Y.powerset, (p i).coeff (ind (Y \ (T : Finset σ))) * c T) *
            aeval b (q i) := by
          simp only [smul_sum, map_sum, sum_mul]
          rw [sum_comm]
          refine sum_congr rfl fun i _ => sum_congr rfl fun T _ => ?_
          rw [Algebra.smul_def, map_mul]
          ring
      _ = 0 := by simp only [hΛ, map_zero, zero_mul, sum_const_zero]
  refine hc0 (funext fun T => ?_)
  have h := hγ Y hYk (fun T => if h : T ∈ Y.powerset then (-1) ^ T.card * c ⟨T, h⟩ else 0) ?_
    T T.2
  · simpa using h
  · rw [← hsum, ← Finset.sum_coe_sort Y.powerset]
    refine sum_congr rfl fun T _ => ?_
    simp only [T.2, ↓reduceDIte]
    rw [Finset.prod_neg, mul_comm, mul_smul, Algebra.smul_def ((-1 : F) ^ _)]
    simp

end Cslib.Circuits.Arithmetic
