/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.MvPolynomial.Supported
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs

/-!
# Read-once oblivious algebraic branching programs

A read-once oblivious algebraic branching program (ROABP) of width `w` reads the variables one
at a time, in a fixed order: it is a product of `w × w` matrices, the `i`-th with entries
univariate polynomials in the variable `X i`, and it computes an entry of the product
(`roabpProd`). A polynomial may be computed by such programs in every order of the variables
(`IsAnyOrderROABP`) or in some order, with layers of bounded degree (`IsROABP`).

The coefficient of a monomial in an entry of the product is the corresponding entry of the
product of the coefficient matrices of the layers (`coeff_roabpProd`). So the coefficients of a
program are the values of a product of matrices that depend on one exponent each, which is how
Nisan's characterisation and the hitting sets for these programs use them.

## Main definitions

* `roabpProd`: the matrix computed by a program that reads the variables of a list.
* `IsAnyOrderROABP`: computed by width-`w` programs in every order of the variables.
* `IsROABP`: computed by a width-`w` program in some order, with layer entries of degree at most
  `δ`.
* `layerCoeff`: the coefficient matrices of a layer.

## Main results

* `roabpProd_mem_supported`: the entries are polynomials in the variables that are read.
* `coeff_roabpProd`: coefficients of a program as entries of a product of coefficient matrices.
* `coeff_roabpProd_eq_zero`: a monomial with a variable that is not read has coefficient zero.
* `eval_roabpProd`: values of a program as entries of a product of evaluated layers.

## References

* [N. Nisan, *Lower bounds for non-commutative computation*][Nisan1991]
* [M. Agrawal, R. Gurjar, A. Korwar, N. Saxena, *Hitting-sets for ROABP and sum of
  set-multilinear circuits*][AgrawalGurjarKorwarSaxena2015], §3, where the product of the
  layers is treated as a polynomial over the matrix algebra
-/

public section

open scoped Polynomial

namespace Cslib.Circuits.Arithmetic

open Finset MvPolynomial

variable {F : Type*} [Field F] {n w : ℕ}

open Polynomial in
/-- The matrix computed by a read-once oblivious branching program of width `w` that reads the
variables in the order of the list `l`: the product of the matrices `M i`, with entries
univariate polynomials evaluated at the variable `X i`. -/
@[expose] noncomputable def roabpProd (M : Fin n → Matrix (Fin w) (Fin w) F[X]) (l : List (Fin n)) :
    Matrix (Fin w) (Fin w) (MvPolynomial (Fin n) F) :=
  (l.map fun i => (M i).map (Polynomial.aeval (X i : MvPolynomial (Fin n) F))).prod

open Polynomial in
/-- `f` is computed by a read-once oblivious branching program of width `w` in every order of
the variables: for every list of all the variables without repetition, `f` is an entry of the
product of some `w × w` matrices of univariate polynomials read in that order. The matrices may
depend on the order. -/
@[expose] def IsAnyOrderROABP (w : ℕ) (f : MvPolynomial (Fin n) F) : Prop :=
  ∀ l : List (Fin n), l.Nodup → (∀ i, i ∈ l) →
    ∃ (M : Fin n → Matrix (Fin w) (Fin w) F[X]) (s t : Fin w), f = roabpProd M l s t

open Polynomial in
/-- The entries of a branching program that reads the variables of a list in a set `S` are
polynomials in the variables of `S`. -/
theorem roabpProd_mem_supported (M : Fin n → Matrix (Fin w) (Fin w) F[X])
    {S : Set (Fin n)} : ∀ l : List (Fin n), (∀ i ∈ l, i ∈ S) → ∀ s t : Fin w,
      roabpProd M l s t ∈ supported F S
  | [], _, s, t => by
    rw [roabpProd, List.map_nil, List.prod_nil, Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  | i :: l, hl, s, t => by
    rw [roabpProd, List.map_cons, List.prod_cons, Matrix.mul_apply]
    refine sum_mem fun k _ => mul_mem ?_
      (roabpProd_mem_supported M l (fun j hj => hl j (List.mem_cons_of_mem _ hj)) k t)
    have hX : (X i : MvPolynomial (Fin n) F) ∈ supported F S :=
      Algebra.subset_adjoin ⟨i, hl i List.mem_cons_self, rfl⟩
    rw [Matrix.map_apply, ← Subtype.coe_mk (X i) hX, ← Polynomial.aeval_subalgebra_coe]
    exact Subtype.coe_prop _

/-- `f` is computed by a read-once oblivious branching program of width `w` in some order of
the variables, with layers of degree at most `δ`: `f` is an entry of the product, in the order
of a list `l` without repetition, of `w × w` matrices of univariate polynomials of degree at
most `δ`. The list need not contain every variable. -/
@[expose] def IsROABP (w δ : ℕ) (f : MvPolynomial (Fin n) F) : Prop :=
  ∃ (l : List (Fin n)) (M : Fin n → Matrix (Fin w) (Fin w) F[X]) (s t : Fin w),
    l.Nodup ∧ (∀ i s t, (M i s t).natDegree ≤ δ) ∧ f = roabpProd M l s t

/-- The matrix of coefficients of `X ^ e` in the layer of the variable `i`. -/
@[expose] def layerCoeff (M : Fin n → Matrix (Fin w) (Fin w) F[X]) (i : Fin n) (e : ℕ) :
    Matrix (Fin w) (Fin w) F :=
  (M i).map fun q => q.coeff e

/-- The coefficient of a monomial in the product of a univariate polynomial in `X i` and a
polynomial without the variable `X i`. -/
theorem coeff_aeval_X_mul_of_mem_supported {S : Set (Fin n)} {i : Fin n} (hi : i ∉ S)
    (p : F[X]) {q : MvPolynomial (Fin n) F} (hq : q ∈ supported F S) (m : Fin n →₀ ℕ) :
    (Polynomial.aeval (X i : MvPolynomial (Fin n) F) p * q).coeff m =
      p.coeff (m i) * q.coeff (m.erase i) := by
  classical
  have h0 : ∀ d : Fin n →₀ ℕ, d i ≠ 0 → q.coeff d = 0 := fun d hd => by
    by_contra hne
    exact hi (mem_supported.1 hq (mem_coe.2 ((mem_vars_iff_mem_support i).2
      ⟨d, mem_support_iff.2 hne, Finsupp.mem_support_iff.2 hd⟩)))
  induction p using Polynomial.induction_on' with
  | add p₁ p₂ h₁ h₂ => simp [add_mul, h₁, h₂]
  | monomial e a =>
    rw [Polynomial.aeval_monomial, algebraMap_eq, C_mul_X_pow_eq_monomial, coeff_monomial_mul',
      Polynomial.coeff_monomial]
    by_cases he : e = m i
    · subst he
      have hle : Finsupp.single i (m i) ≤ m := Finsupp.single_le_iff.2 le_rfl
      have herase : m - Finsupp.single i (m i) = m.erase i := by
        ext j
        by_cases hj : j = i
        · subst hj
          simp
        · simp [Finsupp.erase_ne hj, Finsupp.single_eq_of_ne hj]
      simp [hle, herase]
    · by_cases hle : Finsupp.single i e ≤ m
      · have hlt : m i - e ≠ 0 := by
          have h := Finsupp.single_le_iff.1 hle
          omega
        have hq0 : q.coeff (m - Finsupp.single i e) = 0 :=
          h0 _ (by rwa [Finsupp.tsub_apply, Finsupp.single_eq_same])
        simp [he, hq0]
      · simp [he, hle]

/-- The coefficient of a monomial in an entry of a branching program is the entry of the product
of the coefficient matrices of the layers at the exponents of the monomial. -/
theorem coeff_roabpProd (M : Fin n → Matrix (Fin w) (Fin w) F[X]) :
    ∀ {l : List (Fin n)}, l.Nodup → ∀ m : Fin n →₀ ℕ, (∀ i ∉ l, m i = 0) → ∀ s t : Fin w,
      (roabpProd M l s t).coeff m = (l.map fun i => layerCoeff M i (m i)).prod s t
  | [], _, m, hm, s, t => by
    have hm0 : m = 0 := Finsupp.ext fun i => hm i (List.not_mem_nil)
    rw [roabpProd, List.map_nil, List.prod_nil, List.map_nil, List.prod_nil, hm0,
      Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  | i :: l, hl, m, hm, s, t => by
    have hil : i ∉ l := (List.nodup_cons.1 hl).1
    have hm' : ∀ j ∉ l, (m.erase i) j = 0 := fun j hj => by
      by_cases hji : j = i
      · rw [hji, Finsupp.erase_same]
      · rw [Finsupp.erase_ne hji]
        exact hm j fun h => (List.mem_cons.1 h).elim hji hj
    have hmap : (l.map fun j => layerCoeff M j ((m.erase i) j)) =
        l.map fun j => layerCoeff M j (m j) :=
      List.map_congr_left fun j hj => by
        rw [Finsupp.erase_ne fun h : j = i => hil (h ▸ hj)]
    have hprod : roabpProd M (i :: l) = (M i).map (Polynomial.aeval (X i)) * roabpProd M l := by
      rw [roabpProd, List.map_cons, List.prod_cons, roabpProd]
    rw [hprod, List.map_cons, List.prod_cons, Matrix.mul_apply, Matrix.mul_apply, coeff_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [Matrix.map_apply, coeff_aeval_X_mul_of_mem_supported (S := {j | j ∈ l}) hil _
      (roabpProd_mem_supported M l (fun j hj => hj) k t),
      coeff_roabpProd M (List.nodup_cons.1 hl).2 _ hm' k t, hmap]
    rfl

/-- A monomial with a variable outside the list has coefficient zero in a branching program that
reads the variables of the list. -/
theorem coeff_roabpProd_eq_zero (M : Fin n → Matrix (Fin w) (Fin w) F[X]) (l : List (Fin n))
    {m : Fin n →₀ ℕ} {i : Fin n} (hi : i ∉ l) (hm : m i ≠ 0) (s t : Fin w) :
    (roabpProd M l s t).coeff m = 0 := by
  by_contra hne
  have hsup := roabpProd_mem_supported M l (S := {j | j ∈ l}) (fun j hj => hj) s t
  exact hi (mem_supported.1 hsup
    (mem_coe.2 ((mem_vars_iff_mem_support i).2
      ⟨m, mem_support_iff.2 hne, Finsupp.mem_support_iff.2 hm⟩)))

/-- Evaluating an entry of a branching program at a point evaluates each layer at the coordinate
of its variable. -/
theorem eval_roabpProd (M : Fin n → Matrix (Fin w) (Fin w) F[X]) (l : List (Fin n))
    (a : Fin n → F) (s t : Fin w) :
    eval a (roabpProd M l s t) =
      (l.map fun i => (M i).map (Polynomial.eval (a i))).prod s t := by
  have h : (eval a).mapMatrix (roabpProd M l) =
      (l.map fun i => (M i).map (Polynomial.eval (a i))).prod := by
    rw [roabpProd, map_list_prod, List.map_map]
    refine congrArg List.prod (List.map_congr_left fun i _ => ?_)
    ext s t
    have hC : (eval a).comp C = RingHom.id F := RingHom.ext fun r => eval_C r
    simp [Polynomial.aeval_def, Polynomial.hom_eval₂, hC, Polynomial.eval₂_id]
  exact congrFun (congrFun h s) t

end Cslib.Circuits.Arithmetic
