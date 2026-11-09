/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, reduced monomials over a finite field)

public import CslibFrontier.Init
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.Polynomial

/-!
# Reduced monomials over a finite field are independent

Over a finite field `K`, monomials `∏ j, x j ^ e j` whose exponents are all below `Fintype.card K`
are distinct as functions on `σ → K` when their exponent vectors are distinct, and in fact linearly
independent (`FiniteField.linearIndependent_prod_pow`), by the combinatorial Nullstellensatz. So a
combination of such monomials that vanishes at every point has zero coefficients
(`FiniteField.eq_zero_of_forall_sum_mul_prod_pow_eq_zero`).

## Main results

* `FiniteField.linearIndependent_prod_pow`: distinct reduced monomials are linearly independent
  functions.
* `FiniteField.eq_zero_of_forall_sum_mul_prod_pow_eq_zero`: a vanishing combination of distinct
  reduced monomials has zero coefficients.

## References

* Adapted from MassProduction/HighRate/Independence.lean in
  [S. Schlesinger, *Boolean circuit mass production formalization*][Schlesinger2026MassProduction].
-/

@[expose] public section

namespace FiniteField

variable {K : Type*} [Field K] [Fintype K]

/-- Monomials `∏ j, X j ^ e i j` with distinct exponent vectors, all of whose exponents are below
`Fintype.card K`, are linearly independent as functions on `σ → K`. -/
theorem linearIndependent_prod_pow {ι σ : Type*} [Fintype σ] (e : ι → σ → ℕ)
    (he : Function.Injective e) (hlt : ∀ i j, e i j < Fintype.card K) :
    LinearIndependent K fun i (x : σ → K) => ∏ j, x j ^ e i j := by
  classical
  let d : ι → σ →₀ ℕ := fun i => Finsupp.equivFunOnFinite.symm (e i)
  have hd : LinearIndependent K fun i => MvPolynomial.monomial (d i) (1 : K) :=
    (MvPolynomial.basisMonomials σ K).linearIndependent.comp d
      (Finsupp.equivFunOnFinite.symm.injective.comp he)
  have hspan : Submodule.span K (Set.range fun i => MvPolynomial.monomial (d i) (1 : K)) ≤
      MvPolynomial.restrictDegree σ K (Fintype.card K - 1) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, MvPolynomial.mem_restrictDegree]
    intro t ht j
    obtain rfl := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset ht)
    exact Nat.le_sub_one_of_lt (hlt i j)
  -- Evaluation is injective on polynomials of degree below `Fintype.card K` in each variable.
  convert hd.map (f := MvPolynomial.evalₗ K σ) ?_ using 1
  · funext i x
    simp [d, MvPolynomial.eval_monomial, Finsupp.prod_fintype]
  · rw [Submodule.disjoint_def]
    intro p hp hker
    refine MvPolynomial.eq_zero_of_eval_zero_at_prod_finset p (fun _ => Finset.univ)
      (fun j => ?_) fun x _ => by simpa using congrFun (LinearMap.mem_ker.mp hker) x
    rw [Finset.card_univ, MvPolynomial.degreeOf_lt_iff Fintype.card_pos]
    intro t ht
    exact ((MvPolynomial.mem_restrictDegree _ _ _).mp (hspan hp) t ht j).trans_lt
      (Nat.sub_lt Fintype.card_pos one_pos)

/-- **Reduced monomials are independent**: over a finite field `K`, if a combination
`∑ₜ Cₜ ∏ᵥ xᵥ ^ eₜᵥ` of monomials with pairwise distinct exponent vectors, all exponents below
`|K|`, vanishes at every point, then all coefficients vanish. -/
theorem eq_zero_of_forall_sum_mul_prod_pow_eq_zero {σ T : Type*} [Fintype σ] [Fintype T]
    (e : T → σ → ℕ) (he : Function.Injective e) (hlt : ∀ t v, e t v < Fintype.card K)
    (C : T → K) (h : ∀ x : σ → K, ∑ t, C t * ∏ v, x v ^ e t v = 0) (t : T) : C t = 0 := by
  have hli := linearIndependent_prod_pow (K := K) e he hlt
  refine Fintype.linearIndependent_iff.1 hli C ?_ t
  funext x
  rw [Finset.sum_apply, Pi.zero_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  exact h x

end FiniteField
