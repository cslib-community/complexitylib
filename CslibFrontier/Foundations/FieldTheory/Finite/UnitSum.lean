/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate (Mathlib, sums of low-degree polynomials over a finite field)

public import CslibFrontier.Init
public import Mathlib.Algebra.MvPolynomial.Polynomial
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Sums of low-degree polynomials over the units of a finite field

Let `K` be a finite field with `q` elements. A polynomial of degree less than `q - 1` sums to zero
over `K`, so its sum over the units `Kˣ` is minus its value at `0`. Restricting a multivariate
polynomial to the line `u ↦ u • τ + x` turns this into the identity that removes the masks `τ`
from masked evaluations of a low-degree polynomial: the sum over all units `u` of
`p (u • τ + x)` is `-p x`.

This is the algebraic core of the Cook–Mertz Tree Evaluation algorithm, there phrased with powers
of a primitive root of unity of order `q - 1`, which run through the units.

## Main results

* `FiniteField.sum_eval_eq_zero_of_natDegree_lt`: a polynomial of degree less than `q - 1` sums
  to zero over `K`.
* `FiniteField.sum_units_eval`: its sum over `Kˣ` is minus its value at `0`.
* `FiniteField.natDegree_eval₂_line_le`: restricting a multivariate polynomial to a line gives a
  univariate polynomial of degree at most the total degree.
* `FiniteField.eval_eval₂_line`: evaluating the univariate line restriction at `t` evaluates the
  multivariate polynomial at `t • τ + x`.
* `FiniteField.sum_units_eval_mul_add`: for a multivariate polynomial of total degree less than
  `q - 1`, `∑ u : Kˣ, p (u • τ + x) = -p x`.

## References

* [J. Cook and I. Mertz, *Tree Evaluation is in Space O(log n · log log n)*][CookMertz2024],
  Corollary 9 and Lemma 12.
* [O. Goldreich, *On the Cook–Mertz Tree Evaluation procedure*][Goldreich2024TreeEval],
  Equation (3).
-/

@[expose] public section

open Finset Polynomial

namespace FiniteField

variable {K : Type*} [Field K] [Fintype K]

local notation "q" => Fintype.card K

/-- A polynomial of degree less than `q - 1` sums to zero over the field. -/
theorem sum_eval_eq_zero_of_natDegree_lt {g : K[X]} (hg : g.natDegree < q - 1) :
    ∑ x : K, g.eval x = 0 := by
  simp_rw [eval_eq_sum_range, Finset.sum_comm (s := univ), ← Finset.mul_sum]
  exact Finset.sum_eq_zero fun i hi => by
    rw [sum_pow_lt_card_sub_one K i ((Nat.lt_succ_iff.mp (mem_range.mp hi)).trans_lt hg), mul_zero]

/-- A polynomial of degree less than `q - 1` sums over the units to minus its value at `0`. -/
theorem sum_units_eval [DecidableEq K] {g : K[X]} (hg : g.natDegree < q - 1) :
    ∑ u : Kˣ, g.eval (u : K) = -g.eval 0 := by
  have hunits : ∑ u : Kˣ, g.eval (u : K) = ∑ x ∈ univ \ {0}, g.eval x := by
    refine Finset.sum_nbij (fun u => (u : K)) (fun u _ => by simp) ?_ ?_ fun _ _ => rfl
    · exact fun u _ v _ h => Units.ext h
    · intro x hx
      have hx0 : x ≠ 0 := by simpa using hx
      exact ⟨Units.mk0 x hx0, mem_univ _, rfl⟩
  have h := sum_eval_eq_zero_of_natDegree_lt hg
  rw [← sum_sdiff ({0} : Finset K).subset_univ, sum_singleton] at h
  rw [hunits]
  exact eq_neg_of_add_eq_zero_left h

omit [Fintype K] in
/-- Restricting a multivariate polynomial to the line `t ↦ t • τ + x` gives a univariate
polynomial of degree at most the total degree. -/
theorem natDegree_eval₂_line_le {ι : Type*} (p : MvPolynomial ι K) (τ x : ι → K) :
    (p.eval₂ C fun i => C (τ i) * X + C (x i)).natDegree ≤ p.totalDegree := by
  rw [MvPolynomial.eval₂_eq]
  refine natDegree_sum_le_of_forall_le _ _ fun s hs => ?_
  refine (natDegree_C_mul_le _ _).trans <| (natDegree_prod_le _ _).trans ?_
  calc _ ≤ ∑ i ∈ s.support, s i := by
        gcongr with i
        exact natDegree_pow_le.trans <|
          (Nat.mul_le_mul_left (s i) natDegree_linear_le).trans_eq (mul_one _)
    _ ≤ p.totalDegree := by
        simpa [Finsupp.sum] using MvPolynomial.le_totalDegree hs

omit [Fintype K] in
/-- Evaluating the univariate restriction of `p` to the line `t ↦ t • τ + x` at `t` evaluates `p`
at `i ↦ t * τ i + x i`. -/
theorem eval_eval₂_line {ι : Type*} (p : MvPolynomial ι K) (τ x : ι → K) (t : K) :
    (p.eval₂ C fun i => C (τ i) * X + C (x i)).eval t =
      MvPolynomial.eval (fun i => t * τ i + x i) p := by
  have hC : (evalRingHom t).comp C = RingHom.id K := by ext; simp
  simp only [MvPolynomial.polynomial_eval_eval₂, hC, eval_add, eval_mul, eval_C, eval_X,
    mul_comm (τ _)]
  rfl

/-- **Unmasking low-degree polynomials.** If `p` has total degree less than `q - 1`, then summing
the masked evaluations `p (u • τ + x)` over all units `u` gives `-p x`, for every mask `τ`. -/
theorem sum_units_eval_mul_add [DecidableEq K] {ι : Type*} {p : MvPolynomial ι K}
    (hp : p.totalDegree < q - 1) (τ x : ι → K) :
    ∑ u : Kˣ, MvPolynomial.eval (fun i => (u : K) * τ i + x i) p = -MvPolynomial.eval x p := by
  let g : K[X] := p.eval₂ C fun i => C (τ i) * X + C (x i)
  have hg (t : K) : g.eval t = MvPolynomial.eval (fun i => t * τ i + x i) p :=
    eval_eval₂_line p τ x t
  have h0 : MvPolynomial.eval x p = g.eval 0 := by simp only [hg, zero_mul, zero_add]
  simp_rw [h0, ← hg]
  exact sum_units_eval ((natDegree_eval₂_line_le p τ x).trans_lt hp)

end FiniteField
