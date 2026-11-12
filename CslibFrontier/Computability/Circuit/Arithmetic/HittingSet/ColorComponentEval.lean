/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.ColorPartEval
public import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Evaluating a colour component of a polynomial

The values of the component `colorComponent c ε G` of colour degree `ε` of a polynomial `G` are
reached from values of `G` itself, over a field of characteristic zero: if the component does
not vanish at a point `x`, then `G` does not vanish at one of the points obtained from `x` by
scaling the variables of colour `i` by `z * y i`, for natural numbers `y i ≤ ε i` and an element
`z` of a set with more than `G.totalDegree` elements
(`exists_eval_ne_zero_of_eval_colorComponent_ne_zero`).

The case `ε = (1, …, 1)` is [Shpilka2026, Lemma 3.2]
(`exists_eval_ne_zero_of_eval_colorPart_ne_zero`), proved by inclusion–exclusion. The statement
for a general colour degree, and its proof by finite differences, are not from a source.
Scaling the variables of colour `i` by a new variable `yᵢ` turns `G` into a polynomial `T` in `y`
whose coefficient at `ε` is the value at `x` of the component (`coeff_aeval_monomial`). Substituting
`kᵢ * z` for `yᵢ` and taking the `ε i`-th forward difference at `0` in every `kᵢ` gives a
polynomial in `z` whose coefficient at `z ^ ∑ i, ε i` is `(∏ i, (ε i)!) * T.coeff ε`
(`coeff_sum_smul_aeval_C_mul_X`): the `n`-th forward difference of `k ↦ k ^ j` at `0` is `0` for
`j < n` and `n!` for `j = n`.

## Main results

* `weight_colorWeight_apply`: the colour degree of a monomial, coordinatewise.
* `coeff_sum_smul_aeval_C_mul_X`: a coefficient of a polynomial in `r` variables as a
  coefficient of an iterated forward difference of its restrictions to lines.
* `exists_eval_ne_zero_of_eval_colorComponent_ne_zero`: a nonzero value of a colour component
  gives a nonzero value of the polynomial.

## References

* [A. Shpilka, *Polynomial-size hitting sets for multilinear any-order read-once algebraic
  branching programs and for set-multilinear depth-3 circuits with constant-size variable
  sets*][Shpilka2026], §3, Lemma 3.2, p. 7 (unrefereed preprint), for the colour degree
  `(1, …, 1)`
-/

public section

namespace Cslib.Circuits.Arithmetic

open MvPolynomial

variable {σ F : Type*} {r : ℕ}

/-- The colour degree of a monomial, coordinatewise: its coordinate at the colour `i` is the
degree of the monomial in the variables of colour `i`. -/
theorem weight_colorWeight_apply [DecidableEq (Fin r)] (c : σ → Fin r) (d : σ →₀ ℕ)
    (i : Fin r) :
    Finsupp.weight (colorWeight c) d i = ∑ v ∈ d.support with c v = i, d v := by
  rw [Finsupp.weight_apply, Finsupp.sum, Finsupp.finsetSum_apply, Finset.sum_filter]
  exact Finset.sum_congr rfl fun v _ => by simp [colorWeight, Finsupp.single_apply]

/-- The `n`-th forward difference at `0` of `k ↦ k ^ j`, for `j ≤ n`, as an alternating sum. -/
private theorem sum_neg_one_pow_mul_choose_mul_pow [CommRing F] {j n : ℕ} (h : j ≤ n) :
    ∑ k ∈ Finset.range (n + 1), (-1 : F) ^ (n - k) * (n.choose k : F) * (k : F) ^ j =
      if j = n then (n.factorial : F) else 0 := by
  have key := fwdDiff_iter_eq_sum_shift (1 : F) (fun a : F => a ^ j) n 0
  simp only [zero_add, nsmul_eq_mul, mul_one, zsmul_eq_mul, Int.cast_mul, Int.cast_pow,
    Int.cast_neg, Int.cast_one, Int.cast_natCast] at key
  rw [← key]
  obtain rfl | hlt := h.eq_or_lt
  · simp [fwdDiff_iter_eq_factorial]
  · simp [fwdDiff_iter_pow_eq_zero_of_lt hlt, hlt.ne]

/-- The coefficient at `ε` of a polynomial `T` in `r` variables, times `∏ i, (ε i)!`, is the
coefficient of `z ^ ∑ i, ε i` in the iterated forward difference at `0`, of order `ε i` in
`y i`, of the univariate polynomials `T (y i * z)`. -/
theorem coeff_sum_smul_aeval_C_mul_X [CommRing F] (ε : Fin r →₀ ℕ)
    (T : MvPolynomial (Fin r) F) :
    (∑ y ∈ Fintype.piFinset fun i => Finset.range (ε i + 1),
      (∏ i, (-1 : F) ^ (ε i - y i) * ((ε i).choose (y i) : F)) •
        aeval (fun i => Polynomial.C (y i : F) * Polynomial.X) T).coeff (∑ i, ε i) =
      (∏ i, ((ε i).factorial : F)) * T.coeff ε := by
  classical
  induction T using MvPolynomial.induction_on' with
  | monomial e a =>
    have hy (y : Fin r → ℕ) :
        aeval (fun i => Polynomial.C (y i : F) * Polynomial.X) (monomial e a) =
          Polynomial.C (a * ∏ i, (y i : F) ^ e i) * Polynomial.X ^ ∑ i, e i := by
      rw [aeval_monomial, Finsupp.prod_fintype _ _ fun _ => pow_zero _]
      simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, map_mul,
        map_prod, map_pow, mul_assoc]
      rfl
    simp only [hy, Polynomial.finsetSum_coeff, Polynomial.coeff_smul,
      Polynomial.coeff_C_mul_X_pow, smul_eq_mul, coeff_monomial]
    by_cases hD : ∑ i, ε i = ∑ i, e i
    · have hmul (y : Fin r → ℕ) :
          (∏ i, (-1 : F) ^ (ε i - y i) * ((ε i).choose (y i) : F)) *
            (a * ∏ i, (y i : F) ^ e i) =
          a * ∏ i, (-1 : F) ^ (ε i - y i) * ((ε i).choose (y i) : F) * (y i : F) ^ e i := by
        simp only [Finset.prod_mul_distrib]
        ring
      simp only [hD, ↓reduceIte, hmul]
      rw [← Finset.mul_sum, ← Finset.prod_univ_sum (fun i => Finset.range (ε i + 1))
        fun i k => (-1 : F) ^ (ε i - k) * ((ε i).choose k : F) * (k : F) ^ e i]
      by_cases he : e = ε
      · subst he
        simp only [sum_neg_one_pow_mul_choose_mul_pow le_rfl, ↓reduceIte]
        exact mul_comm _ _
      · obtain ⟨i, hi⟩ : ∃ i, e i < ε i := by
          by_contra! hle
          exact he (Finsupp.ext fun i =>
            ((Finset.sum_eq_sum_iff_of_le fun i _ => hle i).1 hD i (Finset.mem_univ i)).symm)
        rw [Finset.prod_eq_zero (Finset.mem_univ i)
          (by rw [sum_neg_one_pow_mul_choose_mul_pow hi.le]; simp [hi.ne])]
        simp [he]
    · have he : e ≠ ε := by
        rintro rfl
        exact hD rfl
      simp [hD, he]
  | add p q hp hq =>
    simp only [map_add, smul_add, Finset.sum_add_distrib, Polynomial.coeff_add, hp, hq]
    rw [← mul_add]
    rfl

/-- If the component of colour degree `ε` of `G` does not vanish at `x`, over a field of
characteristic zero, then `G` does not vanish at one of the points obtained from `x` by scaling
the variables of colour `i` by `z * y i`, for natural numbers `y i ≤ ε i` and an element `z` of
`Λ`, a set with more than `G.totalDegree` elements. The case `ε = (1, …, 1)` is
[Shpilka2026, Lemma 3.2]. -/
theorem exists_eval_ne_zero_of_eval_colorComponent_ne_zero [Field F] [CharZero F]
    (c : σ → Fin r) (ε : Fin r →₀ ℕ) {G : MvPolynomial σ F} {x : σ → F} {Λ : Finset F}
    (hΛ : G.totalDegree < Λ.card) (hx : MvPolynomial.eval x (colorComponent c ε G) ≠ 0) :
    ∃ z ∈ Λ, ∃ y : Fin r → ℕ, (∀ i, y i ≤ ε i) ∧
      MvPolynomial.eval (fun v => z * (y (c v) : F) * x v) G ≠ 0 := by
  by_contra! h
  let P (y : Fin r → ℕ) : Polynomial F :=
    aeval (fun v => Polynomial.C (x v) * (Polynomial.C (y (c v) : F) * Polynomial.X)) G
  have hP (y : Fin r → ℕ) : P y = aeval (fun i => Polynomial.C (y i : F) * Polynomial.X)
      (aeval (fun v => monomial (colorWeight c v) (x v)) G) := by
    rw [← AlgHom.comp_apply, comp_aeval]
    refine congrArg (fun f => aeval f G) (funext fun v => ?_)
    simp [colorWeight, aeval_monomial]
  have heval (y : Fin r → ℕ) (z : F) :
      (P y).eval z = eval (fun v => z * (y (c v) : F) * x v) G := by
    rw [← Polynomial.coe_aeval_eq_eval, ← AlgHom.comp_apply, comp_aeval]
    refine congrArg (fun f => eval f G) (funext fun v => ?_)
    simp only [map_mul, Polynomial.aeval_C, Polynomial.aeval_X, Algebra.algebraMap_self,
      RingHom.id_apply]
    ring
  have hQ : ∑ y ∈ Fintype.piFinset fun i => Finset.range (ε i + 1),
      (∏ i, (-1 : F) ^ (ε i - y i) * ((ε i).choose (y i) : F)) • P y = 0 := by
    refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ Λ (fun z hz => ?_)
      (lt_of_le_of_lt ?_ hΛ)
    · rw [Polynomial.eval_finsetSum]
      refine Finset.sum_eq_zero fun y hy => ?_
      rw [Polynomial.eval_smul, heval, h z hz y fun i =>
        Nat.lt_succ_iff.1 (Finset.mem_range.1 (Fintype.mem_piFinset.1 hy i)), smul_zero]
    · refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun y _ =>
        (Polynomial.natDegree_smul_le _ _).trans ?_
      simpa using aeval_natDegree_le (n := 1) G le_rfl _ fun v =>
        (Polynomial.natDegree_C_mul_le _ _).trans
          ((Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le)
  refine hx ?_
  have hcoeff :=
    coeff_sum_smul_aeval_C_mul_X ε (aeval (fun v => monomial (colorWeight c v) (x v)) G)
  simp only [← hP, hQ, Polynomial.coeff_zero, coeff_aeval_monomial] at hcoeff
  exact (mul_eq_zero.1 hcoeff.symm).resolve_left
    (Finset.prod_ne_zero_iff.2 fun i _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _))

end Cslib.Circuits.Arithmetic
