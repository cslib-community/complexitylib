/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.Code.SudanInterpolant
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.LinearAlgebra.Lagrange

/-!
# Reed–Solomon list decoding with a hint

List decoding a Reed–Solomon codeword from a small fraction of agreements returns several
candidate polynomials. In local list decoding of Reed–Muller codes [SudanTrevisanVadhan2001] the
right candidate is singled out by its value `a = P(τ)` at one further point, supplied as advice.
This module computes the value `P(0)` of that candidate from the received word, `τ` and `a`
alone, with linear algebra and Newton iteration, and no root finding or factoring.

Let `Q` be the Sudan interpolant of least `Y`-degree of the received word
(`Cslib.Code.Sudan.interpolant`). If `P` has degree at most `d` and more than `D` agreements, then
`Q = (Y - P) * S` with `S(X, P(X)) ≠ 0` of degree at most `D - d`
(`Cslib.Code.Sudan.exists_eq_mul_eval_ne_zero`), so for all but `D - d` points `τ` the root `P` is
simple at `(τ, P(τ))`: `∂Q/∂Y (τ, P(τ)) = S(τ, P(τ)) ≠ 0`. Then the Taylor coefficients of `P` at
`τ` are determined one at a time by Newton's (Hensel's) rule: if `A` has degree less than
`k ≤ d` and agrees with `P(X + τ)` below degree `k`, then the coefficient of `X ^ k` in
`P(X + τ)` is `-[X ^ k] Q(X + τ, A(X)) / ∂Q/∂Y (τ, a)` (`Cslib.Code.henselCoeff_eq`). The
coefficient `[X ^ k] Q(X + τ, A(X))` is a fixed linear combination of the values
`Q(s + τ, A(s))` for `s ∈ F` (`Cslib.Code.sum_coeffWeight_mul_eval`), because this polynomial has
degree at most `D < |F|`. So the whole computation `Cslib.Code.hintDecode` is an arithmetic
computation on the received word, the hint and fixed constants, with no other branching than the
tests for zero in the elimination; the decoded value is correct for all but `D - d` of the hint
points (`Cslib.Code.card_hintDecode_ne_le`).

## Main definitions

* `Cslib.Code.coeffWeight`: the weights extracting a coefficient from the values on all of `F`.
* `Cslib.Code.henselCoeff`: the coefficient chosen by one Newton step.
* `Cslib.Code.henselTrunc`: the Newton iteration from a hint.
* `Cslib.Code.henselSeq`: the coefficients chosen by the Newton iteration.
* `Cslib.Code.henselValue`: the value at `0` of the lifted root.
* `Cslib.Code.hintDecode`: Sudan decoding with a hint.

## Main results

* `Cslib.Code.sum_coeffWeight_mul_eval`: coefficients from values.
* `Cslib.Code.henselValue_eq`: Newton iteration recovers a simple root of degree at most `d`.
* `Cslib.Code.card_hintDecode_ne_le`: decoding with a hint is correct at all but `D - d` hint
  points.

## References

* [M. Sudan, L. Trevisan, S. Vadhan, *Pseudorandom generators without the XOR lemma*]
  [SudanTrevisanVadhan2001]
* [M. Sudan, *Decoding of Reed Solomon codes beyond the error-correction bound*][Sudan1997]
-/

@[expose] public section

namespace Cslib.Code

open Finset Polynomial
open scoped Polynomial.Bivariate

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ### Coefficients from values -/

/-- The weights extracting the coefficient of `X ^ k` from the values at all points of `F`: the
coefficients of the Lagrange basis polynomials of `F`. -/
noncomputable def coeffWeight (k : ℕ) (s : F) : F :=
  (Lagrange.basis (univ : Finset F) id s).coeff k

/-- **Coefficients from values.** A polynomial of degree less than `|F|` has coefficient
`∑ s, coeffWeight k s * R(s)` at `X ^ k`. -/
theorem sum_coeffWeight_mul_eval {R : F[X]} (hR : R.natDegree < Fintype.card F) (k : ℕ) :
    ∑ s, coeffWeight k s * R.eval s = R.coeff k := by
  have hdeg : R.degree < #(univ : Finset F) := by
    rw [card_univ]
    exact degree_le_natDegree.trans_lt (by exact_mod_cast hR)
  conv_rhs => rw [Lagrange.eq_interpolate (s := univ) (v := id) (Set.injOn_id _) hdeg]
  rw [Lagrange.interpolate_apply, finsetSum_coeff]
  refine sum_congr rfl fun s _ => ?_
  rw [coeff_C_mul, coeffWeight, mul_comm]
  rfl

/-! ### Newton iteration -/

/-- The polynomial `Q(X + τ, A(X))`. -/
private noncomputable def shiftEval (Q : F[X][Y]) (τ : F) (A : F[X]) : F[X] :=
  (Q.map (taylorAlgHom τ : F[X] →+* F[X])).eval A

omit [Fintype F] [DecidableEq F] in
/-- The value of `Q(X + τ, A(X))` at `s` is `Q(s + τ, A(s))`. -/
private theorem eval_shiftEval (Q : F[X][Y]) (τ : F) (A : F[X]) (s : F) :
    (shiftEval Q τ A).eval s = Q.evalEval (s + τ) (A.eval s) := by
  rw [shiftEval, eval_map, ← coe_evalRingHom, hom_eval₂, coe_evalRingHom]
  have : (evalRingHom s).comp (taylorAlgHom τ : F[X] →+* F[X]) = evalRingHom (s + τ) :=
    RingHom.ext fun p => by simp [taylor_eval]
  rw [this, ← eval₂_evalRingHom]

/-- The coefficient chosen by one Newton step: `-[X ^ k] Q(X + τ, A(X)) / λ`, computed from the
values of `Q(X + τ, A(X))` on `F`. -/
noncomputable def henselCoeff (Q : F[X][Y]) (τ lam : F) (A : F[X]) (k : ℕ) : F :=
  -(∑ s, coeffWeight k s * Q.evalEval (s + τ) (A.eval s)) / lam

/-- **Newton iteration from a hint.** Starting from the constant `a`, the step to `k + 1` adds the
monomial `henselCoeff Q τ lam A (k + 1) * X ^ (k + 1)`. -/
noncomputable def henselTrunc (Q : F[X][Y]) (τ a lam : F) : ℕ → F[X]
  | 0 => C a
  | k + 1 => henselTrunc Q τ a lam k +
      C (henselCoeff Q τ lam (henselTrunc Q τ a lam k) (k + 1)) * X ^ (k + 1)

/-- The coefficients chosen by the Newton iteration: `a` and then the successive steps. -/
noncomputable def henselSeq (Q : F[X][Y]) (τ a lam : F) : ℕ → F
  | 0 => a
  | k + 1 => henselCoeff Q τ lam (henselTrunc Q τ a lam k) (k + 1)

/-- The iterate to degree `k` is the polynomial with the first `k + 1` chosen coefficients. -/
theorem henselTrunc_eq_sum (Q : F[X][Y]) (τ a lam : F) (k : ℕ) :
    henselTrunc Q τ a lam k = ∑ i ∈ range (k + 1), C (henselSeq Q τ a lam i) * X ^ i := by
  induction k with
  | zero => simp [henselTrunc, henselSeq]
  | succ k ih =>
    rw [henselTrunc, sum_range_succ, ← ih]
    rfl

/-- The value at `s` of the iterate to degree `k`. -/
theorem eval_henselTrunc (Q : F[X][Y]) (τ a lam : F) (k : ℕ) (s : F) :
    (henselTrunc Q τ a lam k).eval s = ∑ i ∈ range (k + 1), henselSeq Q τ a lam i * s ^ i := by
  simp [henselTrunc_eq_sum, eval_finsetSum]

/-- The value at `0` of the root lifted from the hint `a` at `τ`, to degree `d`. -/
noncomputable def henselValue (Q : F[X][Y]) (τ a : F) (d : ℕ) : F :=
  (henselTrunc Q τ a ((derivative Q).evalEval τ a) d).eval (-τ)

omit [Fintype F] [DecidableEq F] in
/-- Substituting a polynomial of degree at most `d` into `Q(X + τ, Y)` gives degree at most `D`
when `Q` has `(1, d)`-weighted degree at most `D`. -/
private theorem natDegree_shiftEval_le {d D : ℕ} {Q : F[X][Y]}
    (hQ : Sudan.WeightedDegreeLE d D Q) (τ : F) {A : F[X]}
    (hA : A.natDegree ≤ d) : (shiftEval Q τ A).natDegree ≤ D := by
  refine (Sudan.WeightedDegreeLE.natDegree_eval_le ?_ hA)
  intro a b hab
  rw [coeff_map] at hab
  have hQb : Q.coeff b ≠ 0 := fun h => hab (by simp [h])
  have ha : a ≤ (Q.coeff b).natDegree := by
    have := le_natDegree_of_ne_zero hab
    rwa [show ((taylorAlgHom τ : F[X] →+* F[X]) (Q.coeff b)) = taylor τ (Q.coeff b) from rfl,
      natDegree_taylor] at this
  have := hQ _ b (leadingCoeff_ne_zero.2 hQb)
  omega

omit [Fintype F] [DecidableEq F] in
/-- The degree-`(k + 1)` coefficient of
`(Q.map (taylorAlgHom τ)).derivative.eval A * (X ^ (k + 1) * R)` is `∂Q/∂Y (τ, P(τ))` times the
degree-`(k + 1)` coefficient of `P(X + τ)`. -/
private theorem coeff_derivative_eval_mul_X_pow_mul (Q : F[X][Y]) {P A R : F[X]} {τ : F} {k : ℕ}
    (hA : A.natDegree ≤ k) (hAP0 : A.coeff 0 = (taylor τ P).coeff 0)
    (hPA : taylor τ P = A + X ^ (k + 1) * R) :
    (((Q.map (taylorAlgHom τ : F[X] →+* F[X])).derivative.eval A) *
        (X ^ (k + 1) * R)).coeff (k + 1) =
      (derivative Q).evalEval τ (P.eval τ) * (taylor τ P).coeff (k + 1) := by
  set φ := (taylorAlgHom τ : F[X] →+* F[X])
  set G := Q.map φ
  rw [show G.derivative.eval A * (X ^ (k + 1) * R) = X ^ (k + 1) * (G.derivative.eval A * R) by
    ring, coeff_X_pow_mul', ite_eq_left le_rfl, Nat.sub_self, mul_coeff_zero,
    coeff_zero_eq_eval_zero]
  have h1 : (G.derivative.eval A).eval 0 = (derivative Q).evalEval τ (P.eval τ) := by
    rw [derivative_map, show (Q.derivative.map φ).eval A = shiftEval Q.derivative τ A from rfl,
      eval_shiftEval, zero_add, ← coeff_zero_eq_eval_zero, hAP0, taylor_coeff_zero]
  have h2 : R.coeff 0 = (taylor τ P).coeff (k + 1) := by
    have := congrArg (coeff · (k + 1)) hPA
    simp only [coeff_add, coeff_X_pow_mul', ite_eq_left le_rfl, Nat.sub_self] at this
    rw [this, coeff_eq_zero_of_natDegree_lt (p := A) (by omega), zero_add]
  rw [h1, h2]

/-- **One Newton step.** Let `Q(X, P(X)) = 0` with `P` of degree at most `d`, let `Q` have
`(1, d)`-weighted degree at most `D < |F|`, and let `λ = ∂Q/∂Y (τ, P(τ)) ≠ 0`. If `A` has
degree at most `k < d` and agrees with `P(X + τ)` below degree `k + 1`, then the Newton step
returns the coefficient of `X ^ (k + 1)` in `P(X + τ)`. -/
theorem henselCoeff_eq {d D : ℕ} {Q : F[X][Y]}
    (hQ : Sudan.WeightedDegreeLE d D Q) (hD : D < Fintype.card F)
    {P : F[X]} (hQP : Q.eval P = 0) {τ : F}
    (hlam : (derivative Q).evalEval τ (P.eval τ) ≠ 0) {A : F[X]} {k : ℕ} (hk : k < d)
    (hA : A.natDegree ≤ k) (hAP : ∀ i ≤ k, A.coeff i = (taylor τ P).coeff i) :
    henselCoeff Q τ ((derivative Q).evalEval τ (P.eval τ)) A (k + 1) =
      (taylor τ P).coeff (k + 1) := by
  set lam := (derivative Q).evalEval τ (P.eval τ)
  set φ := (taylorAlgHom τ : F[X] →+* F[X])
  set G := Q.map φ
  -- `P(X + τ) = A + X ^ (k + 1) * R`
  obtain ⟨R, hR⟩ : X ^ (k + 1) ∣ taylor τ P - A := X_pow_dvd_iff.2 fun i hi => by
    rw [coeff_sub, hAP i (Nat.lt_succ_iff.1 hi), sub_self]
  have hPA : taylor τ P = A + X ^ (k + 1) * R := by rw [← hR]; ring
  have hG : G.eval (taylor τ P) = 0 := by
    change (Q.map φ).eval (φ P) = 0
    rw [eval_map, eval₂_hom, hQP, map_zero]
  obtain ⟨c, hc⟩ := exists_mul_sq_add_linear_part_eq_eval_add G A (X ^ (k + 1) * R)
  rw [← hPA, hG] at hc
  have hcoeff := congrArg (coeff · (k + 1)) hc
  simp only [coeff_add, coeff_zero] at hcoeff
  -- the quadratic term vanishes at degree `k + 1`
  have hsq : (c * (X ^ (k + 1) * R) ^ 2).coeff (k + 1) = 0 := by
    rw [show c * (X ^ (k + 1) * R) ^ 2 = X ^ (k + 1 + (k + 1)) * (c * R ^ 2) by ring,
      coeff_X_pow_mul', ite_eq_right]
    omega
  -- the linear term
  have hlin := coeff_derivative_eval_mul_X_pow_mul Q hA (hAP 0 (Nat.zero_le _)) hPA
  -- the constant term, from values
  have hconst : (G.eval A).coeff (k + 1) =
      ∑ s, coeffWeight (k + 1) s * Q.evalEval (s + τ) (A.eval s) := by
    change (shiftEval Q τ A).coeff (k + 1) = _
    rw [← sum_coeffWeight_mul_eval
      ((natDegree_shiftEval_le hQ τ (hA.trans hk.le)).trans_lt hD)]
    exact sum_congr rfl fun s _ => by rw [eval_shiftEval]
  rw [hsq, hlin, hconst, zero_add] at hcoeff
  have hS : ∑ s, coeffWeight (k + 1) s * Q.evalEval (s + τ) (A.eval s) =
      -(lam * (taylor τ P).coeff (k + 1)) := by linear_combination hcoeff
  rw [henselCoeff, hS, neg_neg, mul_div_cancel_left₀ _ hlam]

/-- **Newton iteration recovers a simple root.** Let `Q(X, P(X)) = 0` with `P` of degree at most
`d`, let `Q` have `(1, d)`-weighted degree at most `D < |F|`, and let
`∂Q/∂Y (τ, P(τ)) ≠ 0`. Then Newton iteration from the hint `P(τ)` returns `P(0)`. -/
theorem henselValue_eq {d D : ℕ} {Q : F[X][Y]}
    (hQ : Sudan.WeightedDegreeLE d D Q) (hD : D < Fintype.card F)
    {P : F[X]} (hP : P.natDegree ≤ d) (hQP : Q.eval P = 0) {τ : F}
    (hlam : (derivative Q).evalEval τ (P.eval τ) ≠ 0) :
    henselValue Q τ (P.eval τ) d = P.eval 0 := by
  set lam := (derivative Q).evalEval τ (P.eval τ)
  have key : ∀ k ≤ d, (henselTrunc Q τ (P.eval τ) lam k).natDegree ≤ k ∧
      ∀ i ≤ k, (henselTrunc Q τ (P.eval τ) lam k).coeff i = (taylor τ P).coeff i := by
    intro k hk
    induction k with
    | zero =>
      refine ⟨by simp [henselTrunc], fun i hi => ?_⟩
      rw [Nat.le_zero.1 hi, henselTrunc, coeff_C_zero, taylor_coeff_zero]
    | succ k ih =>
      obtain ⟨hdeg, hcoeff⟩ := ih (Nat.le_of_succ_le hk)
      have hstep := henselCoeff_eq hQ hD hQP hlam (Nat.lt_of_succ_le hk) hdeg hcoeff
      refine ⟨?_, fun i hi => ?_⟩
      · rw [henselTrunc]
        refine natDegree_add_le_of_degree_le (hdeg.trans (Nat.le_succ k)) ?_
        exact natDegree_C_mul_X_pow_le _ _
      · rw [henselTrunc, coeff_add, coeff_C_mul_X_pow, hstep]
        rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hi) with hi | rfl
        · rw [ite_eq_right (by omega), add_zero, hcoeff i (Nat.lt_succ_iff.1 hi)]
        · rw [ite_eq_left rfl, coeff_eq_zero_of_natDegree_lt (by omega), zero_add]
  obtain ⟨hdeg, hcoeff⟩ := key d le_rfl
  have heq : henselTrunc Q τ (P.eval τ) lam d = taylor τ P := by
    ext i
    by_cases hi : i ≤ d
    · exact hcoeff i hi
    · rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_eq_zero_of_natDegree_lt
        (by rw [natDegree_taylor]; omega)]
  rw [henselValue, heq, taylor_eval, neg_add_cancel]

omit [Fintype F] [DecidableEq F] in
/-- The derivative in `Y` of `bivariateOf M c` at `(x, y)`. -/
theorem evalEval_derivative_bivariateOf (M : Finset (ℕ × ℕ)) (c : ℕ × ℕ → F) (x y : F) :
    (derivative (Sudan.bivariateOf M c)).evalEval x y =
      ∑ m ∈ M, c m * (m.2 * x ^ m.1 * y ^ (m.2 - 1)) := by
  simp only [Sudan.bivariateOf, derivative_sum, derivative_monomial, evalEval_finsetSum]
  refine sum_congr rfl fun m _ => ?_
  simp only [evalEval, eval_monomial, eval_mul, eval_natCast, eval_pow, eval_C]
  ring

/-! ### Decoding with a hint -/

variable {ι : Type*} [Fintype ι]

/-- **Sudan decoding with a hint.** The value at `0` of the root of the least-`Y`-degree Sudan
interpolant of the received word `w` (with evaluation points `α`), lifted by Newton iteration from
the hint `a` at `τ`. -/
noncomputable def hintDecode (α w : ι → F) (d D : ℕ) (τ a : F) : F :=
  henselValue (Sudan.interpolant α w d D) τ a d

/-- **Decoding with a hint is correct at almost every hint point.** With distinct points, `d ≥ 1`,
more monomials of `(1, d)`-weighted degree at most `D` than points, and `D < |F|`: if `P` has
degree at most `d` and agrees with the received word at more than `D` points, then
`hintDecode α w d D τ (P τ) = P 0` for all but at most `D - d` points `τ`. -/
theorem card_hintDecode_ne_le {α w : ι → F} {d D : ℕ} (hα : Function.Injective α)
    (hd : 1 ≤ d) (hn : Fintype.card ι < #(Sudan.monomials d D)) (hD : D < Fintype.card F)
    {P : F[X]} (hP : P.natDegree ≤ d) (hagree : D < #{i | P.eval (α i) = w i}) :
    #{τ | hintDecode α w d D τ (P.eval τ) ≠ P.eval 0} ≤ D - d := by
  have hQ := Sudan.isInterpolant_interpolant α w hd hn
  obtain ⟨S, hQS, hS0, hSdeg⟩ := Sudan.exists_eq_mul_eval_ne_zero hα hQ
    (fun Q' hQ' => Sudan.natDegree_interpolant_le α w hd hn hQ') hP hagree
  have hQP : (Sudan.interpolant α w d D).eval P = 0 := by
    rw [hQS, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul]
  have hsub : ({τ | hintDecode α w d D τ (P.eval τ) ≠ P.eval 0} : Finset F) ⊆
      (S.eval P).roots.toFinset := by
    intro τ hτ
    rw [Multiset.mem_toFinset, mem_roots hS0, IsRoot.def]
    by_contra hne
    refine (mem_filter.1 hτ).2 (henselValue_eq hQ.weightedDegree_le hD hP hQP ?_)
    rw [hQS, derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul,
      evalEval_add, evalEval_mul, evalEval_sub, evalEval_X, evalEval_C, sub_self, zero_mul,
      add_zero, ← eval_eval_eq_evalEval]
    exact hne
  exact (card_le_card hsub).trans ((Multiset.toFinset_card_le _).trans
    ((card_roots' _).trans hSdeg))

end Cslib.Code
