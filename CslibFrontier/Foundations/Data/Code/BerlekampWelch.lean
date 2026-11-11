/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Code.ReedSolomon
public import Mathlib.Algebra.Polynomial.Div
import CslibFrontier.Foundations.Data.Hamming
import Mathlib.LinearAlgebra.Lagrange

/-!
# The Berlekamp–Welch decoder

Let `w : ι → F` be a received word that differs from the values `i ↦ p (α i)` of a polynomial `p`
of degree less than `k` at no more than `e` of the distinct points `α i`. The Berlekamp–Welch
decoder [WelchBerlekamp1986], [GuruswamiRudraSudan2019] looks for a monic
*error locator* `E` of degree `e` and a polynomial `Q` of degree less than `e + k` with
`Q (α i) = w i * E (α i)` at every point: the *key equations*
(`Cslib.Code.BerlekampWelch.IsSolution`). They have a solution, with `E` vanishing at the errors
and `Q = p * E` (`Cslib.Code.BerlekampWelch.exists_isSolution`). Conversely, if `2 e + k ≤ n`,
then for every solution `Q - p * E` has degree less than `e + k` and vanishes at the at least
`n - e ≥ e + k` points without errors, so `Q = p * E` and `p` is the quotient `Q /ₘ E`
(`Cslib.Code.BerlekampWelch.IsSolution.divByMonic_eq`).

The decoder `Cslib.Code.berlekampWelch` takes a solution `(E, Q)`, and returns the quotient
`Q /ₘ E` after checking, as in [GuruswamiRudraSudan2019], that `E` divides `Q` and that the
values of the quotient are within distance `e` of `w`; it fails, returning `none`, when there is
no solution or a check fails. The checks make it *sound* for every received word: an output `p`
has degree less than `k`, its values are within distance `e` of `w`, and `p * E` solves the key
equations together with `E` (`Cslib.Code.degree_lt_of_berlekampWelch_eq_some`,
`Cslib.Code.hammingDist_le_of_berlekampWelch_eq_some`,
`Cslib.Code.exists_isSolution_mul_of_berlekampWelch_eq_some`). In particular, it fails on a
received word with no polynomial of degree less than `k` within distance `e`
(`Cslib.Code.berlekampWelch_eq_none_of_forall_lt_hammingDist`). With distinct points and
`2 e + k ≤ n` it is also *complete*: it returns `p` whenever the values of `p` are within distance
`e` of `w` (`Cslib.Code.berlekampWelch_eq_some`), so its outputs are exactly those polynomials
(`Cslib.Code.berlekampWelch_eq_some_iff`). Reed–Solomon codes of dimension `k` are therefore
uniquely decoded up to `(n - k) / 2` errors, the largest number below half their minimum distance
`n - k + 1`, and the decoder reports failure beyond that radius when no codeword is close.

The key equations are a system of `n` linear equations in the `2 e + k` unknown coefficients of
`E` and `Q`; in the literature they are solved by Gaussian elimination. This module proves the
correctness of the decoder only: `Cslib.Code.berlekampWelch` chooses a solution noncomputably,
and no running time is formalized.

## Main definitions

* `Cslib.Code.BerlekampWelch.IsSolution`: solutions of the key equations.
* `Cslib.Code.berlekampWelch`: the Berlekamp–Welch decoder.

## Main results

* `Cslib.Code.BerlekampWelch.exists_isSolution`: the key equations have a solution.
* `Cslib.Code.BerlekampWelch.IsSolution.eq_mul`,
  `Cslib.Code.BerlekampWelch.IsSolution.divByMonic_eq`: every solution yields the polynomial.
* `Cslib.Code.degree_lt_of_berlekampWelch_eq_some`,
  `Cslib.Code.hammingDist_le_of_berlekampWelch_eq_some`,
  `Cslib.Code.exists_isSolution_mul_of_berlekampWelch_eq_some`: soundness of the decoder.
* `Cslib.Code.berlekampWelch_eq_none_of_forall_lt_hammingDist`: the decoder fails when no
  polynomial is close.
* `Cslib.Code.berlekampWelch_eq_some`: the decoder corrects up to `e` errors when
  `2 e + k ≤ n`.
* `Cslib.Code.berlekampWelch_eq_some_iff`, `Cslib.Code.berlekampWelch_eq_none_iff`: when
  `2 e + k ≤ n`, the decoder returns exactly the polynomials within distance `e`.
* `Cslib.Code.berlekampWelch_eq_some_of_mem_reedSolomon`: unique decoding of Reed–Solomon codes.

## References

* [L. R. Welch, E. R. Berlekamp, *Error correction for algebraic block codes*][WelchBerlekamp1986]
* [V. Guruswami, A. Rudra, M. Sudan, *Essential Coding Theory*]
  [GuruswamiRudraSudan2019]
-/
@[expose] public section

namespace Cslib.Code

open Finset Polynomial

variable {F ι : Type*} [Field F]

namespace BerlekampWelch

/-- `(E, Q)` solves the *Berlekamp–Welch key equations* for the received word `w` with evaluation
points `α`, `e` errors and dimension `k`: the error locator `E` is monic of degree `e`, `Q` has
degree less than `e + k`, and `Q (α i) = w i * E (α i)` at every point. -/
structure IsSolution (α w : ι → F) (e k : ℕ) (E Q : F[X]) : Prop where
  /-- The error locator `E` is monic. -/
  monic : E.Monic
  /-- The error locator `E` has degree exactly `e`. -/
  natDegree_eq : E.natDegree = e
  /-- The polynomial `Q`, which stands for `p * E`, has degree less than `e + k`. -/
  degree_lt : Q.degree < (e + k : ℕ)
  /-- The key equations: `Q (α i) = w i * E (α i)` at every point. -/
  eval_eq : ∀ i, Q.eval (α i) = w i * E.eval (α i)

variable {α w : ι → F} {e k : ℕ} {p : F[X]}

/-- The product of a polynomial of degree less than `k` with a polynomial of degree `e` has degree
less than `e + k`. -/
private theorem degree_mul_lt {E : F[X]} (hp : p.degree < k) (hE : E.natDegree = e) :
    (p * E).degree < (e + k : ℕ) := by
  rcases eq_or_ne p 0 with rfl | hp0
  · rw [zero_mul, degree_zero]
    exact WithBot.bot_lt_coe _
  rcases eq_or_ne E 0 with rfl | hE0
  · rw [mul_zero, degree_zero]
    exact WithBot.bot_lt_coe _
  have := (natDegree_lt_iff_degree_lt hp0).2 hp
  rw [degree_mul, degree_eq_natDegree hp0, degree_eq_natDegree hE0, hE, ← Nat.cast_add,
    Nat.cast_lt]
  omega

/-- The quotient `Q /ₘ E` of a solution of the key equations has degree less than `k`. -/
theorem IsSolution.degree_divByMonic_lt {E Q : F[X]} (h : IsSolution α w e k E Q) :
    (Q /ₘ E).degree < k := by
  rcases eq_or_ne (Q /ₘ E) 0 with h0 | h0
  · rw [h0, degree_zero]
    exact WithBot.bot_lt_coe _
  have hQ : Q ≠ 0 := by
    rintro rfl
    exact h0 (zero_divByMonic E)
  have hlt := (natDegree_lt_iff_degree_lt hQ).2 h.degree_lt
  have hle : E.natDegree ≤ Q.natDegree :=
    natDegree_le_natDegree (not_lt.1 ((divByMonic_eq_zero_iff h.monic).not.1 h0))
  rw [degree_eq_natDegree h0, natDegree_divByMonic _ h.monic, Nat.cast_lt]
  rw [h.natDegree_eq] at hle ⊢
  omega

variable [Fintype ι] [DecidableEq F]

/-- If the received word `w` is within distance `e` of the values of a polynomial `p` of degree
less than `k`, the key equations have a solution: `E` is the product of `X - α i` over the
points `i` where `w` is wrong, times a power of `X` that brings its degree to `e`, and
`Q = p * E`. -/
theorem exists_isSolution (hp : p.degree < k) (he : hammingDist (fun i => p.eval (α i)) w ≤ e) :
    ∃ E Q, IsSolution α w e k E Q := by
  classical
  let errors : Finset ι := {i | p.eval (α i) ≠ w i}
  have herrors : #errors ≤ e := he
  have hmonic : (Lagrange.nodal errors α * X ^ (e - #errors)).Monic :=
    Lagrange.nodal_monic.mul (monic_X_pow _)
  have hdeg : (Lagrange.nodal errors α * X ^ (e - #errors)).natDegree = e := by
    rw [Lagrange.nodal_monic.natDegree_mul (monic_X_pow _), Lagrange.natDegree_nodal,
      natDegree_X_pow]
    omega
  refine ⟨_, _, ⟨hmonic, hdeg, degree_mul_lt hp hdeg, fun i => ?_⟩⟩
  rw [eval_mul]
  by_cases hi : i ∈ errors
  · rw [eval_mul, Lagrange.eval_nodal_at_node hi, zero_mul, mul_zero, mul_zero]
  · rw [show p.eval (α i) = w i by simpa [errors] using hi]

/-- **Correctness of the key equations.** With distinct points, if `2 e + k ≤ n` and the received
word `w` is within distance `e` of the values of a polynomial `p` of degree less than `k`, every
solution `(E, Q)` of the key equations has `Q = p * E`. -/
theorem IsSolution.eq_mul (hα : Function.Injective α) (hn : 2 * e + k ≤ Fintype.card ι)
    (hp : p.degree < k) (he : hammingDist (fun i => p.eval (α i)) w ≤ e) {E Q : F[X]}
    (h : IsSolution α w e k E Q) : Q = p * E := by
  classical
  -- `Q - p * E` vanishes at the points without errors, of which there are at least `e + k`
  let correct : Finset ι := {i | p.eval (α i) = w i}
  have hcorrect : #correct + hammingDist (fun i => p.eval (α i)) w = Fintype.card ι :=
    card_filter_eq_add_hammingDist _ _
  refine sub_eq_zero.1 (eq_zero_of_degree_lt_of_eval_finset_eq_zero (correct.image α) ?_ ?_)
  · rw [card_image_of_injective _ hα]
    calc (Q - p * E).degree ≤ max Q.degree (p * E).degree := degree_sub_le _ _
      _ < (e + k : ℕ) := max_lt h.degree_lt (degree_mul_lt hp h.natDegree_eq)
      _ ≤ #correct := by exact_mod_cast (by omega)
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := mem_image.1 hx
    rw [eval_sub, eval_mul, h.eval_eq i, (mem_filter.1 hi).2, sub_self]

/-- With distinct points, if `2 e + k ≤ n` and the received word is within distance `e` of the
values of a polynomial `p` of degree less than `k`, every solution `(E, Q)` of the key equations
gives `p = Q /ₘ E`. -/
theorem IsSolution.divByMonic_eq (hα : Function.Injective α) (hn : 2 * e + k ≤ Fintype.card ι)
    (hp : p.degree < k) (he : hammingDist (fun i => p.eval (α i)) w ≤ e) {E Q : F[X]}
    (h : IsSolution α w e k E Q) : Q /ₘ E = p := by
  rw [h.eq_mul hα hn hp he, mul_comm, mul_divByMonic_cancel_left p h.monic]

end BerlekampWelch

variable [Fintype ι] [DecidableEq F]

open BerlekampWelch Classical in
/-- The *Berlekamp–Welch decoder* for `e` errors and dimension `k` with evaluation points `α`:
for a solution `(E, Q)` of the key equations for the received word `w`, the quotient `Q /ₘ E` if
`E` divides `Q` and the values of the quotient are within distance `e` of `w`, and `none` when a
check fails or the key equations have no solution. The solution is chosen noncomputably; this
definition makes no claim about how it is found. -/
noncomputable def berlekampWelch (α : ι → F) (e k : ℕ) (w : ι → F) : Option F[X] :=
  if h : ∃ EQ : F[X] × F[X], IsSolution α w e k EQ.1 EQ.2 then
    if h.choose.1 ∣ h.choose.2 ∧
        hammingDist (fun i => (h.choose.2 /ₘ h.choose.1).eval (α i)) w ≤ e then
      some (h.choose.2 /ₘ h.choose.1)
    else none
  else none

variable {α w : ι → F} {e k : ℕ} {p : F[X]}

open BerlekampWelch in
/-- **Soundness of the Berlekamp–Welch decoder.** Whatever the received word, an output `p` of the
decoder comes with an error locator `E` such that `(E, p * E)` solves the key equations. -/
theorem exists_isSolution_mul_of_berlekampWelch_eq_some (h : berlekampWelch α e k w = some p) :
    ∃ E, IsSolution α w e k E (p * E) := by
  classical
  unfold berlekampWelch at h
  split_ifs at h with hEQ hcheck
  obtain ⟨⟨r, hr⟩, -⟩ := hcheck
  have hp : hEQ.choose.2 /ₘ hEQ.choose.1 = r := by
    rw [hr, mul_divByMonic_cancel_left _ hEQ.choose_spec.monic]
  refine ⟨hEQ.choose.1, ?_⟩
  rw [← Option.some_injective _ h, hp, mul_comm, ← hr]
  exact hEQ.choose_spec

/-- **Soundness of the Berlekamp–Welch decoder.** Whatever the received word, an output of the
decoder has degree less than `k`. -/
theorem degree_lt_of_berlekampWelch_eq_some (h : berlekampWelch α e k w = some p) :
    p.degree < k := by
  obtain ⟨E, hE⟩ := exists_isSolution_mul_of_berlekampWelch_eq_some h
  have := hE.degree_divByMonic_lt
  rwa [mul_comm, mul_divByMonic_cancel_left _ hE.monic] at this

/-- **Soundness of the Berlekamp–Welch decoder.** Whatever the received word `w`, the values of an
output of the decoder are within distance `e` of `w`. -/
theorem hammingDist_le_of_berlekampWelch_eq_some (h : berlekampWelch α e k w = some p) :
    hammingDist (fun i => p.eval (α i)) w ≤ e := by
  classical
  unfold berlekampWelch at h
  split_ifs at h with hEQ hcheck
  rw [← Option.some_injective _ h]
  exact hcheck.2

/-- **Failure detection.** If the values of no polynomial of degree less than `k` are within
distance `e` of the received word `w`, the Berlekamp–Welch decoder returns `none`. -/
theorem berlekampWelch_eq_none_of_forall_lt_hammingDist
    (h : ∀ p : F[X], p.degree < k → e < hammingDist (fun i => p.eval (α i)) w) :
    berlekampWelch α e k w = none := by
  rcases hbw : berlekampWelch α e k w with _ | p
  · rfl
  · exact absurd (hammingDist_le_of_berlekampWelch_eq_some hbw)
      (not_le.2 (h p (degree_lt_of_berlekampWelch_eq_some hbw)))

open BerlekampWelch in
/-- **The Berlekamp–Welch decoder corrects `e` errors** when `2 e + k ≤ n`: with distinct points,
if the received word `w` is within distance `e` of the values of a polynomial `p` of degree less
than `k`, the decoder returns `p`. -/
theorem berlekampWelch_eq_some (hα : Function.Injective α) (hn : 2 * e + k ≤ Fintype.card ι)
    (hp : p.degree < k) (he : hammingDist (fun i => p.eval (α i)) w ≤ e) :
    berlekampWelch α e k w = some p := by
  classical
  obtain ⟨E, Q, hEQ⟩ := exists_isSolution hp he
  have h : ∃ EQ : F[X] × F[X], IsSolution α w e k EQ.1 EQ.2 := ⟨(E, Q), hEQ⟩
  have hdiv := h.choose_spec.divByMonic_eq hα hn hp he
  have hdvd : h.choose.1 ∣ h.choose.2 :=
    ⟨p, by rw [h.choose_spec.eq_mul hα hn hp he, mul_comm]⟩
  rw [berlekampWelch, dite_eq_left h, ite_eq_left ⟨hdvd, by rwa [hdiv]⟩, hdiv]

/-- **The outputs of the Berlekamp–Welch decoder** when `2 e + k ≤ n`: with distinct points, the
decoder returns `p` exactly when `p` has degree less than `k` and its values are within distance
`e` of the received word. -/
theorem berlekampWelch_eq_some_iff (hα : Function.Injective α)
    (hn : 2 * e + k ≤ Fintype.card ι) :
    berlekampWelch α e k w = some p ↔
      p.degree < k ∧ hammingDist (fun i => p.eval (α i)) w ≤ e :=
  ⟨fun h => ⟨degree_lt_of_berlekampWelch_eq_some h, hammingDist_le_of_berlekampWelch_eq_some h⟩,
    fun h => berlekampWelch_eq_some hα hn h.1 h.2⟩

/-- **Failures of the Berlekamp–Welch decoder** when `2 e + k ≤ n`: with distinct points, the
decoder returns `none` exactly when the values of no polynomial of degree less than `k` are within
distance `e` of the received word. -/
theorem berlekampWelch_eq_none_iff (hα : Function.Injective α)
    (hn : 2 * e + k ≤ Fintype.card ι) :
    berlekampWelch α e k w = none ↔
      ∀ p : F[X], p.degree < k → e < hammingDist (fun i => p.eval (α i)) w := by
  refine ⟨fun h p hp => not_le.1 fun he => ?_, berlekampWelch_eq_none_of_forall_lt_hammingDist⟩
  rw [berlekampWelch_eq_some hα hn hp he] at h
  exact Option.some_ne_none _ h

/-- **Unique decoding of Reed–Solomon codes.** With distinct points, if `2 e + k ≤ n` and the
received word `w` is within distance `e` of a codeword `c` of the Reed–Solomon code of dimension
`k`, the Berlekamp–Welch decoder returns a polynomial of degree less than `k` whose values are
`c`. -/
theorem berlekampWelch_eq_some_of_mem_reedSolomon (hα : Function.Injective α)
    (hn : 2 * e + k ≤ Fintype.card ι) {c : ι → F} (hc : c ∈ reedSolomon α k)
    (he : hammingDist c w ≤ e) :
    ∃ p : F[X], p.degree < k ∧ (fun i => p.eval (α i)) = c ∧ berlekampWelch α e k w = some p := by
  obtain ⟨p, hp, rfl⟩ := mem_reedSolomon.1 hc
  exact ⟨p, hp, rfl, berlekampWelch_eq_some hα hn hp he⟩

end Cslib.Code
