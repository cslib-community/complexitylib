/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Code.ReedSolomon
public import CslibFrontier.Foundations.Data.Code.SudanInterpolant

/-!
# Sudan's list decoder for Reed–Solomon codes

Let `w : ι → F` be a received word and let `α` be distinct evaluation points. Sudan's algorithm
[Sudan1997], [GuruswamiRudraSudan2019] lists the polynomials `P` of degree less than `k` whose
values agree with `w` at more than `D` points, for a parameter `D`. It interpolates: it finds a
nonzero bivariate polynomial `Q(X, Y)` of `(1, k - 1)`-weighted degree at most `D` that vanishes at
the `n` points `(α i, w i)` (`Cslib.Code.Sudan.IsInterpolant`, `Cslib.Code.Sudan.interpolant`). If
`P` has degree less than `k`, then `Q(X, P(X))` has degree at most `D` and vanishes at every point
where `P` agrees with `w`; when there are more than `D` of them it is zero, so `Y - P(X)` divides
`Q(X, Y)` (`Cslib.Code.Sudan.IsInterpolant.X_sub_C_dvd`): `P` is a root of `Q` viewed as a
polynomial in `Y` over `F[X]`. The number of such roots is at most the `Y`-degree of `Q`, which is
at most `D / (k - 1)` for `k ≥ 2`.

The decoder `Cslib.Code.sudan` returns the roots `P` of the elimination interpolant
`Cslib.Code.Sudan.interpolant α w (k - 1) D` that have degree less than `k` and agree with `w` at
more than `D` points. Because `Cslib.Code.Sudan.interpolant` searches `Y`-degrees up to
`D / (k - 1)`, completeness (`Cslib.Code.mem_sudan_iff`) requires positive weight `k - 1 ≥ 1`, that
is `k ≥ 2`: with distinct points, `k ≥ 2` and more than `n` monomials, its list consists of
exactly those polynomials (`Cslib.Code.mem_sudan_iff`), while soundness
(`Cslib.Code.degree_lt_and_lt_card_of_mem_sudan`) and the list-size bound `L * (k - 1) ≤ D`
(`Cslib.Code.card_sudan_mul_le`) hold for all `k`. For `k ≥ 2` and
`2 * (k - 1) * n < (D + 1) * (D + 2)`, this list decodes the Reed–Solomon code of dimension `k`
from agreement `D + 1 ≈ √(2 * (k - 1) * n)` (`Cslib.Code.mem_sudan_iff_of_lt`), and at most
`D / (k - 1)` codewords have that agreement with any word
(`Cslib.Code.ncard_sep_reedSolomon_mul_le`). Unique decoding needs agreement `(n + k) / 2`, so this
goes beyond half the minimum distance when the rate `k / n` is small: asymptotically, below
`3 - 2 * √2 ≈ 0.17`.

This module proves the correctness of the decoder only: `Cslib.Code.sudan` computes the interpolant
by elimination (`Cslib.Code.Sudan.interpolant`) and takes its roots in `F[X][Y]` noncomputably
(`Polynomial.roots`), which in the literature are found in polynomial time by factoring bivariate
polynomials; no running time is formalized here.

## Main definitions

* `Cslib.Code.sudan`: Sudan's list decoder, built from the explicit elimination interpolant
  `Cslib.Code.Sudan.interpolant`.

## Main results

* `Cslib.Code.degree_lt_and_lt_card_of_mem_sudan`: soundness of the listed polynomials.
* `Cslib.Code.mem_sudan_iff`, `Cslib.Code.mem_sudan_iff_of_lt`: the decoder lists exactly the
  polynomials with large agreement.
* `Cslib.Code.card_sudan_mul_le`: the decoder lists at most `D / (k - 1)` polynomials.
* `Cslib.Code.exists_mem_sudan_of_mem_reedSolomon`: list decoding of Reed–Solomon codes.
* `Cslib.Code.ncard_sep_reedSolomon_mul_le`: few Reed–Solomon codewords have large agreement with
  a word.

## References

* [M. Sudan, *Decoding of Reed Solomon codes beyond the error-correction bound*][Sudan1997]
* [V. Guruswami, A. Rudra, M. Sudan, *Essential Coding Theory*]
  [GuruswamiRudraSudan2019]
-/

@[expose] public section

namespace Cslib.Code

open Finset Polynomial

variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq F]

/-- *Sudan's list decoder* for dimension `k` and weighted degree `D` with evaluation points `α`: the
roots `P` of the least-`Y`-degree Sudan interpolant `Sudan.interpolant α w (k - 1) D` for the
received word `w`, as a polynomial in `Y`, that have degree less than `k` and agree with `w` at more
than `D` points. Completeness (`mem_sudan_iff`) assumes `k ≥ 2` so that the weight `k - 1` is
positive; the roots are taken noncomputably via `Polynomial.roots`. -/
noncomputable def sudan (α w : ι → F) (k D : ℕ) : Finset F[X] :=
  {P ∈ (Sudan.interpolant α w (k - 1) D).roots.toFinset |
    P.degree < k ∧ D < #{i | P.eval (α i) = w i}}

variable {α w : ι → F} {k D : ℕ} {P : F[X]}

/-- Every polynomial listed by Sudan's decoder has degree less than `k` and agrees with the
received word at more than `D` points. -/
theorem degree_lt_and_lt_card_of_mem_sudan (h : P ∈ sudan α w k D) :
    P.degree < k ∧ D < #{i | P.eval (α i) = w i} :=
  (mem_filter.1 h).2

/-- **The size of the list.** Sudan's decoder lists `L` polynomials with `L * (k - 1) ≤ D`: at most
`D / (k - 1)` of them for `k ≥ 2`. -/
theorem card_sudan_mul_le : #(sudan α w k D) * (k - 1) ≤ D := by
  refine (Nat.mul_le_mul_right _ ?_).trans
    (Sudan.weightedDegreeLE_interpolant α w (k - 1) D).natDegree_mul_le
  exact (card_filter_le _ _).trans (Multiset.toFinset_card_le _ |>.trans (card_roots' _))

/-- **Sudan's list decoder lists the polynomials with large agreement.** With distinct points,
`k ≥ 2` and more than `n` monomials of `(1, k - 1)`-weighted degree at most `D`, Sudan's decoder
lists exactly the polynomials of degree less than `k` that agree with the received word at more than
`D` points. -/
theorem mem_sudan_iff (hα : Function.Injective α) (hk : 2 ≤ k)
    (hn : Fintype.card ι < #(Sudan.monomials (k - 1) D)) :
    P ∈ sudan α w k D ↔ P.degree < k ∧ D < #{i | P.eval (α i) = w i} := by
  refine ⟨degree_lt_and_lt_card_of_mem_sudan, fun hP => ?_⟩
  have hQ := Sudan.isInterpolant_interpolant α w (by omega) hn
  have hPdeg : P.natDegree ≤ k - 1 := by
    rcases eq_or_ne P 0 with rfl | hP0
    · simp
    · have := (natDegree_lt_iff_degree_lt hP0).2 hP.1
      omega
  exact mem_filter.2 ⟨Multiset.mem_toFinset.2 (hQ.mem_roots hα hPdeg hP.2), hP⟩

/-- **Sudan's list decoding of Reed–Solomon codes** [Sudan1997]. With distinct points, `k ≥ 2` and
`2 * (k - 1) * n < (D + 1) * (D + 2)`, Sudan's decoder lists exactly the polynomials of degree less
than `k` that agree with the received word at more than `D` points; by `card_sudan_mul_le` there are
at most `D / (k - 1)` of them. -/
theorem mem_sudan_iff_of_lt (hα : Function.Injective α) (hk : 2 ≤ k)
    (hn : 2 * (k - 1) * Fintype.card ι < (D + 1) * (D + 2)) :
    P ∈ sudan α w k D ↔ P.degree < k ∧ D < #{i | P.eval (α i) = w i} := by
  refine mem_sudan_iff hα hk ?_
  have := Sudan.add_one_mul_add_two_le_two_mul_mul_card_monomials (w := k - 1) (by omega) D
  exact Nat.lt_of_mul_lt_mul_left (hn.trans_le this)

/-- **List decoding of Reed–Solomon codes.** With distinct points, `k ≥ 2` and
`2 * (k - 1) * n < (D + 1) * (D + 2)`, every codeword of the Reed–Solomon code of dimension `k`
that agrees with the received word at more than `D` points is the list of values of a polynomial
listed by Sudan's decoder. -/
theorem exists_mem_sudan_of_mem_reedSolomon (hα : Function.Injective α) (hk : 2 ≤ k)
    (hn : 2 * (k - 1) * Fintype.card ι < (D + 1) * (D + 2)) {c : ι → F}
    (hc : c ∈ reedSolomon α k) (hagree : D < #{i | c i = w i}) :
    ∃ P ∈ sudan α w k D, (fun i => P.eval (α i)) = c := by
  obtain ⟨P, hP, rfl⟩ := mem_reedSolomon.1 hc
  exact ⟨P, (mem_sudan_iff_of_lt hα hk hn).2 ⟨hP, hagree⟩, rfl⟩

/-- **List size for Reed–Solomon codes.** With distinct points, `k ≥ 2` and
`2 * (k - 1) * n < (D + 1) * (D + 2)`, the number `L` of codewords of the Reed–Solomon code of
dimension `k` that agree with a word at more than `D` points satisfies `L * (k - 1) ≤ D`. -/
theorem ncard_sep_reedSolomon_mul_le (hα : Function.Injective α) (hk : 2 ≤ k)
    (hn : 2 * (k - 1) * Fintype.card ι < (D + 1) * (D + 2)) (w : ι → F) :
    {c ∈ (reedSolomon α k : Set (ι → F)) | D < #{i | c i = w i}}.ncard * (k - 1) ≤ D := by
  refine (Nat.mul_le_mul_right _ ?_).trans (card_sudan_mul_le (α := α) (w := w))
  calc {c ∈ (reedSolomon α k : Set (ι → F)) | D < #{i | c i = w i}}.ncard
      ≤ ((fun P : F[X] => fun i => P.eval (α i)) '' (sudan α w k D : Set F[X])).ncard := by
        refine Set.ncard_le_ncard (fun c hc => ?_) ((sudan α w k D).finite_toSet.image _)
        obtain ⟨P, hP, rfl⟩ := exists_mem_sudan_of_mem_reedSolomon hα hk hn hc.1 hc.2
        exact ⟨P, hP, rfl⟩
    _ ≤ (sudan α w k D : Set F[X]).ncard := Set.ncard_image_le (sudan α w k D).finite_toSet
    _ = #(sudan α w k D) := Set.ncard_coe_finset _

end Cslib.Code
