/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Algebra.Polynomial.RealRoot.RootBound
public import CslibFrontier.Foundations.Algebra.Polynomial.RealRoot.Sturm
public import CslibFrontier.Foundations.Data.Polynomial.CoeffList
public import Mathlib.Data.List.SignVariations
public import Mathlib.Data.Nat.Log

import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Data.Rat.Cast.Order

/-!
# Computable Rational Polynomial Arithmetic and Sturm Evaluation

This module provides computable coefficient-list operations on `ℚ[X]` (trimming, arithmetic,
formal derivative, Euclidean division, Sturm sequences, rational sign-variation counting, Cauchy
root bounds, integer denominator clearing, and Mignotte bisection-depth computation) and proves
their exact algebraic correspondence with Mathlib's `Polynomial` and `Polynomial.sturmVariations`
over `ℝ`.

## Main definitions

* `Cslib.RealRoot.IsTrimmed`: predicate asserting that a coefficient list has no trailing zero.
* `Cslib.RealRoot.trim`, `Cslib.RealRoot.addList`, `Cslib.RealRoot.negList`,
  `Cslib.RealRoot.subList`, `Cslib.RealRoot.scaleList`, `Cslib.RealRoot.shiftZero`,
  `Cslib.RealRoot.derivList`, `Cslib.RealRoot.divModList`, `Cslib.RealRoot.negModList`:
  computable dense-list operations representing polynomials in `ℚ[X]`.
* `Cslib.RealRoot.sturmSeqList`, `Cslib.RealRoot.sturmVariationsList`: computable Sturm sequence
  and rational sign-variation evaluation over `ℚ`.
* `Cslib.RealRoot.cauchyBoundNat`, `Cslib.RealRoot.lcmDens`, `Cslib.RealRoot.clearDenomsList`,
  `Cslib.RealRoot.sqNormList`, `Cslib.RealRoot.mignotteSepSqInv`,
  `Cslib.RealRoot.mignotteBisectionDepth`: computable Cauchy root bound, integer clearing,
  Mignotte separation denominator, and bisection-depth bound.

## Main results

* `Cslib.RealRoot.ofCoeffList_negModList` and `Cslib.RealRoot.sturmSeqList_map_ofCoeffList`:
  exact correspondence between list operations and `Polynomial.mod` / `Polynomial.sturmSeq`.
* `Cslib.RealRoot.sturmVariationsList_eq_sturmVariations`:
  `sturmVariationsList (sturmSeqList cs) x` equals
  `sturmVariations ((ofCoeffList cs).map (algebraMap ℚ ℝ)) x`.
* `Cslib.RealRoot.abs_lt_cauchyBoundNat_of_isRoot`, `Cslib.RealRoot.dyadic_width_lt_root_sep`,
  and `Cslib.RealRoot.mignotteBisectionDepth_le`: verified Cauchy root enclosure, Mignotte
  bisection separation guarantee, and logarithmic depth bound.

## References

* [BasuPollackRoy2006] (locator unverified)
* [Mahler1964] (originator of the Mahler-measure root-separation inequality; locator unverified)
* [Mignotte1982] (locator unverified)
-/

public section

namespace Cslib.RealRoot

open Polynomial

/-- Predicate asserting that a coefficient list has no trailing zero. -/
def IsTrimmed {R : Type*} [Zero R] (l : List R) : Prop :=
  l.getLast? ≠ some 0

/-- The empty coefficient list `[]` is trimmed. -/
theorem isTrimmed_nil {R : Type*} [Zero R] : IsTrimmed ([] : List R) := by
  simp only [IsTrimmed, List.getLast?_nil, ne_eq, reduceCtorEq, not_false_eq_true]

/-- Remove trailing zero coefficients from a rational coefficient list. -/
@[expose] def trim : List ℚ → List ℚ
  | [] => []
  | a :: as =>
    let t := trim as
    if t.isEmpty then (if a = 0 then [] else [a]) else a :: t

/-- `trim as` has length at most `as.length`. -/
theorem trim_length_le (as : List ℚ) : (trim as).length ≤ as.length := by
  induction as with
  | nil => simp only [trim, List.length_nil, le_refl]
  | cons a as ih =>
    simp only [trim]
    by_cases he : (trim as).isEmpty = true
    · simp only [he, ↓reduceIte]
      split_ifs <;> simp only [List.length_nil, List.length_cons] <;> omega
    · simp only [he, Bool.false_eq_true, ↓reduceIte, List.length_cons]
      omega

/-- Trimming trailing zeros preserves the polynomial denoted by `ofCoeffList`. -/
theorem ofCoeffList_trim (as : List ℚ) : ofCoeffList (trim as) = ofCoeffList as := by
  induction as with
  | nil => simp only [trim]
  | cons a as ih =>
    simp only [trim]
    by_cases he : (trim as).isEmpty = true
    · have hnil : trim as = [] := List.isEmpty_iff.mp he
      have h0 : ofCoeffList as = 0 := by rw [← ih, hnil, ofCoeffList_nil]
      simp only [he, ↓reduceIte]
      by_cases ha : a = 0
      · simp only [ha, ↓reduceIte, ofCoeffList_nil, ofCoeffList_cons, C_0, h0, mul_zero, add_zero]
      · simp only [ha, ↓reduceIte, ofCoeffList_cons, ofCoeffList_nil, h0]
    · simp only [he, Bool.false_eq_true, ↓reduceIte, ofCoeffList_cons, ih]

/-- Every output of `trim` is trimmed (`IsTrimmed`). -/
theorem isTrimmed_trim (as : List ℚ) : IsTrimmed (trim as) := by
  induction as with
  | nil => exact isTrimmed_nil
  | cons a as ih =>
    simp only [trim]
    by_cases he : (trim as).isEmpty = true
    · simp only [he, ↓reduceIte]
      by_cases ha : a = 0
      · simp only [ha, ↓reduceIte]
        exact isTrimmed_nil
      · rw [ite_eq_right (fun h => absurd h ha)]
        simp only [IsTrimmed, List.getLast?_singleton, ne_eq, Option.some.injEq]
        exact ha
    · have hne : trim as ≠ [] := fun hnil => he (List.isEmpty_iff.mpr hnil)
      simp only [he, Bool.false_eq_true, ↓reduceIte]
      have hlast : (a :: trim as).getLast? = (trim as).getLast? := by
        cases h : trim as with
        | nil => exact absurd h hne
        | cons _ _ => rfl
      rw [IsTrimmed, hlast]
      exact ih

/-- Any nonempty trimmed list has a nonzero last element. -/
theorem IsTrimmed.getLast?_ne_zero {l : List ℚ} (ht : IsTrimmed l) (hl : l ≠ []) :
    ∃ x, l.getLast? = some x ∧ x ≠ 0 := by
  have hsome : l.getLast? ≠ none := fun hnone => hl (List.getLast?_eq_none_iff.mp hnone)
  obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp hsome
  refine ⟨x, hx, ?_⟩
  intro hx0
  subst hx0
  exact ht hx

private theorem coeff_last_of_getLast?_eq {l : List ℚ} {x : ℚ} (hx : l.getLast? = some x) :
    (ofCoeffList l).coeff (l.length - 1) = x := by
  have hl : l ≠ [] := fun h => by simp only [h, List.getLast?_nil, reduceCtorEq] at hx
  have hlt : l.length - 1 < l.length := Nat.sub_lt (List.length_pos_of_ne_nil hl) zero_lt_one
  rw [coeff_ofCoeffList, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
  have hlast : some l[l.length - 1] = l.getLast? :=
    (List.getElem?_eq_getElem hlt).symm.trans List.getLast?_eq_getElem?.symm
  rw [hx] at hlast
  cases hlast
  rfl

/-- Leading-position coefficient `(ofCoeffList l).coeff (l.length - 1)` is nonzero for nonempty
trimmed `l`. -/
theorem IsTrimmed.coeff_last_ne_zero {l : List ℚ} (ht : IsTrimmed l) (hl : l ≠ []) :
    (ofCoeffList l).coeff (l.length - 1) ≠ 0 := by
  obtain ⟨x, hx, hx0⟩ := ht.getLast?_ne_zero hl
  rwa [coeff_last_of_getLast?_eq hx]

/-- A nonempty trimmed list represents a nonzero polynomial. -/
theorem IsTrimmed.ofCoeffList_ne_zero {l : List ℚ} (ht : IsTrimmed l) (hl : l ≠ []) :
    ofCoeffList l ≠ 0 := by
  intro h0
  apply ht.coeff_last_ne_zero hl
  rw [h0, coeff_zero]

/-- A trimmed list is empty if and only if its polynomial is `0`. -/
theorem IsTrimmed.eq_nil_iff {l : List ℚ} (ht : IsTrimmed l) :
    l = [] ↔ ofCoeffList l = 0 := by
  constructor
  · rintro rfl
    exact ofCoeffList_nil
  · intro h0
    by_contra hne
    exact ht.ofCoeffList_ne_zero hne h0

/-- For nonempty trimmed `l`, `(ofCoeffList l).natDegree + 1 = l.length`. -/
theorem IsTrimmed.natDegree_add_one {l : List ℚ} (ht : IsTrimmed l) (hl : l ≠ []) :
    (ofCoeffList l).natDegree + 1 = l.length := by
  have hle : (ofCoeffList l).natDegree ≤ l.length - 1 := natDegree_ofCoeffList_le l
  have hge : l.length - 1 ≤ (ofCoeffList l).natDegree :=
    le_natDegree_of_ne_zero (ht.coeff_last_ne_zero hl)
  have hpos : 1 ≤ l.length := List.length_pos_of_ne_nil hl
  omega

/-- Shorter trimmed lists have strictly smaller polynomial degree than nonempty trimmed `v`. -/
theorem IsTrimmed.degree_lt_of_length_lt {u v : List ℚ} (hu : IsTrimmed u) (hv : IsTrimmed v)
    (hv0 : v ≠ []) (huv : u.length < v.length) :
    (ofCoeffList u).degree < (ofCoeffList v).degree := by
  by_cases hu0 : u = []
  · subst hu0
    rw [ofCoeffList_nil, degree_zero]
    exact bot_lt_iff_ne_bot.mpr (Polynomial.degree_ne_bot.mpr (hv.ofCoeffList_ne_zero hv0))
  · refine Polynomial.degree_lt_degree ?_
    have hdu := hu.natDegree_add_one hu0
    have hdv := hv.natDegree_add_one hv0
    omega

/-- Coefficients of `ofCoeffList l` at indices `≥ l.length` are zero. -/
theorem coeff_ofCoeffList_eq_zero_of_le {R : Type*} [Semiring R] (l : List R) {i : ℕ}
    (hi : l.length ≤ i) : (ofCoeffList l).coeff i = 0 := by
  rw [coeff_ofCoeffList, List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]

/-- Pointwise addition of rational coefficient lists. -/
@[expose] def addList : List ℚ → List ℚ → List ℚ
  | [], bs => bs
  | as, [] => as
  | a :: as, b :: bs => (a + b) :: addList as bs

/-- Pointwise negation of a rational coefficient list. -/
@[expose] def negList : List ℚ → List ℚ := List.map Neg.neg

/-- Pointwise subtraction of rational coefficient lists. -/
@[expose] def subList (as bs : List ℚ) : List ℚ := addList as (negList bs)

/-- Scalar multiplication of a rational coefficient list. -/
@[expose] def scaleList (c : ℚ) : List ℚ → List ℚ := List.map (c * ·)

/-- Multiplication by `X ^ k` via prepending `k` zeros. -/
@[expose] def shiftZero (k : ℕ) (bs : List ℚ) : List ℚ := List.replicate k 0 ++ bs

/-- Auxiliary shifted-derivative pass over a coefficient list. -/
@[expose] def derivAux (k : ℕ) : List ℚ → List ℚ
  | [] => []
  | a :: as => ((k : ℚ) * a) :: derivAux (k + 1) as

/-- Computable formal derivative of a rational coefficient list, trimmed. -/
@[expose] def derivList : List ℚ → List ℚ
  | [] => []
  | _ :: as => trim (derivAux 1 as)

/-- Pointwise `addList` corresponds to polynomial addition under `ofCoeffList`. -/
theorem ofCoeffList_addList (as bs : List ℚ) :
    ofCoeffList (addList as bs) = ofCoeffList as + ofCoeffList bs := by
  induction as generalizing bs with
  | nil => simp only [addList, ofCoeffList_nil, zero_add]
  | cons a as ih =>
    cases bs with
    | nil => simp only [addList, ofCoeffList_nil, add_zero]
    | cons b bs =>
      simp only [addList, ofCoeffList_cons, ih, C_add, mul_add]
      ring

/-- Pointwise `subList` corresponds to polynomial subtraction under `ofCoeffList`. -/
theorem ofCoeffList_subList (as bs : List ℚ) :
    ofCoeffList (subList as bs) = ofCoeffList as - ofCoeffList bs := by
  rw [subList, ofCoeffList_addList, negList, ofCoeffList_map_neg, sub_eq_add_neg]

/-- Prepending `k` zeros via `shiftZero` multiplies `ofCoeffList bs` by `X ^ k`. -/
theorem ofCoeffList_shiftZero (k : ℕ) (bs : List ℚ) :
    ofCoeffList (shiftZero k bs) = X ^ k * ofCoeffList bs := by
  rw [shiftZero, ofCoeffList_append, ofCoeffList_replicate_zero, zero_add, List.length_replicate]

private theorem derivAux_length (k : ℕ) (as : List ℚ) :
    (derivAux k as).length = as.length := by
  induction as generalizing k with
  | nil => simp only [derivAux, List.length_nil]
  | cons _ as ih => simp only [derivAux, List.length_cons, ih]

private theorem coeff_ofCoeffList_derivAux (k : ℕ) (as : List ℚ) (i : ℕ) :
    (ofCoeffList (derivAux k as)).coeff i = ((k + i : ℕ) : ℚ) * (ofCoeffList as).coeff i := by
  induction as generalizing k i with
  | nil => simp only [derivAux, ofCoeffList_nil, coeff_zero, mul_zero]
  | cons a as ih =>
    cases i with
    | zero =>
      simp only [derivAux, ofCoeffList_cons, coeff_add, coeff_C_zero, coeff_X_mul_zero, add_zero]
    | succ i =>
      simp only [derivAux, ofCoeffList_cons, coeff_add, coeff_C_succ, zero_add, coeff_X_mul]
      rw [ih (k + 1) i]
      have hidx : k + 1 + i = k + (i + 1) := by omega
      rw [hidx]

/-- `derivList as` represents `derivative (ofCoeffList as)`. -/
theorem ofCoeffList_derivList (as : List ℚ) :
    ofCoeffList (derivList as) = derivative (ofCoeffList as) := by
  cases as with
  | nil => simp only [derivList, ofCoeffList_nil, derivative_zero]
  | cons a as =>
    rw [derivList, ofCoeffList_trim]
    ext i
    rw [coeff_ofCoeffList_derivAux 1 as i, ofCoeffList_cons, coeff_derivative,
      coeff_add, coeff_C_succ, zero_add, coeff_X_mul, mul_comm]
    have hidx : (1 + i : ℕ) = i + 1 := by omega
    rw [hidx, Nat.cast_add, Nat.cast_one]

/-- Every output of `derivList` is trimmed (`IsTrimmed`). -/
theorem isTrimmed_derivList (as : List ℚ) : IsTrimmed (derivList as) := by
  cases as with
  | nil => exact isTrimmed_nil
  | cons _ as => exact isTrimmed_trim _

/-- `derivList as` has length at most `as.length - 1`. -/
theorem derivList_length_le (as : List ℚ) : (derivList as).length ≤ as.length - 1 := by
  cases as with
  | nil => simp only [derivList, List.length_nil, Nat.zero_sub, le_refl]
  | cons _ as =>
    simp only [derivList, List.length_cons, Nat.add_sub_cancel]
    exact (trim_length_le _).trans (derivAux_length 1 as).le

/-- Fuel-bounded polynomial Euclidean division on trimmed lists (`u` by nonempty `v`). -/
@[expose] def divModAux : ℕ → List ℚ → List ℚ → List ℚ × List ℚ
  | 0, u, _ => ([], trim u)
  | n + 1, u, v =>
    let u' := trim u
    if u'.length < v.length then
      ([], u')
    else
      match v.getLast?, u'.getLast? with
      | some lc, some lu =>
        let shift := u'.length - v.length
        let factor := lu / lc
        let subtrahend := scaleList factor (shiftZero shift v)
        let uNext := trim (subList u' subtrahend)
        let res := divModAux n uNext v
        (addList res.1 (shiftZero shift [factor]), res.2)
      | _, _ => ([], u')

/-- Computable Euclidean quotient and remainder on `List ℚ`. -/
@[expose] def divModList (u v : List ℚ) : List ℚ × List ℚ :=
  let u' := trim u
  let v' := trim v
  divModAux u'.length u' v'

/-- Computable negated remainder `-u % v` on `List ℚ`, trimmed. -/
@[expose] def negModList (u v : List ℚ) : List ℚ :=
  Prod.snd (divModList (negList u) v)

private theorem subList_step_length_lt {u' v : List ℚ} (_hu' : IsTrimmed u') (hv : IsTrimmed v)
    (hv0 : v ≠ []) (huv : v.length ≤ u'.length) {lc lu : ℚ}
    (hlc : v.getLast? = some lc) (hlu : u'.getLast? = some lu) :
    (trim (subList u' (scaleList (lu / lc) (shiftZero (u'.length - v.length) v)))).length <
      u'.length := by
  let shift := u'.length - v.length
  let factor := lu / lc
  let subtrahend := scaleList factor (shiftZero shift v)
  let uNext := trim (subList u' subtrahend)
  have hu0 : u' ≠ [] :=
    List.ne_nil_of_length_pos (lt_of_lt_of_le (List.length_pos_of_ne_nil hv0) huv)
  have hlc0 : lc ≠ 0 := by
    intro h0
    rw [h0] at hlc
    exact hv hlc
  have hsub_len : subtrahend.length = u'.length := by
    simp only [subtrahend, scaleList, List.length_map, shiftZero, List.length_append,
      List.length_replicate, shift]
    omega
  have hcoeff_zero : ∀ i, u'.length - 1 ≤ i → (ofCoeffList uNext).coeff i = 0 := by
    intro i hi
    rw [ofCoeffList_trim, ofCoeffList_subList, coeff_sub]
    dsimp only [subtrahend, scaleList]
    rw [ofCoeffList_map_mul, ofCoeffList_shiftZero, coeff_C_mul]
    rcases eq_or_lt_of_le hi with hEq | hLt
    · subst hEq
      have hshift_le : shift ≤ u'.length - 1 := by
        have hv1 : 1 ≤ v.length := List.length_pos_of_ne_nil hv0
        omega
      rw [coeff_last_of_getLast?_eq hlu, coeff_X_pow_mul']
      simp only [hshift_le, ↓reduceIte]
      have hidx : u'.length - 1 - shift = v.length - 1 := by
        have hv1 : 1 ≤ v.length := List.length_pos_of_ne_nil hv0
        omega
      rw [hidx, coeff_last_of_getLast?_eq hlc, div_mul_cancel₀ lu hlc0, sub_self]
    · have hi_ge : u'.length ≤ i := by
        have hu1 : 1 ≤ u'.length := List.length_pos_of_ne_nil hu0
        omega
      rw [coeff_ofCoeffList_eq_zero_of_le u' hi_ge]
      have hsub0 : (ofCoeffList subtrahend).coeff i = 0 :=
        coeff_ofCoeffList_eq_zero_of_le subtrahend (hsub_len ▸ hi_ge)
      dsimp only [subtrahend, scaleList] at hsub0
      rw [ofCoeffList_map_mul, ofCoeffList_shiftZero, coeff_C_mul] at hsub0
      rw [hsub0, sub_self]
  change uNext.length < u'.length
  by_cases hun : uNext = []
  · rw [hun, List.length_nil]
    exact List.length_pos_of_ne_nil hu0
  · have hlast_ne : (ofCoeffList uNext).coeff (uNext.length - 1) ≠ 0 :=
      (isTrimmed_trim _).coeff_last_ne_zero hun
    have hlt : uNext.length - 1 < u'.length - 1 := by
      by_contra hge
      exact hlast_ne (hcoeff_zero _ (Nat.le_of_not_lt hge))
    have huNext_pos : 1 ≤ uNext.length := List.length_pos_of_ne_nil hun
    omega

private theorem divModAux_spec : ∀ (n : ℕ) (u v : List ℚ),
    IsTrimmed v → v ≠ [] → (trim u).length ≤ n →
    let res := divModAux n u v
    IsTrimmed res.2 ∧ res.2.length < v.length ∧
      ofCoeffList u = ofCoeffList res.1 * ofCoeffList v + ofCoeffList res.2
  | 0, u, v, _, hv0, hlen => by
    have hu' : trim u = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hlen)
    simp only [divModAux, ofCoeffList_nil, zero_mul, zero_add]
    refine ⟨isTrimmed_trim u, ?_, ?_⟩
    · rw [hu', List.length_nil]
      exact List.length_pos_of_ne_nil hv0
    · rw [← ofCoeffList_trim u]
  | n + 1, u, v, hv, hv0, hlen => by
    simp only [divModAux]
    by_cases hlt : (trim u).length < v.length
    · simp only [hlt, ↓reduceIte, ofCoeffList_nil, zero_mul, zero_add, true_and]
      exact ⟨isTrimmed_trim u, (ofCoeffList_trim u).symm⟩
    · have huv : v.length ≤ (trim u).length := Nat.le_of_not_lt hlt
      have hu0 : trim u ≠ [] :=
        List.ne_nil_of_length_pos (lt_of_lt_of_le (List.length_pos_of_ne_nil hv0) huv)
      obtain ⟨lc, hlc, _⟩ := hv.getLast?_ne_zero hv0
      obtain ⟨lu, hlu, _⟩ := (isTrimmed_trim u).getLast?_ne_zero hu0
      simp only [hlt, ↓reduceIte, hlc, hlu]
      let shift := (trim u).length - v.length
      let factor := lu / lc
      let subtrahend := scaleList factor (shiftZero shift v)
      let uNext := trim (subList (trim u) subtrahend)
      have huNext_lt : uNext.length < (trim u).length :=
        subList_step_length_lt (isTrimmed_trim u) hv hv0 huv hlc hlu
      have hlen_next : (trim uNext).length ≤ n := by
        have h1 : (trim uNext).length ≤ uNext.length := trim_length_le uNext
        omega
      have ih := divModAux_spec n uNext v hv hv0 hlen_next
      rcases ih with ⟨htr, hrlen, heq⟩
      refine ⟨htr, hrlen, ?_⟩
      have hstep : ofCoeffList u =
          C factor * (X ^ shift * ofCoeffList v) + ofCoeffList uNext := by
        rw [← ofCoeffList_trim u]
        have huNext_eq : ofCoeffList uNext =
            ofCoeffList (trim u) - C factor * (X ^ shift * ofCoeffList v) := by
          rw [ofCoeffList_trim, ofCoeffList_subList]
          dsimp only [subtrahend, scaleList]
          rw [ofCoeffList_map_mul, ofCoeffList_shiftZero]
        rw [huNext_eq]
        ring
      rw [hstep, heq, ofCoeffList_addList, ofCoeffList_shiftZero, ofCoeffList_cons,
        ofCoeffList_nil, mul_zero, add_zero]
      ring

/-- Correctness of `divModList u v` when `ofCoeffList v ≠ 0`: trimmed remainder of strictly
shorter length satisfying `ofCoeffList u = ofCoeffList q * ofCoeffList v + ofCoeffList r`. -/
theorem divModList_spec {u v : List ℚ} (hv0 : ofCoeffList v ≠ 0) :
    let res := divModList u v
    IsTrimmed res.2 ∧ res.2.length < (trim v).length ∧
      ofCoeffList u = ofCoeffList res.1 * ofCoeffList v + ofCoeffList res.2 := by
  have hv_trim : IsTrimmed (trim v) := isTrimmed_trim v
  have hv_ne : trim v ≠ [] := fun hnil =>
    hv0 (by rw [← ofCoeffList_trim v, hnil, ofCoeffList_nil])
  have hspec := divModAux_spec (trim u).length (trim u) (trim v) hv_trim hv_ne
    (trim_length_le (trim u))
  simpa only [divModList, ofCoeffList_trim] using hspec

/-- `negModList u v` represents the negated Euclidean remainder `-(ofCoeffList u) % ofCoeffList v`
with a trimmed, shorter coefficient list. -/
theorem ofCoeffList_negModList {u v : List ℚ} (hv0 : ofCoeffList v ≠ 0) :
    IsTrimmed (negModList u v) ∧ (negModList u v).length < (trim v).length ∧
      ofCoeffList (negModList u v) = -(ofCoeffList u) % ofCoeffList v := by
  have hv_trim : IsTrimmed (trim v) := isTrimmed_trim v
  have hv_ne : trim v ≠ [] := fun hnil =>
    hv0 (by rw [← ofCoeffList_trim v, hnil, ofCoeffList_nil])
  have ⟨htr, hrlen, heq⟩ := divModList_spec (u := negList u) hv0
  change IsTrimmed (negModList u v) ∧ (negModList u v).length < (trim v).length ∧ _ at *
  refine ⟨htr, hrlen, ?_⟩
  have hdeg_lt : (ofCoeffList (negModList u v)).degree < (ofCoeffList v).degree := by
    rw [← ofCoeffList_trim v]
    exact htr.degree_lt_of_length_lt hv_trim hv_ne hrlen
  have hneg : -(ofCoeffList u) =
      ofCoeffList (divModList (negList u) v).1 * ofCoeffList v + ofCoeffList (negModList u v) := by
    rw [← ofCoeffList_map_neg u]
    exact heq
  rw [hneg, Polynomial.add_mod, EuclideanDomain.mod_eq_zero.mpr (dvd_mul_left _ _), zero_add,
    (Polynomial.mod_eq_self_iff hv0).mpr hdeg_lt]

/-- Fuel-bounded computable Sturm sequence on trimmed lists. -/
@[expose] def sturmSeqAux : ℕ → List ℚ → List ℚ → List (List ℚ)
  | 0, p, _ => [p]
  | n + 1, p, q =>
    if q.isEmpty then [p]
    else p :: sturmSeqAux n q (negModList p q)

/-- Computable Sturm sequence of a rational coefficient list `cs`. -/
@[expose] def sturmSeqList (cs : List ℚ) : List (List ℚ) :=
  let p := trim cs
  if p.isEmpty then []
  else
    let dp := derivList p
    sturmSeqAux dp.length p dp

private theorem sturmSeqAux_spec : ∀ (n : ℕ) (p q : List ℚ),
    IsTrimmed p → p ≠ [] → IsTrimmed q → q.length ≤ n →
    (sturmSeqAux n p q).map ofCoeffList = Polynomial.sturmSeq (ofCoeffList p) (ofCoeffList q) ∧
      (sturmSeqAux n p q).length ≤ n + 1 ∧
      ∀ f ∈ sturmSeqAux n p q, f.length ≤ max p.length q.length
  | 0, p, q, hp, hp0, _, hqn => by
    have hq_nil : q = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hqn)
    subst hq_nil
    have hp_ne : ofCoeffList p ≠ 0 := hp.ofCoeffList_ne_zero hp0
    simp only [sturmSeqAux, List.map_cons, List.map_nil, ofCoeffList_nil,
      Polynomial.sturmSeq_zero_right]
    rw [ite_eq_right (fun h => absurd h hp_ne)]
    refine ⟨rfl, by simp only [List.length_singleton]; omega, fun f hf => ?_⟩
    rw [List.mem_singleton] at hf
    subst hf
    exact le_max_left _ _
  | n + 1, p, q, hp, hp0, hq, hqn => by
    have hp_ne : ofCoeffList p ≠ 0 := hp.ofCoeffList_ne_zero hp0
    by_cases hqe : q.isEmpty = true
    · have hq_nil : q = [] := List.isEmpty_iff.mp hqe
      subst hq_nil
      simp only [sturmSeqAux, hqe, ↓reduceIte, List.map_cons, List.map_nil, ofCoeffList_nil,
        Polynomial.sturmSeq_zero_right]
      rw [ite_eq_right (fun h => absurd h hp_ne)]
      refine ⟨rfl, by simp only [List.length_singleton]; omega, fun f hf => ?_⟩
      rw [List.mem_singleton] at hf
      subst hf
      exact le_max_left _ _
    · have hq0 : q ≠ [] := fun hnil => hqe (List.isEmpty_iff.mpr hnil)
      have hq_ne : ofCoeffList q ≠ 0 := hq.ofCoeffList_ne_zero hq0
      obtain ⟨hr_trim, hr_len, hr_mod⟩ := ofCoeffList_negModList (u := p) hq_ne
      have hr_len_q : (negModList p q).length < q.length :=
        lt_of_lt_of_le hr_len (trim_length_le q)
      have hr_le_n : (negModList p q).length ≤ n := by omega
      have ih := sturmSeqAux_spec n q (negModList p q) hq hq0 hr_trim hr_le_n
      rcases ih with ⟨ih_map, ih_len, ih_mem⟩
      simp only [sturmSeqAux, hqe, Bool.false_eq_true, ↓reduceIte, List.map_cons, List.length_cons,
        List.mem_cons]
      refine ⟨?_, ?_, ?_⟩
      · rw [Polynomial.sturmSeq_cons hp_ne, ih_map, hr_mod]
      · omega
      · rintro f (rfl | hf)
        · exact le_max_left _ _
        · refine (ih_mem f hf).trans (max_le (le_max_right _ _) ?_)
          exact le_trans hr_len_q.le (le_max_right _ _)

/-- `sturmSeqList cs` represents
`Polynomial.sturmSeq (ofCoeffList cs) (derivative (ofCoeffList cs))` elementwise under
`ofCoeffList`. -/
theorem sturmSeqList_map_ofCoeffList (cs : List ℚ) :
    (sturmSeqList cs).map ofCoeffList =
      Polynomial.sturmSeq (ofCoeffList cs) (derivative (ofCoeffList cs)) := by
  simp only [sturmSeqList]
  by_cases he : (trim cs).isEmpty = true
  · have hnil : trim cs = [] := List.isEmpty_iff.mp he
    have h0 : ofCoeffList cs = 0 := by rw [← ofCoeffList_trim cs, hnil, ofCoeffList_nil]
    simp only [he, ↓reduceIte, List.map_nil, h0, derivative_zero, Polynomial.sturmSeq_zero_left]
  · have hne : trim cs ≠ [] := fun hnil => he (List.isEmpty_iff.mpr hnil)
    have hspec := sturmSeqAux_spec (derivList (trim cs)).length (trim cs) (derivList (trim cs))
      (isTrimmed_trim cs) hne (isTrimmed_derivList (trim cs)) le_rfl
    simp only [he, Bool.false_eq_true, ↓reduceIte]
    rw [hspec.1, ofCoeffList_derivList, ofCoeffList_trim]

/-- Length bound `(sturmSeqList cs).length ≤ (ofCoeffList cs).natDegree + 1`. -/
theorem sturmSeqList_length_le (cs : List ℚ) :
    (sturmSeqList cs).length ≤ (ofCoeffList cs).natDegree + 1 := by
  simp only [sturmSeqList]
  by_cases he : (trim cs).isEmpty = true
  · simp only [he, ↓reduceIte, List.length_nil, Nat.zero_le]
  · have hne : trim cs ≠ [] := fun hnil => he (List.isEmpty_iff.mpr hnil)
    have hspec := sturmSeqAux_spec (derivList (trim cs)).length (trim cs) (derivList (trim cs))
      (isTrimmed_trim cs) hne (isTrimmed_derivList (trim cs)) le_rfl
    simp only [he, Bool.false_eq_true, ↓reduceIte]
    have hdp_len : (derivList (trim cs)).length ≤ (trim cs).length - 1 :=
      derivList_length_le (trim cs)
    have hdeg : (ofCoeffList cs).natDegree + 1 = (trim cs).length := by
      rw [← ofCoeffList_trim cs]
      exact (isTrimmed_trim cs).natDegree_add_one hne
    omega

/-- Entry length bound: every list in `sturmSeqList cs` has length at most `(trim cs).length`. -/
theorem sturmSeqList_entry_length_le (cs : List ℚ) {f : List ℚ} (hf : f ∈ sturmSeqList cs) :
    f.length ≤ (trim cs).length := by
  simp only [sturmSeqList] at hf
  by_cases he : (trim cs).isEmpty = true
  · simp only [he, ↓reduceIte, List.not_mem_nil] at hf
  · have hne : trim cs ≠ [] := fun hnil => he (List.isEmpty_iff.mpr hnil)
    have hspec := sturmSeqAux_spec (derivList (trim cs)).length (trim cs) (derivList (trim cs))
      (isTrimmed_trim cs) hne (isTrimmed_derivList (trim cs)) le_rfl
    simp only [he, Bool.false_eq_true, ↓reduceIte] at hf
    have hdp_len : (derivList (trim cs)).length ≤ (trim cs).length :=
      (derivList_length_le (trim cs)).trans (Nat.sub_le _ _)
    exact (hspec.2.2 f hf).trans (max_le le_rfl hdp_len)

/-- Rational Sturm sign variations of a precomputed Sturm sequence at `x : ℚ`. -/
@[expose] def sturmVariationsList (seq : List (List ℚ)) (x : ℚ) : ℕ :=
  (seq.map (evalCoeffList x)).signVariations

/-- `sturmVariationsList (sturmSeqList cs) x` equals the real Sturm sign-variation count
`Polynomial.sturmVariations ((ofCoeffList cs).map (algebraMap ℚ ℝ)) (x : ℝ)`. -/
theorem sturmVariationsList_eq_sturmVariations (cs : List ℚ) (x : ℚ) :
    sturmVariationsList (sturmSeqList cs) x =
      Polynomial.sturmVariations ((ofCoeffList cs).map (algebraMap ℚ ℝ)) (x : ℝ) := by
  rw [Polynomial.sturmVariations, Polynomial.derivative_map,
    Polynomial.sturmSeq_map (algebraMap ℚ ℝ), ← sturmSeqList_map_ofCoeffList cs, List.map_map,
    List.map_map]
  have hlist : (List.map (fun g => eval (x : ℝ) ((ofCoeffList g).map (algebraMap ℚ ℝ)))
      (sturmSeqList cs)) =
      (sturmSeqList cs |>.map (evalCoeffList x)).map (algebraMap ℚ ℝ) := by
    rw [List.map_map]
    refine List.map_congr_left fun g _ => ?_
    have heval : eval ((algebraMap ℚ ℝ) x) ((ofCoeffList g).map (algebraMap ℚ ℝ)) =
        (algebraMap ℚ ℝ) (eval x (ofCoeffList g)) := by
      rw [Polynomial.eval_map, Polynomial.eval₂_hom]
    change eval ((algebraMap ℚ ℝ) x) ((ofCoeffList g).map (algebraMap ℚ ℝ)) = _
    rw [heval, eval_ofCoeffList]
    rfl
  change _ =
      (List.map (fun g => eval (x : ℝ) ((ofCoeffList g).map (algebraMap ℚ ℝ)))
        (sturmSeqList cs)).signVariations
  rw [hlist, sturmVariationsList]
  refine (List.signVariations_map (fun q => ?_) _).symm
  change SignType.sign (q : ℝ) = SignType.sign q
  rcases lt_trichotomy q 0 with hlt | rfl | hgt
  · have hR : (q : ℝ) < 0 := Rat.cast_lt_zero.mpr hlt
    rw [sign_neg hlt, sign_neg hR]
  · simp only [Rat.cast_zero, sign_zero]
  · have hR : (0 : ℝ) < (q : ℝ) := Rat.cast_pos.mpr hgt
    rw [sign_pos hgt, sign_pos hR]

/-- Maximum absolute value among a list of rational numbers (`0` on `[]`). -/
@[expose] def maxAbsList : List ℚ → ℚ
  | [] => 0
  | a :: as => max |a| (maxAbsList as)

/-- Nonnegativity of `maxAbsList l`. -/
theorem maxAbsList_nonneg (l : List ℚ) : 0 ≤ maxAbsList l := by
  induction l with
  | nil => exact le_rfl
  | cons a l ih => exact le_trans (abs_nonneg a) (le_max_left _ _)

/-- Every indexed entry `l.getD i 0` has absolute value at most `maxAbsList l`. -/
theorem abs_getD_le_maxAbsList (l : List ℚ) (i : ℕ) : |l.getD i 0| ≤ maxAbsList l := by
  induction l generalizing i with
  | nil => simp only [List.getD_eq_getElem?_getD, List.getElem?_nil, Option.getD_none, abs_zero,
      maxAbsList, le_refl]
  | cons a l ih =>
    cases i with
    | zero =>
      simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_zero, Option.getD_some,
        maxAbsList]
      exact le_max_left _ _
    | succ i =>
      simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_succ]
      exact (ih i).trans (le_max_right _ _)

/-- Computable positive integer upper bound strictly greater than the absolute value of every
real root of `ofCoeffList cs`. -/
@[expose] def cauchyBoundNat (cs : List ℚ) : ℕ :=
  let t := trim cs
  if t.length ≤ 1 then 1
  else
    let lc := Option.getD t.getLast? 1
    let m := maxAbsList t.dropLast
    let b := m / |lc| + 1
    Int.natAbs b.num / b.den + 1

/-- `cauchyBoundNat cs` is always at least `1`. -/
theorem one_le_cauchyBoundNat (cs : List ℚ) : 1 ≤ cauchyBoundNat cs := by
  simp only [cauchyBoundNat]
  split_ifs
  · exact le_rfl
  · exact Nat.le_add_left 1 _

private theorem getD_dropLast_of_lt {α : Type*} (l : List α) (d : α) {i : ℕ}
    (hi : i < l.length - 1) : l.dropLast.getD i d = l.getD i d := by
  have hi' : i < l.dropLast.length := by
    rw [List.length_dropLast]
    exact hi
  have hi_l : i < l.length := Nat.lt_of_lt_of_le hi (Nat.sub_le _ _)
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hi', List.getElem?_eq_getElem hi_l, Option.getD_some,
    Option.getD_some, List.getElem_dropLast]

/-- Every real root `r` of `(ofCoeffList cs).map (algebraMap ℚ ℝ)` (when nonzero) satisfies
`|r| < cauchyBoundNat cs`. -/
theorem abs_lt_cauchyBoundNat_of_isRoot {cs : List ℚ} (hcs : ofCoeffList cs ≠ 0) {r : ℝ}
    (hr : ((ofCoeffList cs).map (algebraMap ℚ ℝ)).IsRoot r) :
    |r| < (cauchyBoundNat cs : ℝ) := by
  let t := trim cs
  have ht : IsTrimmed t := isTrimmed_trim cs
  have hq : ofCoeffList t = ofCoeffList cs := ofCoeffList_trim cs
  have ht0 : ofCoeffList t ≠ 0 := hq ▸ hcs
  have htnil : t ≠ [] := fun hnil => ht0 (by rw [hnil, ofCoeffList_nil])
  have hdeg : (ofCoeffList t).natDegree + 1 = t.length := ht.natDegree_add_one htnil
  have hr' : ((ofCoeffList t).map (algebraMap ℚ ℝ)).IsRoot r := hq ▸ hr
  dsimp only [cauchyBoundNat]
  split_ifs with hlen
  · have hlen' : t.length ≤ 1 := hlen
    have hdeg0 : (ofCoeffList t).natDegree = 0 := by omega
    have hc : ofCoeffList t = C ((ofCoeffList t).coeff 0) := eq_C_of_natDegree_eq_zero hdeg0
    have hc0 : (ofCoeffList t).coeff 0 ≠ 0 := by
      intro h0
      apply ht0
      rw [hc, h0, C_0]
    exfalso
    rw [hc, Polynomial.map_C, IsRoot.def, eval_C, eq_ratCast] at hr'
    exact hc0 (Rat.cast_injective (α := ℝ) (hr'.trans Rat.cast_zero.symm))
  · obtain ⟨lc, hlc, hlc0⟩ := ht.getLast?_ne_zero htnil
    have hlead : (ofCoeffList t).leadingCoeff = lc := by
      rw [leadingCoeff, (by omega : (ofCoeffList t).natDegree = t.length - 1),
        coeff_last_of_getLast?_eq hlc]
    have hlc_eq : Option.getD t.getLast? 1 = lc := by rw [hlc, Option.getD_some]
    have hm :
        ∀ i < (ofCoeffList t).natDegree, |(ofCoeffList t).coeff i| ≤ maxAbsList t.dropLast := by
      intro i hi
      rw [coeff_ofCoeffList, ← getD_dropLast_of_lt t 0 (by omega)]
      exact abs_getD_le_maxAbsList t.dropLast i
    have hcb := abs_lt_cauchyBound_of_forall_coeff_le ht0 (maxAbsList_nonneg _) hm hr'
    rw [hlead] at hcb
    let b := maxAbsList t.dropLast / |lc| + 1
    have hb_nonneg : 0 ≤ b :=
      add_nonneg (div_nonneg (maxAbsList_nonneg _) (abs_nonneg _)) zero_le_one
    have hb_eq_abs : |b| = b := abs_of_nonneg hb_nonneg
    have hrat_lt : b < ((Int.natAbs b.num / b.den + 1 : ℕ) : ℚ) := by
      have hden_pos : 0 < b.den := b.den_pos
      have hnum_eq : (Int.natAbs b.num : ℚ) / (b.den : ℚ) = |b| := by
        calc (Int.natAbs b.num : ℚ) / (b.den : ℚ)
            = |(b.num : ℚ)| / |(b.den : ℚ)| := by
                rw [Nat.abs_cast, ← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
          _ = |(b.num : ℚ) / (b.den : ℚ)| := (abs_div _ _).symm
          _ = |b| := by rw [Rat.num_div_den]
      have hdiv : Int.natAbs b.num < (Int.natAbs b.num / b.den + 1) * b.den := by
        rw [Nat.add_one_mul]
        exact Nat.lt_div_mul_add hden_pos
      have hdivQ : (Int.natAbs b.num : ℚ) <
          ((Int.natAbs b.num / b.den + 1 : ℕ) : ℚ) * (b.den : ℚ) := by
        exact_mod_cast hdiv
      conv_lhs => rw [← hb_eq_abs, ← hnum_eq]
      exact (div_lt_iff₀ (by exact_mod_cast hden_pos)).mpr hdivQ
    have hreal_lt : (b : ℝ) < ((Int.natAbs b.num / b.den + 1 : ℕ) : ℝ) := by
      exact_mod_cast hrat_lt
    rw [hlc_eq]
    exact lt_trans hcb hreal_lt

/-- Lowest common multiple of all denominators in a rational coefficient list. -/
@[expose] def lcmDens : List ℚ → ℕ
  | [] => 1
  | q :: qs => Nat.lcm q.den (lcmDens qs)

/-- `lcmDens cs` is always positive (`1 ≤ lcmDens cs`). -/
theorem one_le_lcmDens (cs : List ℚ) : 1 ≤ lcmDens cs := by
  induction cs with
  | nil => simp only [lcmDens, le_refl]
  | cons q qs ih =>
    simp only [lcmDens]
    exact Nat.pos_of_ne_zero (Nat.lcm_ne_zero (Rat.den_nz q) (by omega))

/-- Every element's denominator divides `lcmDens cs`. -/
theorem dvd_lcmDens {cs : List ℚ} {q : ℚ} (hq : q ∈ cs) : q.den ∣ lcmDens cs := by
  induction cs with
  | nil => cases hq
  | cons a as ih =>
    simp only [lcmDens]
    rcases List.mem_cons.mp hq with rfl | hmem
    · exact Nat.dvd_lcm_left _ _
    · exact dvd_trans (ih hmem) (Nat.dvd_lcm_right _ _)

/-- Clear denominators of `cs : List ℚ`, returning `(D, ns)` with `1 ≤ D` and
`ns.map (↑) = cs.map (D * ·)`. -/
@[expose] def clearDenomsList (cs : List ℚ) : ℕ × List ℤ :=
  let D := lcmDens cs
  (D, cs.map fun q => q.num * ((D / q.den : ℕ) : ℤ))

private theorem ofCoeffList_clearDenoms_aux (D : ℕ) (cs : List ℚ)
    (hD : ∀ q ∈ cs, q.den ∣ D) :
    (ofCoeffList (cs.map fun q => q.num * ((D / q.den : ℕ) : ℤ))).map (algebraMap ℤ ℚ) =
      C (D : ℚ) * ofCoeffList cs := by
  induction cs with
  | nil => simp only [List.map_nil, ofCoeffList_nil, Polynomial.map_zero, mul_zero]
  | cons q cs ih =>
    simp only [List.map_cons, ofCoeffList_cons, Polynomial.map_add, Polynomial.map_C,
      Polynomial.map_mul, Polynomial.map_X]
    have hq_dvd : q.den ∣ D := hD q List.mem_cons_self
    have hcast_div : (((D / q.den : ℕ) : ℤ) : ℚ) = (D : ℚ) / (q.den : ℚ) := by
      have hd_pos : (q.den : ℚ) ≠ 0 := by exact_mod_cast Rat.den_nz q
      rw [Int.cast_natCast, eq_div_iff hd_pos]
      exact_mod_cast Nat.div_mul_cancel hq_dvd
    have hterm : ((q.num * ((D / q.den : ℕ) : ℤ) : ℤ) : ℚ) = (D : ℚ) * q := by
      rw [Int.cast_mul, hcast_div, mul_div_assoc', mul_comm (q.num : ℚ) (D : ℚ),
        mul_div_assoc, Rat.num_div_den]
    change C ((q.num * ((D / q.den : ℕ) : ℤ) : ℤ) : ℚ) +
        X * (ofCoeffList (cs.map fun q => q.num * ((D / q.den : ℕ) : ℤ))).map (algebraMap ℤ ℚ) =
      C (D : ℚ) * (C q + X * ofCoeffList cs)
    rw [hterm, ih (fun a ha => hD a (List.mem_cons_of_mem q ha)), C_mul]
    ring

/-- `(clearDenomsList cs).2` represents `(clearDenomsList cs).1 * ofCoeffList cs` over `ℚ[X]`. -/
theorem ofCoeffList_clearDenomsList (cs : List ℚ) :
    (ofCoeffList (clearDenomsList cs).2).map (algebraMap ℤ ℚ) =
      C ((clearDenomsList cs).1 : ℚ) * ofCoeffList cs :=
  ofCoeffList_clearDenoms_aux (lcmDens cs) cs (fun _ hq => dvd_lcmDens hq)

/-- The clearing multiplier `(clearDenomsList cs).1` is always at least `1`. -/
theorem one_le_clearDenomsList_fst (cs : List ℚ) : 1 ≤ (clearDenomsList cs).1 :=
  one_le_lcmDens cs

/-- Sum of squares of an integer coefficient list. -/
@[expose] def sqNormList (ns : List ℤ) : ℕ :=
  ns.foldl (fun acc a => acc + Int.natAbs a ^ 2) 0

private theorem foldl_sqNorm (acc : ℕ) (ns : List ℤ) :
    ns.foldl (fun s a => s + Int.natAbs a ^ 2) acc =
      acc + ∑ i ∈ Finset.range ns.length, (Int.natAbs (ns.getD i 0)) ^ 2 := by
  induction ns generalizing acc with
  | nil => simp only [List.foldl_nil, List.length_nil, Finset.range_zero, Finset.sum_empty,
      add_zero]
  | cons a ns ih =>
    simp only [List.foldl_cons, List.length_cons, ih (acc + Int.natAbs a ^ 2)]
    rw [Finset.sum_range_succ']
    simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.getD_some]
    omega

/-- `coeffSqNorm (ofCoeffList ns)` is bounded above by `sqNormList ns`. -/
theorem coeffSqNorm_ofCoeffList_le (ns : List ℤ) :
    coeffSqNorm (ofCoeffList ns) ≤ sqNormList ns := by
  rw [sqNormList, foldl_sqNorm, zero_add, coeffSqNorm_eq_sum_range]
  by_cases h0 : ofCoeffList ns = 0
  · simp only [h0, natDegree_zero, zero_add, Finset.range_one, Finset.sum_singleton, coeff_zero,
      Int.natAbs_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Nat.zero_le]
  · have hne : ns ≠ [] := fun hnil => h0 (by rw [hnil, ofCoeffList_nil])
    have hdeg : (ofCoeffList ns).natDegree + 1 ≤ ns.length := by
      have hle := natDegree_ofCoeffList_le ns
      have hpos : 1 ≤ ns.length := List.length_pos_of_ne_nil hne
      omega
    refine Finset.sum_le_sum_of_subset (Finset.range_mono hdeg) |>.trans_eq ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [coeff_ofCoeffList]

/-- Mignotte squared-separation denominator `d ^ (d + 2) * sqNormList ns ^ (d - 1)`. -/
@[expose] def mignotteSepSqInv (cs : List ℚ) : ℕ :=
  let t := trim cs
  let d := t.length - 1
  let ns := Prod.snd (clearDenomsList t)
  d ^ (d + 2) * (sqNormList ns) ^ (d - 1)

/-- Computable Mignotte bisection depth `K` ensuring dyadic width `2 * B / 2 ^ K` is strictly
smaller than any root gap when `2 ≤ deg p` (`0` when `deg p ≤ 1`). -/
@[expose] def mignotteBisectionDepth (cs : List ℚ) : ℕ :=
  let t := trim cs
  if t.length ≤ 2 then 0
  else
    let b := cauchyBoundNat cs
    let s := mignotteSepSqInv cs
    Nat.clog 4 (4 * b ^ 2 * s / 3 + 1)

/-- `mignotteBisectionDepth cs` vanishes whenever `(ofCoeffList cs).natDegree ≤ 1`. -/
theorem mignotteBisectionDepth_eq_zero_of_natDegree_le_one {cs : List ℚ}
    (hd : (ofCoeffList cs).natDegree ≤ 1) : mignotteBisectionDepth cs = 0 := by
  simp only [mignotteBisectionDepth]
  by_cases h0 : trim cs = []
  · simp only [h0, List.length_nil, Nat.reduceLeDiff, ↓reduceIte]
  · have hdeg : (ofCoeffList cs).natDegree + 1 = (trim cs).length := by
      rw [← ofCoeffList_trim cs]
      exact (isTrimmed_trim cs).natDegree_add_one h0
    have hlen : (trim cs).length ≤ 2 := by omega
    simp only [hlen, ↓reduceIte]

/-- For nonzero `ofCoeffList cs`, the cleared-denominator integer coefficient squared norm is
at least `1`. -/
theorem one_le_sqNormList_clearDenoms_trim {cs : List ℚ} (hcs : ofCoeffList cs ≠ 0) :
    1 ≤ sqNormList (Prod.snd (clearDenomsList (trim cs))) := by
  let t := trim cs
  let res := clearDenomsList t
  have ht0 : ofCoeffList t ≠ 0 := by rwa [ofCoeffList_trim]
  have hD : 1 ≤ res.1 := one_le_clearDenomsList_fst t
  have hD0 : (res.1 : ℚ) ≠ 0 := by exact_mod_cast (by omega : res.1 ≠ 0)
  have hmap : (ofCoeffList res.2).map (algebraMap ℤ ℚ) = C (res.1 : ℚ) * ofCoeffList t :=
    ofCoeffList_clearDenomsList t
  have hp0 : ofCoeffList res.2 ≠ 0 := by
    intro h0
    rw [h0, Polynomial.map_zero] at hmap
    exact mul_ne_zero (C_ne_zero.mpr hD0) ht0 hmap.symm
  have hcsq_pos : 1 ≤ coeffSqNorm (ofCoeffList res.2) := by
    rw [coeffSqNorm]
    have hsupp : (ofCoeffList res.2).natDegree ∈ (ofCoeffList res.2).support :=
      mem_support_iff.mpr (leadingCoeff_ne_zero.mpr hp0)
    have hle : (Int.natAbs ((ofCoeffList res.2).coeff (ofCoeffList res.2).natDegree)) ^ 2 ≤
        ∑ i ∈ (ofCoeffList res.2).support, (Int.natAbs ((ofCoeffList res.2).coeff i)) ^ 2 :=
      Finset.single_le_sum (f := fun i => Int.natAbs ((ofCoeffList res.2).coeff i) ^ 2)
        (fun _ _ => Nat.zero_le _) hsupp
    have hlead_pos : 1 ≤ Int.natAbs ((ofCoeffList res.2).leadingCoeff) :=
      Int.natAbs_pos.mpr (leadingCoeff_ne_zero.mpr hp0)
    have hpow : 1 ≤ (Int.natAbs ((ofCoeffList res.2).leadingCoeff)) ^ 2 := by nlinarith
    exact hpow.trans hle
  exact hcsq_pos.trans (coeffSqNorm_ofCoeffList_le res.2)

/-- Dyadic bisection at depth `mignotteBisectionDepth cs` shrinks the interval width
`2 * cauchyBoundNat cs / 2 ^ K` strictly below the Mignotte separation between any two distinct
real roots of separable `ofCoeffList cs` (`2 ≤ natDegree`). -/
theorem dyadic_width_lt_root_sep {cs : List ℚ} (hsep : (ofCoeffList cs).Separable)
    (hd : 2 ≤ (ofCoeffList cs).natDegree) {α β : ℝ}
    (hα : ((ofCoeffList cs).map (algebraMap ℚ ℝ)).IsRoot α)
    (hβ : ((ofCoeffList cs).map (algebraMap ℚ ℝ)).IsRoot β) (hne : α ≠ β) :
    2 * (cauchyBoundNat cs : ℝ) / (2 : ℝ) ^ mignotteBisectionDepth cs < |α - β| := by
  let t := trim cs
  have ht0 : t ≠ [] := fun hnil => by
    have h0 : ofCoeffList cs = 0 := by
      rw [← ofCoeffList_trim cs]
      change ofCoeffList t = 0
      rw [hnil, ofCoeffList_nil]
    simp only [h0, natDegree_zero] at hd
    omega
  have hdeg_t : (ofCoeffList cs).natDegree + 1 = t.length := by
    rw [← ofCoeffList_trim cs]
    exact (isTrimmed_trim cs).natDegree_add_one ht0
  have hlen : ¬t.length ≤ 2 := by omega
  let b := cauchyBoundNat cs
  let s := mignotteSepSqInv cs
  let k := mignotteBisectionDepth cs
  have hk_eq : k = Nat.clog 4 (4 * b ^ 2 * s / 3 + 1) := by
    change (if t.length ≤ 2 then 0 else Nat.clog 4 (4 * b ^ 2 * s / 3 + 1)) = _
    rw [ite_eq_right (fun h => absurd h hlen)]
  let res := clearDenomsList t
  have hD0 : (res.1 : ℚ) ≠ 0 := by
    have hD : 1 ≤ res.1 := one_le_clearDenomsList_fst t
    exact_mod_cast Nat.ne_of_gt hD
  have hmap : (ofCoeffList res.2).map (algebraMap ℤ ℚ) =
      C (res.1 : ℚ) * ofCoeffList cs := by
    rw [← ofCoeffList_trim cs]
    exact ofCoeffList_clearDenomsList t
  have hmignotte := mignotte_sep_sqNorm_rat hd hsep hD0 hmap hα hβ hne
  have hs_ge : (ofCoeffList cs).natDegree ^ ((ofCoeffList cs).natDegree + 2) *
      coeffSqNorm (ofCoeffList res.2) ^ ((ofCoeffList cs).natDegree - 1) ≤ s := by
    have hcsq : coeffSqNorm (ofCoeffList res.2) ≤ sqNormList res.2 :=
      coeffSqNorm_ofCoeffList_le res.2
    have hd_eq : t.length - 1 = (ofCoeffList cs).natDegree := by omega
    rw [show s = (t.length - 1) ^ ((t.length - 1) + 2) * (sqNormList res.2) ^ ((t.length - 1) - 1)
      from rfl, hd_eq]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hcsq _)
  have hmignotte_s : (3 : ℝ) ≤ |α - β| ^ 2 * (s : ℝ) := by
    refine hmignotte.trans ?_
    have hsr : ((ofCoeffList cs).natDegree ^ ((ofCoeffList cs).natDegree + 2) *
        coeffSqNorm (ofCoeffList res.2) ^ ((ofCoeffList cs).natDegree - 1) : ℝ) ≤ (s : ℝ) := by
      exact_mod_cast hs_ge
    push_cast at hsr ⊢
    gcongr
  have hs_pos : (0 : ℝ) < (s : ℝ) := by
    by_contra hle
    have h0 : (s : ℝ) = 0 := le_antisymm (le_of_not_gt hle) (Nat.cast_nonneg _)
    rw [h0, mul_zero] at hmignotte_s
    linarith
  have hclog : 4 * b ^ 2 * s / 3 + 1 ≤ 4 ^ k := by
    rw [hk_eq]
    exact Nat.le_pow_clog (by decide : 1 < 4) _
  have hlt_nat : 4 * b ^ 2 * s < 3 * 4 ^ k := by omega
  have hlt_real : (4 : ℝ) * (b : ℝ) ^ 2 * (s : ℝ) < 3 * (4 : ℝ) ^ k := by
    exact_mod_cast hlt_nat
  have h4_eq : (4 : ℝ) ^ k = ((2 : ℝ) ^ k) ^ 2 := by
    rw [← pow_mul, mul_comm k 2, pow_mul]
    norm_num
  have hpow_pos : (0 : ℝ) < ((2 : ℝ) ^ k) ^ 2 := by positivity
  have hwidth_sq : (2 * (b : ℝ) / (2 : ℝ) ^ k) ^ 2 * (s : ℝ) < 3 := by
    have heq : (2 * (b : ℝ) / (2 : ℝ) ^ k) ^ 2 * (s : ℝ) =
        ((4 : ℝ) * (b : ℝ) ^ 2 * (s : ℝ)) / ((2 : ℝ) ^ k) ^ 2 := by ring
    rw [heq, div_lt_iff₀ hpow_pos, ← h4_eq]
    exact hlt_real
  have hsq_lt : (2 * (b : ℝ) / (2 : ℝ) ^ k) ^ 2 * (s : ℝ) < |α - β| ^ 2 * (s : ℝ) :=
    lt_of_lt_of_le hwidth_sq hmignotte_s
  have hsq_lt' : (2 * (b : ℝ) / (2 : ℝ) ^ k) ^ 2 < |α - β| ^ 2 :=
    (mul_lt_mul_iff_left₀ hs_pos).mp hsq_lt
  exact lt_of_pow_lt_pow_left₀ 2 (abs_nonneg _) hsq_lt'

/-- Logarithmic upper bound on `mignotteBisectionDepth cs` in terms of `cauchyBoundNat cs`,
`natDegree`, and cleared-denominator `sqNormList`. -/
theorem mignotteBisectionDepth_le (cs : List ℚ) (hd : 2 ≤ (ofCoeffList cs).natDegree) :
    mignotteBisectionDepth cs ≤
      1 + 2 * Nat.clog 4 (cauchyBoundNat cs) +
        ((ofCoeffList cs).natDegree + 2) * Nat.clog 4 (ofCoeffList cs).natDegree +
        ((ofCoeffList cs).natDegree - 1) *
          Nat.clog 4 (sqNormList (Prod.snd (clearDenomsList (trim cs)))) := by
  let t := trim cs
  have hcs0 : ofCoeffList cs ≠ 0 := fun h0 => by
    simp only [h0, natDegree_zero] at hd
    omega
  have ht0 : t ≠ [] := fun hnil => hcs0 (by
    rw [← ofCoeffList_trim cs]
    change ofCoeffList t = 0
    rw [hnil, ofCoeffList_nil])
  have hdeg_t : (ofCoeffList cs).natDegree + 1 = t.length := by
    rw [← ofCoeffList_trim cs]
    exact (isTrimmed_trim cs).natDegree_add_one ht0
  have hlen : ¬t.length ≤ 2 := by omega
  let d := (ofCoeffList cs).natDegree
  let b := cauchyBoundNat cs
  let sn := sqNormList (Prod.snd (clearDenomsList t))
  have hb_ge1 : 1 ≤ b := one_le_cauchyBoundNat cs
  have hsn_ge1 : 1 ≤ sn := one_le_sqNormList_clearDenoms_trim hcs0
  have hd_eq : t.length - 1 = d := by omega
  have hs_eq : mignotteSepSqInv cs = d ^ (d + 2) * sn ^ (d - 1) := by
    simp only [mignotteSepSqInv, t, d, sn]
    rw [hd_eq]
  have hs_ge1 : 1 ≤ mignotteSepSqInv cs := by
    rw [hs_eq]
    exact Nat.mul_pos (Nat.pow_pos (by omega)) (Nat.pow_pos hsn_ge1)
  have hx_ge1 : 1 ≤ b ^ 2 * mignotteSepSqInv cs :=
    Nat.mul_pos (Nat.pow_pos hb_ge1) hs_ge1
  have hdiv_le : 4 * b ^ 2 * mignotteSepSqInv cs / 3 + 1 ≤
      4 * b ^ 2 * mignotteSepSqInv cs := by
    let x := b ^ 2 * mignotteSepSqInv cs
    have h4x : 4 * b ^ 2 * mignotteSepSqInv cs = 4 * x := by ring
    change 4 * b ^ 2 * mignotteSepSqInv cs / 3 + 1 ≤ 4 * b ^ 2 * mignotteSepSqInv cs
    rw [h4x]
    have hx1 : 1 ≤ x := hx_ge1
    omega
  have hpow_b : b ^ 2 ≤ 4 ^ (2 * Nat.clog 4 b) := by
    rw [mul_comm 2 _, pow_mul]
    exact Nat.pow_le_pow_left (Nat.le_pow_clog (by decide : 1 < 4) b) 2
  have hpow_d : d ^ (d + 2) ≤ 4 ^ ((d + 2) * Nat.clog 4 d) := by
    rw [mul_comm (d + 2) _, pow_mul]
    exact Nat.pow_le_pow_left (Nat.le_pow_clog (by decide : 1 < 4) d) (d + 2)
  have hpow_sn : sn ^ (d - 1) ≤ 4 ^ ((d - 1) * Nat.clog 4 sn) := by
    rw [mul_comm (d - 1) _, pow_mul]
    exact Nat.pow_le_pow_left (Nat.le_pow_clog (by decide : 1 < 4) sn) (d - 1)
  have hpow_all : 4 * b ^ 2 * mignotteSepSqInv cs ≤
      4 ^ (1 + 2 * Nat.clog 4 b + (d + 2) * Nat.clog 4 d + (d - 1) * Nat.clog 4 sn) := by
    have hrhs : 4 ^ (1 + 2 * Nat.clog 4 b + (d + 2) * Nat.clog 4 d + (d - 1) * Nat.clog 4 sn) =
        4 * 4 ^ (2 * Nat.clog 4 b) * 4 ^ ((d + 2) * Nat.clog 4 d) *
          4 ^ ((d - 1) * Nat.clog 4 sn) := by
      simp only [pow_add, pow_one]
    rw [hs_eq, hrhs]
    calc 4 * b ^ 2 * (d ^ (d + 2) * sn ^ (d - 1))
        ≤ 4 * 4 ^ (2 * Nat.clog 4 b) *
            (4 ^ ((d + 2) * Nat.clog 4 d) * 4 ^ ((d - 1) * Nat.clog 4 sn)) := by gcongr
      _ = 4 * 4 ^ (2 * Nat.clog 4 b) * 4 ^ ((d + 2) * Nat.clog 4 d) *
            4 ^ ((d - 1) * Nat.clog 4 sn) := by ring
  change (if t.length ≤ 2 then 0 else Nat.clog 4 (4 * b ^ 2 * mignotteSepSqInv cs / 3 + 1)) ≤ _
  rw [ite_eq_right (fun h => absurd h hlen)]
  exact Nat.clog_le_of_le_pow (hdiv_le.trans hpow_all)

end Cslib.RealRoot
