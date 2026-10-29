/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.PolyTime.CNF.SparsePolyCompile
public import Complexity.Computability.PolyTime.ParityFactorEval
public import Complexity.Foundations.Data.MvPolynomial.AffineTaylor
public import Mathlib.Algebra.Polynomial.Taylor
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Foundations.BooleanAnalysis.SparseClearedSpecialization
import Complexity.Foundations.Data.Int.Order
import Complexity.Foundations.Data.List.Lookup
import Complexity.Foundations.Data.List.OfFn
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Stage-1 sparse monomial $z$-jet substitution and node-$t$ Taylor shift

Section 3.4, Sections 5.3–5.4, and Appendix B.2 of
[OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH] evaluate each degree-$\le k$
sparse $\mathbb{F}_2$ equation at a node $t \in \mathbb{Z}$ in $\mathbb{Z}[z]/(z^J)$ by:
1. Horner Taylor-shifting univariate integer polynomials around $t$ modulo $z^J$
   (`Cslib.taylorShiftZJet`, using step helper `Cslib.SparseMonomialJet.hornerShiftStep`);
2. assembling each factor variable's homogenized affine-Taylor input $z$-jet
   $d_{\mathrm{den}} \theta_{f,v}(z; x) = \langle d_{\mathrm{den}} \vec{P}_{f,v}(t), x \rangle +
   \langle d_{\mathrm{den}}(\vec{P}_{f,v}(t + z) - \vec{P}_{f,v}(t)), \mathbf{1}_U \rangle \bmod
   z^J$ (`Cslib.combineAffineInputZJet`, `Cslib.evalBaselineAt`, `Cslib.evalTaylorCorrectionZJet`,
   `Cslib.evalAffineInputZJet`, `Cslib.evalAffineInputZJetTable`), bridged to
   `Cslib.AffineTaylor.affineInput`;
3. multiplying variable $z$-jets across canonical monomials (via helper
   `Cslib.SparseMonomialJet.prodMonomialJet`) with scale $d_{\mathrm{den}}^{k - |M|}$ and summing
   across sparse equations (`Cslib.evalClearedMonomialJet`, `Cslib.evalClearedEquationJet`),
   bridged to `Cslib.BitString.clearedMonomialPoly`, `Cslib.BitString.clearedMonomialSumPoly`, and
   `Cslib.Complexity.evalMonomialList`; and
4. composing with `Cslib.evalParityFactorJet` at $\Delta = d_{\mathrm{den}}^k$
   (`Cslib.evalEquationParityFactorJet`) for the homogenized $J \times \ell$ factor table matching
   `Cslib.BitString.parityFactorCleared` ($\Gamma = \Delta^{2 \ell - 1}$ when $d_{\mathrm{den}} \ne
   0$), with `@[fun_prop]` `ComputableInPolyTime` certificates on all nine top-level routines.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH]
-/

@[expose] public section

namespace Cslib

open Polynomial Turing.MultiTapeTM
open Cslib.BitString (bitVal monomial monomialSum clearedMonomialPoly clearedMonomialSumPoly
  parityBaseDigitCleared hPolyCleared parityFactorCleared coeff_parityFactorCleared
  monomialSum_zmod_two_eq_zero_iff_even eval_zero_clearedMonomialPoly
  eval_zero_clearedMonomialSumPoly)
open Cslib.Complexity (IsCanonicalMonomial IsCanonicalEquation evalMonomialList
  bitVal_evalMonomialList_eq_sum_monomial)

private lemma getD_truncZJet_of_lt {J j : ℕ} (hj : j < J) (u : List ℤ) :
    (truncZJet J u).getD j 0 = u.getD j 0 := List.getD_map_range _ 0 hj

/-! ### 1. Univariate integer polynomial Taylor shift modulo $z^J$ (`taylorShiftZJet`) -/

/-- Single Horner Taylor-shift step mapping `acc` to `(c + (t + z) * acc) mod z^J`. -/
def SparseMonomialJet.hornerShiftStep (J : ℕ) (t : ℤ) (acc : List ℤ) (c : ℤ) : List ℤ :=
  truncZJet J (polyAdd [c] (mulZJet J [t, 1] acc))

/-- Executable univariate integer Taylor shift at node $t \in \mathbb{Z}$ truncated modulo $z^J$
([OpenAI2026ETH], §3.4 and Appendix B.2), computing the low-$J$ coefficients of
`Polynomial.taylor t (Polynomial.ofCoeffList coeffs)`. -/
def taylorShiftZJet (J : ℕ) (t : ℤ) (coeffs : List ℤ) : List ℤ :=
  coeffs.reverse.foldl (SparseMonomialJet.hornerShiftStep J t) (truncZJet J [])

private lemma polyNorm1_hornerShiftStep_le (J : ℕ) (t : ℤ) (acc : List ℤ) (c : ℤ) :
    polyNorm1 (SparseMonomialJet.hornerShiftStep J t acc c) ≤
      c.natAbs + (t.natAbs + 1) * polyNorm1 acc := by
  unfold SparseMonomialJet.hornerShiftStep; rw [polyNorm1_truncZJet]
  have hlin : polyNorm1 ([t, 1].take J) ≤ t.natAbs + 1 := (polyNorm1_take_le [t, 1] J).trans
    (by simp only [polyNorm1_cons, polyNorm1_nil, Int.natAbs_one, add_zero, le_rfl])
  have hmul : polyNorm1 (mulZJet J [t, 1] acc) ≤ (t.natAbs + 1) * polyNorm1 acc :=
    (polyNorm1_mulZJet_le J [t, 1] acc).trans (Nat.mul_le_mul hlin (polyNorm1_take_le acc J))
  exact (polyNorm1_take_le _ J).trans ((polyNorm1_polyAdd_le [c] _).trans
    (by simp only [polyNorm1_cons, polyNorm1_nil, add_zero]; exact Nat.add_le_add_left hmul _))

private lemma foldl_hornerShiftStep_bounds (J : ℕ) (t : ℤ) (w : List ℤ) :
    let out := w.foldl (SparseMonomialJet.hornerShiftStep J t) (truncZJet J [])
    out.length = J ∧ polyNorm1 out ≤ polyNorm1 w * (t.natAbs + 1) ^ w.length := by
  induction w using List.reverseRecOn with
  | nil =>
    simp only [List.foldl_nil, length_truncZJet, polyNorm1_truncZJet, List.take_nil,
      polyNorm1_nil, List.length_nil, pow_zero, mul_one, le_rfl, and_self]
  | append_singleton u c ih =>
    rcases ih with ⟨_, hnorm⟩
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, List.length_append,
      List.length_singleton, polyNorm1_append, polyNorm1_cons, polyNorm1_nil, add_zero]
    refine ⟨by simp only [SparseMonomialJet.hornerShiftStep, length_truncZJet], ?_⟩
    set acc := u.foldl (SparseMonomialJet.hornerShiftStep J t) (truncZJet J [])
    have hc_le : c.natAbs ≤ c.natAbs * (t.natAbs + 1) ^ (u.length + 1) :=
      Nat.le_mul_of_pos_right c.natAbs (Nat.one_le_pow _ _ (by omega))
    have hacc_le : (t.natAbs + 1) * polyNorm1 acc ≤ polyNorm1 u * (t.natAbs + 1) ^ (u.length + 1) :=
      (Nat.mul_le_mul_left _ hnorm).trans_eq (by rw [pow_succ']; ring)
    exact (polyNorm1_hornerShiftStep_le J t acc c).trans
      ((Nat.add_le_add hc_le hacc_le).trans_eq (by ring))

/-- `taylorShiftZJet J t coeffs` has exact length `J`. -/
@[simp] theorem length_taylorShiftZJet (J : ℕ) (t : ℤ) (coeffs : List ℤ) :
    (taylorShiftZJet J t coeffs).length = J :=
  (foldl_hornerShiftStep_bounds J t coeffs.reverse).1

/-- Entry `j < J` of `taylorShiftZJet J t coeffs` equals
`(Polynomial.taylor t (Polynomial.ofCoeffList coeffs)).coeff j`. -/
theorem getD_taylorShiftZJet_of_lt {J j : ℕ} (hj : j < J) (t : ℤ) (coeffs : List ℤ) :
    (taylorShiftZJet J t coeffs).getD j 0 =
      (Polynomial.taylor t (ofCoeffList coeffs)).coeff j := by
  induction coeffs generalizing j with
  | nil =>
    simp only [taylorShiftZJet, List.reverse_nil, List.foldl_nil, getD_truncZJet_of_lt hj,
      List.getD_nil, ofCoeffList_nil, map_zero, coeff_zero]
  | cons c rest ih =>
    have hcons : taylorShiftZJet J t (c :: rest) =
        SparseMonomialJet.hornerShiftStep J t (taylorShiftZJet J t rest) c := by
      simp only [taylorShiftZJet, List.reverse_cons, List.foldl_append, List.foldl_cons,
        List.foldl_nil]
    rw [hcons, SparseMonomialJet.hornerShiftStep, getD_truncZJet_of_lt hj, getD_polyAdd,
      ← coeff_ofCoeffList (mulZJet J [t, 1] (taylorShiftZJet J t rest)),
      coeff_ofCoeffList_mulZJet hj]
    have hc : ([c] : List ℤ).getD j 0 = (C c : ℤ[X]).coeff j := by
      simpa only [coeff_ofCoeffList, ofCoeffList_cons, ofCoeffList_nil, mul_zero, add_zero] using
        (coeff_ofCoeffList [c] j).symm
    have hlin : ofCoeffList ([t, 1] : List ℤ) = X + C t := by
      simp only [ofCoeffList_cons, ofCoeffList_nil, mul_zero, add_zero, map_one, mul_one]; ring
    have hmul : (ofCoeffList [t, 1] * ofCoeffList (taylorShiftZJet J t rest)).coeff j =
        ((X + C t) * Polynomial.taylor t (ofCoeffList rest)).coeff j := by
      rw [hlin]
      exact coeff_eq_below_mul (fun _ _ => rfl)
        (fun i hi => by rw [coeff_ofCoeffList, ih hi]) j hj
    rw [hc, hmul, ← coeff_add, ofCoeffList_cons, map_add, taylor_C, taylor_mul, taylor_X]

/-- `taylorShiftZJet` agrees with `Polynomial.coeffsBelow J` of `Polynomial.taylor t`. -/
theorem taylorShiftZJet_eq_coeffsBelow (J : ℕ) (t : ℤ) (coeffs : List ℤ) :
    taylorShiftZJet J t coeffs = (Polynomial.taylor t (ofCoeffList coeffs)).coeffsBelow J := by
  unfold coeffsBelow
  refine List.ext_getElem (by simp only [length_taylorShiftZJet, List.length_map,
      List.length_range]) fun j hj _ => ?_
  have hjlt : j < J := by simpa only [length_taylorShiftZJet] using hj
  rw [← List.getD_eq_getElem _ 0 hj, getD_taylorShiftZJet_of_lt hjlt,
    List.getElem_map, List.getElem_range]

/-- The polynomial represented by `taylorShiftZJet J t coeffs` has degree at most `J - 1`. -/
theorem natDegree_ofCoeffList_taylorShiftZJet_le (J : ℕ) (t : ℤ) (coeffs : List ℤ) :
    (ofCoeffList (taylorShiftZJet J t coeffs)).natDegree ≤ J - 1 := by
  simpa only [length_taylorShiftZJet] using natDegree_ofCoeffList_le (taylorShiftZJet J t coeffs)

/-- Congruence of `ofCoeffList (taylorShiftZJet J t coeffs)` modulo $X^J$. -/
theorem X_pow_dvd_taylor_sub_ofCoeffList_taylorShiftZJet (J : ℕ) (t : ℤ) (coeffs : List ℤ) :
    X ^ J ∣ Polynomial.taylor t (ofCoeffList coeffs) -
      ofCoeffList (taylorShiftZJet J t coeffs) := by
  rw [Polynomial.X_pow_dvd_iff]; intro j hj
  rw [coeff_sub, coeff_ofCoeffList, getD_taylorShiftZJet_of_lt hj, sub_self]

/-- Exact recovery of `Polynomial.taylor t` when `(ofCoeffList coeffs).natDegree < J`. -/
theorem ofCoeffList_taylorShiftZJet_eq_taylor {J : ℕ} (t : ℤ) {coeffs : List ℤ}
    (hdeg : (ofCoeffList coeffs).natDegree < J) :
    ofCoeffList (taylorShiftZJet J t coeffs) = Polynomial.taylor t (ofCoeffList coeffs) := by
  rw [taylorShiftZJet_eq_coeffsBelow]; exact ofCoeffList_coeffsBelow (by rwa [natDegree_taylor])

/-- Horner $\ell_1$-norm bound for `taylorShiftZJet`. -/
theorem polyNorm1_taylorShiftZJet_le (J : ℕ) (t : ℤ) (coeffs : List ℤ) :
    polyNorm1 (taylorShiftZJet J t coeffs) ≤
      polyNorm1 coeffs * (t.natAbs + 1) ^ coeffs.length := by
  simpa only [taylorShiftZJet, polyNorm1_reverse, List.length_reverse] using
    (foldl_hornerShiftStep_bounds J t coeffs.reverse).2

/-- Entry bit-length bound for `taylorShiftZJet` under `encIntBin`. -/
theorem length_encIntBin_mem_taylorShiftZJet_le {J : ℕ} {t : ℤ} {coeffs : List ℤ} {z : ℤ}
    (hz : z ∈ taylorShiftZJet J t coeffs) :
    (encIntBin z).length ≤ (polyNorm1 coeffs).size + coeffs.length * (t.natAbs + 1).size + 2 := by
  have h1 : polyNorm1 coeffs ≤ 2 ^ (polyNorm1 coeffs).size := (Nat.lt_size_self _).le
  have h2 : (t.natAbs + 1) ^ coeffs.length ≤ 2 ^ (coeffs.length * (t.natAbs + 1).size) :=
    (Nat.pow_le_pow_left (Nat.lt_size_self _).le _).trans_eq (by rw [← pow_mul, mul_comm])
  exact length_encIntBin_le_of_natAbs_le
    (((natAbs_mem_le_polyNorm1 hz).trans (polyNorm1_taylorShiftZJet_le J t coeffs)).trans
      ((Nat.mul_le_mul h1 h2).trans_eq (pow_add _ _ _).symm))

/-! ### 2. Affine-Taylor variable $z$-jet evaluation (`evalAffineInputZJet`) -/

/-- Assembles a length-`J` 1D $z$-jet from `base` ($j = 0$) and `corrJet` ($1 \le j < J$). -/
def combineAffineInputZJet (J : ℕ) (base : ℤ) (corrJet : List ℤ) : List ℤ :=
  if J = 0 then [] else base :: (truncZJet J corrJet).drop 1

/-- Evaluates the scalar baseline $\langle d_{\mathrm{den}} \vec{P}_{f,v}(t), x \rangle$ at `t`
([OpenAI2026ETH], §3.4 eq. (3.7) and Appendix B.2; missing `x` bits default to `false`). -/
def evalBaselineAt (t : ℤ) (rowCoeffs : List (List ℤ)) (x : List Bool) : ℤ :=
  ((List.range rowCoeffs.length).map fun u =>
    if x.getD u false then (taylorShiftZJet 1 t (rowCoeffs.getD u [])).getD 0 0 else 0).sum

/-- Evaluates the length-`J` zero-constant Taylor-correction $z$-jet
$\langle d_{\mathrm{den}}(\vec{P}_{f,v}(t + z) - \vec{P}_{f,v}(t)), \mathbf{1}_U \rangle \bmod z^J$
([OpenAI2026ETH], §3.4 eq. (3.7) and Appendix B.2; missing `U` bits default to `false`). -/
def evalTaylorCorrectionZJet (J : ℕ) (t : ℤ) (rowCoeffs : List (List ℤ)) (U : List Bool) :
    List ℤ :=
  let uJets := (List.range rowCoeffs.length).map fun u =>
    if U.getD u false then combineAffineInputZJet J 0 (taylorShiftZJet J t (rowCoeffs.getD u []))
    else truncZJet J []
  (List.range J).map fun j => (uJets.map fun q => q.getD j 0).sum

/-- Evaluates the length-`J` homogenized affine-Taylor input $z$-jet $d_{\mathrm{den}} \theta_{f,v}$
([OpenAI2026ETH], §3.4 eq. (3.7) and Appendix B.2). -/
def evalAffineInputZJet (J : ℕ) (t : ℤ) (rowCoeffs : List (List ℤ)) (U x : List Bool) : List ℤ :=
  combineAffineInputZJet J (evalBaselineAt t rowCoeffs x) (evalTaylorCorrectionZJet J t rowCoeffs U)

/-- Materialized `rowsCoeffs.length × J` table of homogenized affine-Taylor variable $z$-jets. -/
def evalAffineInputZJetTable (J : ℕ) (t : ℤ) (rowsCoeffs : List (List (List ℤ)))
    (U x : List Bool) : List (List ℤ) :=
  rowsCoeffs.map fun rowCoeffs => evalAffineInputZJet J t rowCoeffs U x

/-- `combineAffineInputZJet J base corrJet` has exact length `J`. -/
@[simp] theorem length_combineAffineInputZJet (J : ℕ) (base : ℤ) (corrJet : List ℤ) :
    (combineAffineInputZJet J base corrJet).length = J := by
  unfold combineAffineInputZJet; split_ifs with hJ
  · simp only [List.length_nil, hJ]
  · simp only [List.length_cons, List.length_drop, length_truncZJet]; omega

/-- Entry `j < J` of `combineAffineInputZJet` is `base` at `0` and `corrJet.getD j 0` for `j > 0`.
-/
theorem getD_combineAffineInputZJet_of_lt {J j : ℕ} (hj : j < J) (base : ℤ) (corrJet : List ℤ) :
    (combineAffineInputZJet J base corrJet).getD j 0 =
      if j = 0 then base else corrJet.getD j 0 := by
  have hJ : J ≠ 0 := by omega
  cases j with
  | zero => simp only [combineAffineInputZJet, hJ, ↓reduceIte, List.getD_cons_zero]
  | succ k =>
    simp only [combineAffineInputZJet, hJ, ↓reduceIte, List.getD_cons_succ,
      Nat.add_eq_zero_iff, one_ne_zero, and_false]
    rw [List.getD_eq_getElem?_getD (l := (truncZJet J corrJet).drop 1), List.getElem?_drop,
      Nat.add_comm 1 k, ← List.getD_eq_getElem?_getD, getD_truncZJet_of_lt hj]

/-- `evalBaselineAt t rowCoeffs x` equals the polynomial baseline sum at `t`. -/
theorem evalBaselineAt_eq_sum (t : ℤ) (rowCoeffs : List (List ℤ)) (x : List Bool) :
    evalBaselineAt t rowCoeffs x =
      ∑ i : Fin rowCoeffs.length,
        (ofCoeffList (rowCoeffs.getD i [])).eval t * bitVal ℤ (x.getD i false) := by
  unfold evalBaselineAt; rw [List.sum_map_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [getD_taylorShiftZJet_of_lt Nat.zero_lt_one, Polynomial.taylor_coeff_zero]
  cases x.getD i false
  · simp only [Bool.false_eq_true, ↓reduceIte, Cslib.BitString.bitVal_false, mul_zero]
  · simp only [↓reduceIte, Cslib.BitString.bitVal_true, mul_one]

/-- At `t = 0`, `evalBaselineAt 0 rowCoeffs x` sums the constant entries selected by `x`. -/
theorem evalBaselineAt_zero (rowCoeffs : List (List ℤ)) (x : List Bool) :
    evalBaselineAt 0 rowCoeffs x =
      ∑ i : Fin rowCoeffs.length, rowEntry rowCoeffs i 0 * bitVal ℤ (x.getD i false) := by
  rw [evalBaselineAt_eq_sum]
  exact Finset.sum_congr rfl fun i _ => by
    rw [← Polynomial.coeff_zero_eq_eval_zero, coeff_ofCoeffList, rowEntry]

/-- `evalTaylorCorrectionZJet` has exact length `J`. -/
@[simp] theorem length_evalTaylorCorrectionZJet (J : ℕ) (t : ℤ) (rowCoeffs : List (List ℤ))
    (U : List Bool) : (evalTaylorCorrectionZJet J t rowCoeffs U).length = J := by
  simp only [evalTaylorCorrectionZJet, List.length_map, List.length_range]

/-- Entrywise specification of `evalTaylorCorrectionZJet` for `j < J`. -/
theorem getD_evalTaylorCorrectionZJet_of_lt {J j : ℕ} (hj : j < J) (t : ℤ)
    (rowCoeffs : List (List ℤ)) (U : List Bool) :
    (evalTaylorCorrectionZJet J t rowCoeffs U).getD j 0 =
      if j = 0 then 0
      else ∑ i : Fin rowCoeffs.length,
        bitVal ℤ (U.getD i false) *
          (Polynomial.taylor t (ofCoeffList (rowCoeffs.getD i []))).coeff j := by
  unfold evalTaylorCorrectionZJet; dsimp only
  rw [List.getD_map_range _ 0 hj, List.map_map, List.sum_map_range]
  by_cases hj0 : j = 0
  · subst hj0; simp only [↓reduceIte]
    refine Finset.sum_eq_zero fun i _ => ?_
    simp only [Function.comp_apply]
    cases U.getD i false
    · simp only [Bool.false_eq_true, ↓reduceIte, getD_truncZJet_of_lt hj, List.getD_nil]
    · simp only [↓reduceIte, getD_combineAffineInputZJet_of_lt hj]
  · simp only [hj0, ↓reduceIte]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Function.comp_apply]
    cases U.getD i false
    · simp only [Bool.false_eq_true, ↓reduceIte, getD_truncZJet_of_lt hj, List.getD_nil,
        Cslib.BitString.bitVal_false, zero_mul]
    · simp only [↓reduceIte, getD_combineAffineInputZJet_of_lt hj, hj0,
        getD_taylorShiftZJet_of_lt hj, Cslib.BitString.bitVal_true, one_mul]

/-- `evalAffineInputZJet` returns a $z$-jet of exact length `J`. -/
@[simp] theorem length_evalAffineInputZJet (J : ℕ) (t : ℤ) (rowCoeffs : List (List ℤ))
    (U x : List Bool) :
    (evalAffineInputZJet J t rowCoeffs U x).length = J :=
  length_combineAffineInputZJet J _ _

/-- `evalAffineInputZJetTable` has length `rowsCoeffs.length`. -/
@[simp] theorem length_evalAffineInputZJetTable (J : ℕ) (t : ℤ)
    (rowsCoeffs : List (List (List ℤ))) (U x : List Bool) :
    (evalAffineInputZJetTable J t rowsCoeffs U x).length = rowsCoeffs.length := by
  simp only [evalAffineInputZJetTable, List.length_map]

/-- `evalAffineInputZJetTable` has rectangular shape `rowsCoeffs.length × J`. -/
theorem isTableShape_evalAffineInputZJetTable (J : ℕ) (t : ℤ)
    (rowsCoeffs : List (List (List ℤ))) (U x : List Bool) :
    IsTableShape rowsCoeffs.length J (evalAffineInputZJetTable J t rowsCoeffs U x) := by
  refine ⟨length_evalAffineInputZJetTable J t rowsCoeffs U x, fun q hq => ?_⟩
  obtain ⟨r, _, rfl⟩ := List.mem_map.mp hq; exact length_evalAffineInputZJet J t r U x

private lemma evalAffineInputZJet_nil (J : ℕ) (t : ℤ) (U x : List Bool) :
    evalAffineInputZJet J t [] U x = truncZJet J [] := by
  refine List.ext_getElem (by simp only [length_evalAffineInputZJet, length_truncZJet])
    fun j hj hj2 => ?_
  have hjlt : j < J := by simpa only [length_evalAffineInputZJet] using hj
  rw [← List.getD_eq_getElem _ 0 hj, ← List.getD_eq_getElem _ 0 hj2,
    getD_truncZJet_of_lt hjlt, List.getD_nil, evalAffineInputZJet,
    getD_combineAffineInputZJet_of_lt hjlt]
  by_cases hj0 : j = 0
  · subst hj0; simp only [↓reduceIte, evalBaselineAt, List.length_nil, List.range_zero,
      List.map_nil, List.sum_nil]
  · simp only [hj0, ↓reduceIte, getD_evalTaylorCorrectionZJet_of_lt hjlt, List.length_nil,
      Finset.univ_eq_empty, Finset.sum_empty]

/-- Truncating row `v` of `evalAffineInputZJetTable` to length `J` agrees with
`evalAffineInputZJet J t (rowsCoeffs.getD v []) U x` at every `v : ℕ`. -/
theorem truncZJet_getD_evalAffineInputZJetTable (J : ℕ) (t : ℤ)
    (rowsCoeffs : List (List (List ℤ))) (U x : List Bool) (v : ℕ) :
    truncZJet J ((evalAffineInputZJetTable J t rowsCoeffs U x).getD v []) =
      evalAffineInputZJet J t (rowsCoeffs.getD v []) U x := by
  by_cases hv : v < rowsCoeffs.length
  · have hv' : v < (evalAffineInputZJetTable J t rowsCoeffs U x).length := by
      simpa only [length_evalAffineInputZJetTable] using hv
    rw [List.getD_eq_getElem _ [] hv', List.getD_eq_getElem _ [] hv]
    simp only [evalAffineInputZJetTable, List.getElem_map]
    refine List.ext_getElem (by simp only [length_truncZJet, length_evalAffineInputZJet])
      fun j hj hj2 => ?_
    have hjlt : j < J := by simpa only [length_truncZJet] using hj
    rw [← List.getD_eq_getElem _ 0 hj, getD_truncZJet_of_lt hjlt, List.getD_eq_getElem _ 0 hj2]
  · rw [List.getD_eq_default _ _ (by rw [length_evalAffineInputZJetTable]; omega),
      List.getD_eq_default rowsCoeffs [] (by omega), evalAffineInputZJet_nil]

/-- Entry `(v, j)` (`j < J`) of `evalAffineInputZJetTable` agrees with `evalAffineInputZJet`. -/
theorem rowEntry_evalAffineInputZJetTable_of_lt {J j : ℕ} (hj : j < J) (t : ℤ)
    (rowsCoeffs : List (List (List ℤ))) (U x : List Bool) (v : ℕ) :
    rowEntry (evalAffineInputZJetTable J t rowsCoeffs U x) v j =
      (evalAffineInputZJet J t (rowsCoeffs.getD v []) U x).getD j 0 := by
  rw [rowEntry, ← getD_truncZJet_of_lt hj, truncZJet_getD_evalAffineInputZJetTable]

/-- `evalAffineInputZJetTable` agrees with `Cslib.tabulateTable` on `rowsCoeffs.length × J`. -/
theorem evalAffineInputZJetTable_eq_tabulateTable (J : ℕ) (t : ℤ)
    (rowsCoeffs : List (List (List ℤ))) (U x : List Bool) :
    evalAffineInputZJetTable J t rowsCoeffs U x =
      tabulateTable rowsCoeffs.length J
        (fun v j => (evalAffineInputZJet J t (rowsCoeffs.getD v []) U x).getD j 0) :=
  eq_of_isTableShape_of_rowEntry_eq (isTableShape_evalAffineInputZJetTable J t rowsCoeffs U x)
    (isTableShape_tabulateTable _ J _) fun v hv j hj => by
      rw [rowEntry_evalAffineInputZJetTable_of_lt hj, rowEntry_tabulateTable_of_lt _ hv hj]

/-- **Refinement of `evalAffineInputZJet` to `Cslib.AffineTaylor.affineInput` over `Fin n`**
([OpenAI2026ETH], §3.4 eq. (3.7) and Appendix B.2) for `rowCoeffs.length ≤ n` and `j < J`. -/
theorem getD_evalAffineInputZJet_eq_coeff_affineInput_fin {J n j : ℕ} (hj : j < J) (t : ℤ)
    {rowCoeffs : List (List ℤ)} (hlen : rowCoeffs.length ≤ n) (U x : List Bool) :
    (evalAffineInputZJet J t rowCoeffs U x).getD j 0 =
      ((Cslib.AffineTaylor.affineInput
          (fun i : Fin n => ofCoeffList (rowCoeffs.getD i []))
          t (fun i : Fin n => x.getD i false)).map
        (MvPolynomial.eval fun i : Fin n => bitVal ℤ (U.getD i false))).coeff j := by
  let P (u : ℕ) : ℤ[X] := ofCoeffList (rowCoeffs.getD u [])
  let term (u : ℕ) : ℤ[X] :=
    C (bitVal ℤ (U.getD u false)) * (Polynomial.taylor t (P u) - C ((P u).eval t))
  rw [Cslib.AffineTaylor.map_eval_affineInput, Polynomial.coeff_add,
    Polynomial.finsetSum_coeff, evalAffineInputZJet, getD_combineAffineInputZJet_of_lt hj]
  by_cases hj0 : j = 0
  · subst hj0; simp only [↓reduceIte, Polynomial.coeff_C_zero]
    have hcorr : ∑ i : Fin n, (term i).coeff 0 = 0 := Finset.sum_eq_zero fun i _ => by
      simp only [term, Polynomial.coeff_C_mul, Cslib.AffineTaylor.coeff_zero_taylor_sub_C_eval,
        mul_zero]
    let b (u : ℕ) : ℤ := (P u).eval t * bitVal ℤ (x.getD u false)
    rw [hcorr, add_zero, evalBaselineAt_eq_sum, Fin.sum_univ_eq_sum_range b _,
      Fin.sum_univ_eq_sum_range b n]
    refine Finset.sum_subset (Finset.range_mono hlen) fun u _ hu => ?_
    have hge : rowCoeffs.length ≤ u := by simpa only [Finset.mem_range, not_lt] using hu
    simp only [b, P, List.getD_eq_default rowCoeffs [] hge, ofCoeffList_nil, eval_zero, zero_mul]
  · simp only [hj0, ↓reduceIte, Polynomial.coeff_C_of_ne_zero hj0, zero_add,
      getD_evalTaylorCorrectionZJet_of_lt hj]
    let c (u : ℕ) : ℤ := bitVal ℤ (U.getD u false) * (Polynomial.taylor t (P u)).coeff j
    rw [Fin.sum_univ_eq_sum_range c rowCoeffs.length,
      Fin.sum_univ_eq_sum_range (fun u => (term u).coeff j) n,
      Finset.sum_congr rfl fun u (_ : u ∈ Finset.range rowCoeffs.length) =>
        show c u = (term u).coeff j by
          simp only [c, term, Polynomial.coeff_C_mul, coeff_sub,
            Polynomial.coeff_C_of_ne_zero hj0, sub_zero]]
    refine Finset.sum_subset (Finset.range_mono hlen) fun u _ hu => ?_
    have hge : rowCoeffs.length ≤ u := by simpa only [Finset.mem_range, not_lt] using hu
    simp only [term, P, List.getD_eq_default rowCoeffs [] hge, ofCoeffList_nil, eval_zero,
      map_zero, sub_self, mul_zero, coeff_zero]

/-- **Entrywise specification of `evalAffineInputZJet` against `Cslib.AffineTaylor.affineInput`**
over `Fin rowCoeffs.length` for `j < J`. -/
theorem getD_evalAffineInputZJet_eq_coeff_affineInput {J j : ℕ} (hj : j < J) (t : ℤ)
    (rowCoeffs : List (List ℤ)) (U x : List Bool) :
    (evalAffineInputZJet J t rowCoeffs U x).getD j 0 =
      ((Cslib.AffineTaylor.affineInput
          (fun i : Fin rowCoeffs.length => ofCoeffList (rowCoeffs.getD i []))
          t (fun i : Fin rowCoeffs.length => x.getD i false)).map
        (MvPolynomial.eval fun i : Fin rowCoeffs.length => bitVal ℤ (U.getD i false))).coeff j :=
  getD_evalAffineInputZJet_eq_coeff_affineInput_fin hj t le_rfl U x

/-- **Table entry specification of `evalAffineInputZJetTable` against
`Cslib.AffineTaylor.affineInput`** over `Fin n` (`∀ r ∈ rowsCoeffs, r.length ≤ n`) for `j < J`. -/
theorem rowEntry_evalAffineInputZJetTable_eq_coeff_affineInput {J n j : ℕ} (hj : j < J) (t : ℤ)
    {rowsCoeffs : List (List (List ℤ))} (hrows : ∀ r ∈ rowsCoeffs, r.length ≤ n)
    (U x : List Bool) (v : ℕ) :
    rowEntry (evalAffineInputZJetTable J t rowsCoeffs U x) v j =
      ((Cslib.AffineTaylor.affineInput
          (fun i : Fin n => ofCoeffList ((rowsCoeffs.getD v []).getD i []))
          t (fun i : Fin n => x.getD i false)).map
        (MvPolynomial.eval fun i : Fin n => bitVal ℤ (U.getD i false))).coeff j := by
  have hlen : (rowsCoeffs.getD v []).length ≤ n := by
    by_cases hv : v < rowsCoeffs.length
    · rw [List.getD_eq_getElem _ [] hv]; exact hrows _ (List.getElem_mem hv)
    · rw [List.getD_eq_default rowsCoeffs [] (by omega)]; exact Nat.zero_le n
  rw [rowEntry_evalAffineInputZJetTable_of_lt hj]
  exact getD_evalAffineInputZJet_eq_coeff_affineInput_fin hj t hlen U x

/-- At `j = 0` (`1 ≤ J`), `evalAffineInputZJet` evaluates to `evalBaselineAt t rowCoeffs x`. -/
theorem getD_zero_evalAffineInputZJet {J : ℕ} (hJ : 1 ≤ J) (t : ℤ)
    (rowCoeffs : List (List ℤ)) (U x : List Bool) :
    (evalAffineInputZJet J t rowCoeffs U x).getD 0 0 = evalBaselineAt t rowCoeffs x := by
  simpa only [evalAffineInputZJet, ↓reduceIte] using
    getD_combineAffineInputZJet_of_lt (by omega : 0 < J) (evalBaselineAt t rowCoeffs x)
      (evalTaylorCorrectionZJet J t rowCoeffs U)

/-- At `t = 0` and `j = 0` (`1 ≤ J`), `evalAffineInputZJet J 0 rowCoeffs U x` sums the constant
entries selected by `x`. -/
theorem getD_zero_evalAffineInputZJet_zero {J : ℕ} (hJ : 1 ≤ J)
    (rowCoeffs : List (List ℤ)) (U x : List Bool) :
    (evalAffineInputZJet J 0 rowCoeffs U x).getD 0 0 =
      ∑ i : Fin rowCoeffs.length, rowEntry rowCoeffs i 0 * bitVal ℤ (x.getD i false) :=
  (getD_zero_evalAffineInputZJet hJ 0 rowCoeffs U x).trans (evalBaselineAt_zero rowCoeffs x)

/-- At `t = 0, j = 0` (`1 ≤ J`), a unit row restoring coordinate `w` at scale `dDen` evaluates to
`dDen * bitVal ℤ (x.getD w false)` regardless of `U`. -/
theorem getD_zero_evalAffineInputZJet_of_unit_row {J w : ℕ} (hJ : 1 ≤ J) (dDen : ℤ)
    {rowCoeffs : List (List ℤ)} (hw : w < rowCoeffs.length)
    (hunit : ∀ u < rowCoeffs.length, rowEntry rowCoeffs u 0 = if u = w then dDen else 0)
    (U x : List Bool) :
    (evalAffineInputZJet J 0 rowCoeffs U x).getD 0 0 = dDen * bitVal ℤ (x.getD w false) := by
  let f (u : ℕ) : ℤ := rowEntry rowCoeffs u 0 * bitVal ℤ (x.getD u false)
  rw [getD_zero_evalAffineInputZJet_zero hJ, Fin.sum_univ_eq_sum_range f rowCoeffs.length,
    Finset.sum_congr rfl fun u hu =>
      show f u = if u = w then dDen * bitVal ℤ (x.getD w false) else 0 by
        dsimp only [f]; rw [hunit u (Finset.mem_range.mp hu)]; split_ifs with huw
        · subst huw; rfl
        · exact zero_mul _,
    Finset.sum_ite_eq', ite_eq_left (Finset.mem_range.mpr hw)]

private lemma polyNorm1_eq_sum_range_getD (l : List ℤ) :
    polyNorm1 l = ∑ j ∈ Finset.range l.length, (l.getD j 0).natAbs := by
  have hl : l = (List.range l.length).map fun j => l.getD j 0 :=
    List.ext_getElem (by simp only [List.length_map, List.length_range]) fun j hj _ => by
      rw [List.getElem_map, List.getElem_range, List.getD_eq_getElem _ 0 hj]
  conv_lhs => rw [polyNorm1, hl]
  rw [List.map_map, List.sum_map_range,
    Fin.sum_univ_eq_sum_range (Int.natAbs ∘ fun j => l.getD j 0) l.length]; rfl

private lemma natAbs_getD_evalAffineInputZJet_le {J j : ℕ} (hj : j < J) (t : ℤ)
    (rowCoeffs : List (List ℤ)) (U x : List Bool) :
    ((evalAffineInputZJet J t rowCoeffs U x).getD j 0).natAbs ≤
      ∑ i : Fin rowCoeffs.length,
        ((taylorShiftZJet J t (rowCoeffs.getD i [])).getD j 0).natAbs := by
  rw [evalAffineInputZJet, getD_combineAffineInputZJet_of_lt hj]
  by_cases hj0 : j = 0
  · subst hj0; simp only [↓reduceIte, evalBaselineAt_eq_sum]
    refine (Finset.le_sum_of_subadditive Int.natAbs Int.natAbs_zero.le Int.natAbs_add_le _ _).trans
      (Finset.sum_le_sum fun i _ => ?_)
    rw [← Polynomial.taylor_coeff_zero, ← getD_taylorShiftZJet_of_lt hj]
    cases x.getD i false
    · simp only [Cslib.BitString.bitVal_false, mul_zero, Int.natAbs_zero, Nat.zero_le]
    · simp only [Cslib.BitString.bitVal_true, mul_one, le_rfl]
  · simp only [hj0, ↓reduceIte, getD_evalTaylorCorrectionZJet_of_lt hj]
    refine (Finset.le_sum_of_subadditive Int.natAbs Int.natAbs_zero.le Int.natAbs_add_le _ _).trans
      (Finset.sum_le_sum fun i _ => ?_)
    rw [← getD_taylorShiftZJet_of_lt hj]
    cases U.getD i false
    · simp only [Cslib.BitString.bitVal_false, zero_mul, Int.natAbs_zero, Nat.zero_le]
    · simp only [Cslib.BitString.bitVal_true, one_mul, le_rfl]

/-- Coordinatewise shifted-norm bound for `evalAffineInputZJet`. -/
theorem polyNorm1_evalAffineInputZJet_le_sum_taylorShiftZJet (J : ℕ) (t : ℤ)
    (rowCoeffs : List (List ℤ)) (U x : List Bool) :
    polyNorm1 (evalAffineInputZJet J t rowCoeffs U x) ≤
      (rowCoeffs.map fun c => polyNorm1 (taylorShiftZJet J t c)).sum := by
  rw [polyNorm1_eq_sum_range_getD, length_evalAffineInputZJet]
  refine (Finset.sum_le_sum fun j hj =>
    natAbs_getD_evalAffineInputZJet_le (Finset.mem_range.mp hj) t rowCoeffs U x).trans_eq ?_
  rw [Finset.sum_comm]
  have hmap : rowCoeffs = (List.range rowCoeffs.length).map fun u => rowCoeffs.getD u [] :=
    List.ext_getElem (by simp only [List.length_map, List.length_range]) fun u hu _ => by
      rw [List.getElem_map, List.getElem_range, List.getD_eq_getElem _ [] hu]
  conv_rhs => rw [hmap]
  rw [List.map_map, List.sum_map_range]
  exact Finset.sum_congr rfl fun i _ => by
    simp only [Function.comp_apply, polyNorm1_eq_sum_range_getD (taylorShiftZJet J t _),
      length_taylorShiftZJet]

/-- **Appendix B.2 $B_0$-style $\ell_1$-norm bound for `evalAffineInputZJet`** ([OpenAI2026ETH],
Appendix B.2, p. 48) via `polyNorm1_taylorShiftZJet_le`. -/
theorem polyNorm1_evalAffineInputZJet_le (J : ℕ) (t : ℤ) (rowCoeffs : List (List ℤ))
    (U x : List Bool) :
    polyNorm1 (evalAffineInputZJet J t rowCoeffs U x) ≤
      (rowCoeffs.map fun c => polyNorm1 c * (t.natAbs + 1) ^ c.length).sum :=
  (polyNorm1_evalAffineInputZJet_le_sum_taylorShiftZJet J t rowCoeffs U x).trans
    (List.sum_le_sum fun c _ => polyNorm1_taylorShiftZJet_le J t c)

/-- **Appendix B.2 $\ell_1$-norm bound for `evalTaylorCorrectionZJet`**. -/
theorem polyNorm1_evalTaylorCorrectionZJet_le (J : ℕ) (t : ℤ) (rowCoeffs : List (List ℤ))
    (U : List Bool) :
    polyNorm1 (evalTaylorCorrectionZJet J t rowCoeffs U) ≤
      (rowCoeffs.map fun c => polyNorm1 c * (t.natAbs + 1) ^ c.length).sum := by
  have heq : evalTaylorCorrectionZJet J t rowCoeffs U = evalAffineInputZJet J t rowCoeffs U [] :=
    List.ext_getElem (by simp only [length_evalTaylorCorrectionZJet, length_evalAffineInputZJet])
      fun j hj hj2 => by
        have hjlt : j < J := by simpa only [length_evalTaylorCorrectionZJet] using hj
        rw [← List.getD_eq_getElem _ 0 hj, ← List.getD_eq_getElem _ 0 hj2, evalAffineInputZJet,
          getD_combineAffineInputZJet_of_lt hjlt]
        by_cases hj0 : j = 0
        · subst hj0; simp only [↓reduceIte, getD_evalTaylorCorrectionZJet_of_lt hjlt,
            evalBaselineAt_eq_sum, List.getD_nil, Cslib.BitString.bitVal_false, mul_zero,
            Finset.sum_const_zero]
        · simp only [hj0, ↓reduceIte]
  simpa only [heq] using polyNorm1_evalAffineInputZJet_le J t rowCoeffs U []

/-- Every row `q ∈ evalAffineInputZJetTable J t rowsCoeffs U x` satisfies
`polyNorm1 (truncZJet J q) ≤ B₀` and `polyNorm1 q ≤ B₀` under rowwise Horner bound `B₀`. -/
theorem polyNorm1_truncZJet_mem_evalAffineInputZJetTable_le {J B₀ : ℕ} {t : ℤ}
    {rowsCoeffs : List (List (List ℤ))}
    (hrows : ∀ rowCoeffs ∈ rowsCoeffs,
      (rowCoeffs.map fun c => polyNorm1 c * (t.natAbs + 1) ^ c.length).sum ≤ B₀)
    (U x : List Bool) {q : List ℤ} (hq : q ∈ evalAffineInputZJetTable J t rowsCoeffs U x) :
    polyNorm1 (truncZJet J q) ≤ B₀ ∧ polyNorm1 q ≤ B₀ := by
  obtain ⟨rowCoeffs, hr, rfl⟩ := List.mem_map.mp hq
  have h1 := (polyNorm1_evalAffineInputZJet_le J t rowCoeffs U x).trans (hrows rowCoeffs hr)
  exact ⟨(polyNorm1_truncZJet J _).trans_le ((polyNorm1_take_le _ J).trans h1), h1⟩

private lemma polyNorm1_truncZJet_getD_le {J B₀ : ℕ} {varJets : List (List ℤ)}
    (hjets : ∀ q ∈ varJets, polyNorm1 (truncZJet J q) ≤ B₀) (v : ℕ) :
    polyNorm1 (truncZJet J (varJets.getD v [])) ≤ B₀ := by
  by_cases hv : v < varJets.length
  · rw [List.getD_eq_getElem _ [] hv]; exact hjets _ (List.getElem_mem hv)
  · rw [List.getD_eq_default _ _ (by omega), polyNorm1_truncZJet, List.take_nil, polyNorm1_nil]
    exact Nat.zero_le B₀

/-! ### 3. Stage-1 homogenized monomial & equation $z$-jet evaluation -/

/-- Product of truncated variable $z$-jets across `mon` modulo $z^J$. -/
def SparseMonomialJet.prodMonomialJet (J : ℕ) (varJets : List (List ℤ)) (mon : List ℕ) : List ℤ :=
  mon.foldl (fun acc v => mulZJet J acc (truncZJet J (varJets.getD v []))) (truncZJet J [1])

/-- Stage-1 degree-$k$ homogenized monomial $z$-jet evaluation ([OpenAI2026ETH], §5.3–5.4 and
Appendix B.2), computing $d_{\mathrm{den}}^{k - |\text{mon}|} \prod_{v \in \text{mon}} \theta_v(z)
\bmod z^J$ (missing `varJets` rows default to `[]`; `k < mon.length` uses `k - mon.length = 0`). -/
def evalClearedMonomialJet (J k : ℕ) (dDen : ℤ) (varJets : List (List ℤ)) (mon : List ℕ) :
    List ℤ :=
  mulZJet J [dDen ^ (k - mon.length)] (SparseMonomialJet.prodMonomialJet J varJets mon)

/-- Stage-1 degree-$k$ homogenized sparse equation $z$-jet evaluation ([OpenAI2026ETH], §5.3–5.4
and Appendix B.2), summing `evalClearedMonomialJet` across `mon ∈ eq` modulo $z^J$. -/
def evalClearedEquationJet (J k : ℕ) (dDen : ℤ) (varJets : List (List ℤ))
    (eq : List (List ℕ)) : List ℤ :=
  eq.foldl
    (fun acc mon => truncZJet J (polyAdd acc (evalClearedMonomialJet J k dDen varJets mon)))
    (truncZJet J [])

private lemma length_prodMonomialJet (J : ℕ) (varJets : List (List ℤ)) (mon : List ℕ) :
    (SparseMonomialJet.prodMonomialJet J varJets mon).length = J := by
  unfold SparseMonomialJet.prodMonomialJet
  induction mon using List.reverseRecOn with
  | nil => exact length_truncZJet J [1]
  | append_singleton u v _ =>
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, length_mulZJet]

/-- `evalClearedMonomialJet` has exact length `J`. -/
@[simp] theorem length_evalClearedMonomialJet (J k : ℕ) (dDen : ℤ) (varJets : List (List ℤ))
    (mon : List ℕ) :
    (evalClearedMonomialJet J k dDen varJets mon).length = J :=
  length_mulZJet J _ _

/-- `evalClearedEquationJet` has exact length `J`. -/
@[simp] theorem length_evalClearedEquationJet (J k : ℕ) (dDen : ℤ) (varJets : List (List ℤ))
    (eq : List (List ℕ)) :
    (evalClearedEquationJet J k dDen varJets eq).length = J := by
  unfold evalClearedEquationJet
  induction eq using List.reverseRecOn with
  | nil => exact length_truncZJet J []
  | append_singleton u mon _ =>
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, length_truncZJet]

private lemma getD_prodMonomialJet_of_lt {J j : ℕ} (hj : j < J) {varJets : List (List ℤ)}
    {θ : ℕ → ℤ[X]} {mon : List ℕ}
    (hθ : ∀ v ∈ mon, ∀ i < J, rowEntry varJets v i = (θ v).coeff i) :
    (SparseMonomialJet.prodMonomialJet J varJets mon).getD j 0 = ((mon.map θ).prod).coeff j := by
  unfold SparseMonomialJet.prodMonomialJet
  induction mon using List.reverseRecOn generalizing j with
  | nil =>
    simp only [List.foldl_nil, List.map_nil, List.prod_nil, getD_truncZJet_of_lt hj]
    have h1 : ofCoeffList ([1] : List ℤ) = 1 := by
      simp only [ofCoeffList_cons, ofCoeffList_nil, mul_zero, add_zero, map_one]
    simpa only [coeff_ofCoeffList] using congrArg (fun P => P.coeff j) h1
  | append_singleton u v ih =>
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, List.map_append,
      List.map_singleton, List.prod_append, List.prod_singleton]
    rw [← coeff_ofCoeffList, coeff_ofCoeffList_mulZJet hj]
    refine coeff_eq_below_mul (fun i hi => ?_) (fun i hi => ?_) j hj
    · rw [coeff_ofCoeffList]; exact ih hi fun w hw => hθ w (List.mem_append_left _ hw)
    · rw [coeff_ofCoeffList, getD_truncZJet_of_lt hi]
      exact hθ v (List.mem_append_right _ (List.mem_singleton_self v)) i hi

/-- **Coefficient specification of `evalClearedMonomialJet`** against
`Cslib.BitString.clearedMonomialPoly` for `j < J`. -/
theorem getD_evalClearedMonomialJet_of_lt {J k j : ℕ} (hj : j < J) (dDen : ℤ)
    {varJets : List (List ℤ)} {θ : ℕ → ℤ[X]} {mon : List ℕ}
    (hmon : IsCanonicalMonomial mon) (_hdeg : mon.length ≤ k)
    (hθ : ∀ v ∈ mon, ∀ i < J, rowEntry varJets v i = (θ v).coeff i) :
    (evalClearedMonomialJet J k dDen varJets mon).getD j 0 =
      (clearedMonomialPoly dDen k θ mon.toFinset).coeff j := by
  unfold evalClearedMonomialJet clearedMonomialPoly
  rw [← coeff_ofCoeffList, coeff_ofCoeffList_mulZJet hj, List.toFinset_card_of_nodup hmon.nodup,
    List.prod_toFinset θ hmon.nodup]
  have hc : ofCoeffList [dDen ^ (k - mon.length)] = C (dDen ^ (k - mon.length)) := by
    simp only [ofCoeffList_cons, ofCoeffList_nil, mul_zero, add_zero]
  rw [hc]
  exact coeff_eq_below_mul (fun _ _ => rfl)
    (fun i hi => by rw [coeff_ofCoeffList, getD_prodMonomialJet_of_lt hi hθ]) j hj

private lemma getD_evalClearedEquationJet_eq_list_sum {J k j : ℕ} (hj : j < J) (dDen : ℤ)
    (varJets : List (List ℤ)) (eq : List (List ℕ)) :
    (evalClearedEquationJet J k dDen varJets eq).getD j 0 =
      (eq.map fun mon => (evalClearedMonomialJet J k dDen varJets mon).getD j 0).sum := by
  unfold evalClearedEquationJet
  induction eq using List.reverseRecOn with
  | nil =>
    simp only [List.foldl_nil, getD_truncZJet_of_lt hj, List.getD_nil, List.map_nil, List.sum_nil]
  | append_singleton u mon ih =>
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, getD_truncZJet_of_lt hj,
      getD_polyAdd, List.map_append, List.map_singleton, List.sum_append, List.sum_singleton, ih]

/-- **Coefficient specification of `evalClearedEquationJet`** against
`Cslib.BitString.clearedMonomialSumPoly` for `j < J`. -/
theorem getD_evalClearedEquationJet_of_lt {J k j : ℕ} (hj : j < J) (dDen : ℤ)
    {varJets : List (List ℤ)} {θ : ℕ → ℤ[X]} {eq : List (List ℕ)}
    (heq : IsCanonicalEquation eq) (hdeg : ∀ mon ∈ eq, mon.length ≤ k)
    (hθ : ∀ mon ∈ eq, ∀ v ∈ mon, ∀ i < J, rowEntry varJets v i = (θ v).coeff i) :
    (evalClearedEquationJet J k dDen varJets eq).getD j 0 =
      (clearedMonomialSumPoly dDen k θ (eq.map List.toFinset).toFinset).coeff j := by
  rw [getD_evalClearedEquationJet_eq_list_sum hj, clearedMonomialSumPoly,
    Polynomial.finsetSum_coeff]
  have hnd : (eq.map List.toFinset).Nodup :=
    heq.1.map_on fun m₁ hm₁ m₂ hm₂ h => (heq.2 m₁ hm₁).eq_of_toFinset_eq (heq.2 m₂ hm₂) h
  rw [List.sum_toFinset (fun M => (clearedMonomialPoly dDen k θ M).coeff j) hnd, List.map_map]
  exact congrArg List.sum (List.map_congr_left fun mon hmon =>
    getD_evalClearedMonomialJet_of_lt hj dDen (heq.2 mon hmon) (hdeg mon hmon) (hθ mon hmon))

/-- `Polynomial.taylor t` commutes with `clearedMonomialPoly`. -/
theorem taylor_clearedMonomialPoly (t dDen : ℤ) (k : ℕ) (θ₀ : ℕ → ℤ[X]) (M : Finset ℕ) :
    Polynomial.taylor t (clearedMonomialPoly dDen k θ₀ M) =
      clearedMonomialPoly dDen k (fun v => Polynomial.taylor t (θ₀ v)) M := by
  unfold clearedMonomialPoly; rw [taylor_mul, taylor_C]
  exact congrArg _ (map_prod (taylorAlgHom t) θ₀ M)

/-- `Polynomial.taylor t` commutes with `clearedMonomialSumPoly`. -/
theorem taylor_clearedMonomialSumPoly (t dDen : ℤ) (k : ℕ) (θ₀ : ℕ → ℤ[X])
    (𝓜 : Finset (Finset ℕ)) :
    Polynomial.taylor t (clearedMonomialSumPoly dDen k θ₀ 𝓜) =
      clearedMonomialSumPoly dDen k (fun v => Polynomial.taylor t (θ₀ v)) 𝓜 := by
  unfold clearedMonomialSumPoly; rw [map_sum]
  exact Finset.sum_congr rfl fun M _ => taylor_clearedMonomialPoly t dDen k θ₀ M

/-- **Node-$t$ Taylor-shift specialization of `evalClearedEquationJet`** for `j < J`. -/
theorem getD_evalClearedEquationJet_eq_taylor_coeff {J k j : ℕ} (hj : j < J) (t dDen : ℤ)
    {varJets : List (List ℤ)} {θ₀ : ℕ → ℤ[X]} {eq : List (List ℕ)}
    (heq : IsCanonicalEquation eq) (hdeg : ∀ mon ∈ eq, mon.length ≤ k)
    (hθ : ∀ mon ∈ eq, ∀ v ∈ mon, ∀ i < J,
      rowEntry varJets v i = (Polynomial.taylor t (θ₀ v)).coeff i) :
    (evalClearedEquationJet J k dDen varJets eq).getD j 0 =
      (Polynomial.taylor t
        (clearedMonomialSumPoly dDen k θ₀ (eq.map List.toFinset).toFinset)).coeff j := by
  rw [taylor_clearedMonomialSumPoly]
  exact getD_evalClearedEquationJet_of_lt hj dDen heq hdeg hθ

/-- At `j = 0` (`1 ≤ J`), `evalClearedMonomialJet` evaluates to `dDen ^ k * monomial ℤ ... x`. -/
theorem getD_zero_evalClearedMonomialJet {J k : ℕ} (hJ : 1 ≤ J) (dDen : ℤ)
    {varJets : List (List ℤ)} {mon : List ℕ} (hmon : IsCanonicalMonomial mon)
    (hdeg : mon.length ≤ k) (x : ℕ → Bool)
    (hx : ∀ v ∈ mon, rowEntry varJets v 0 = dDen * bitVal ℤ (x v)) :
    (evalClearedMonomialJet J k dDen varJets mon).getD 0 0 =
      dDen ^ k * monomial ℤ mon.toFinset x := by
  have hj : 0 < J := by omega
  let θ : ℕ → ℤ[X] := fun v => ofCoeffList (truncZJet J (varJets.getD v []))
  rw [getD_evalClearedMonomialJet_of_lt hj dDen hmon hdeg (θ := θ) fun v _ i hi => by
      simp only [θ, coeff_ofCoeffList, getD_truncZJet_of_lt hi, rowEntry],
    Polynomial.coeff_zero_eq_eval_zero]
  exact eval_zero_clearedMonomialPoly dDen θ x
    ((List.toFinset_card_of_nodup hmon.nodup).trans_le hdeg) fun v hv => by
      rw [← Polynomial.coeff_zero_eq_eval_zero]
      simpa only [θ, coeff_ofCoeffList, getD_truncZJet_of_lt hj, rowEntry] using
        hx v (List.mem_toFinset.mp hv)

/-- At `j = 0` (`1 ≤ J`), `evalClearedEquationJet` gives `dDen ^ k * monomialSum ℤ ... x`. -/
theorem getD_zero_evalClearedEquationJet {J k : ℕ} (hJ : 1 ≤ J) (dDen : ℤ)
    {varJets : List (List ℤ)} {eq : List (List ℕ)} (heq : IsCanonicalEquation eq)
    (hdeg : ∀ mon ∈ eq, mon.length ≤ k) (x : ℕ → Bool)
    (hx : ∀ mon ∈ eq, ∀ v ∈ mon, rowEntry varJets v 0 = dDen * bitVal ℤ (x v)) :
    (evalClearedEquationJet J k dDen varJets eq).getD 0 0 =
      dDen ^ k * monomialSum ℤ (eq.map List.toFinset).toFinset x := by
  have hj : 0 < J := by omega
  let θ : ℕ → ℤ[X] := fun v => ofCoeffList (truncZJet J (varJets.getD v []))
  rw [getD_evalClearedEquationJet_of_lt hj dDen heq hdeg (θ := θ) fun _ _ _ _ i hi => by
      simp only [θ, coeff_ofCoeffList, getD_truncZJet_of_lt hi, rowEntry],
    Polynomial.coeff_zero_eq_eval_zero]
  refine eval_zero_clearedMonomialSumPoly dDen θ x (fun M hM => ?_) (fun M hM v hv => ?_)
  · obtain ⟨mon, hmon, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hM)
    exact (List.toFinset_card_of_nodup (heq.2 mon hmon).nodup).trans_le (hdeg mon hmon)
  · obtain ⟨mon, hmon, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hM)
    rw [← Polynomial.coeff_zero_eq_eval_zero]
    simpa only [θ, coeff_ofCoeffList, getD_truncZJet_of_lt hj, rowEntry] using
      hx mon hmon v (List.mem_toFinset.mp hv)

/-- **Boolean parity bridge** between `monomialSum ℤ` and `Cslib.Complexity.evalMonomialList`. -/
theorem even_monomialSum_toFinset_iff_evalMonomialList_eq_false {eq : List (List ℕ)}
    (heq : IsCanonicalEquation eq) (x : ℕ → Bool) :
    Even (monomialSum ℤ (eq.map List.toFinset).toFinset x) ↔ evalMonomialList eq x = false := by
  rw [← monomialSum_zmod_two_eq_zero_iff_even]; unfold monomialSum
  rw [← bitVal_evalMonomialList_eq_sum_monomial heq x]
  cases evalMonomialList eq x
  · simp only [Cslib.BitString.bitVal_false]
  · simp only [Cslib.BitString.bitVal_true, one_ne_zero, Bool.true_eq_false]

private lemma polyNorm1_prodMonomialJet_le {J B₀ : ℕ} {varJets : List (List ℤ)} {mon : List ℕ}
    (hjets : ∀ v ∈ mon, polyNorm1 (truncZJet J (varJets.getD v [])) ≤ B₀) :
    polyNorm1 (SparseMonomialJet.prodMonomialJet J varJets mon) ≤ B₀ ^ mon.length := by
  unfold SparseMonomialJet.prodMonomialJet
  induction mon using List.reverseRecOn with
  | nil =>
    rw [List.foldl_nil, polyNorm1_truncZJet, List.length_nil, pow_zero]
    exact (polyNorm1_take_le [1] J).trans
      (by simp only [polyNorm1_cons, polyNorm1_nil, Int.natAbs_one, add_zero, le_rfl])
  | append_singleton u v ih =>
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, List.length_append,
      List.length_singleton]
    have hu := ih fun w hw => hjets w (List.mem_append_left _ hw)
    have hv := hjets v (List.mem_append_right _ (List.mem_singleton_self v))
    exact (polyNorm1_mulZJet_le J _ _).trans ((Nat.mul_le_mul ((polyNorm1_take_le _ J).trans hu)
      ((polyNorm1_take_le _ J).trans hv)).trans_eq (pow_succ B₀ u.length).symm)

/-- **Stage-1 monomial $\ell_1$-norm bound** ([OpenAI2026ETH], Appendix B.2). -/
theorem polyNorm1_evalClearedMonomialJet_le {J k B₀ : ℕ} {dDen : ℤ} (hd : dDen.natAbs ≤ B₀)
    {varJets : List (List ℤ)} {mon : List ℕ} (hdeg : mon.length ≤ k)
    (hjets : ∀ v ∈ mon, polyNorm1 (truncZJet J (varJets.getD v [])) ≤ B₀) :
    polyNorm1 (evalClearedMonomialJet J k dDen varJets mon) ≤ B₀ ^ k := by
  unfold evalClearedMonomialJet
  have hscale : polyNorm1 ([dDen ^ (k - mon.length)].take J) ≤ B₀ ^ (k - mon.length) := by
    refine (polyNorm1_take_le _ J).trans ?_
    simp only [polyNorm1_cons, polyNorm1_nil, add_zero, Int.natAbs_pow]
    exact Nat.pow_le_pow_left hd _
  have hprod := (polyNorm1_take_le _ J).trans (polyNorm1_prodMonomialJet_le hjets)
  exact (polyNorm1_mulZJet_le J _ _).trans
    ((Nat.mul_le_mul hscale hprod).trans_eq (by rw [← pow_add, Nat.sub_add_cancel hdeg]))

private lemma foldl_addJet_norm_le (J : ℕ) {α : Type} (f : α → List ℤ) (M : ℕ) (w : List α)
    (hf : ∀ a ∈ w, polyNorm1 (f a) ≤ M) :
    polyNorm1 (w.foldl (fun acc a => truncZJet J (polyAdd acc (f a))) (truncZJet J [])) ≤
      w.length * M := by
  induction w using List.reverseRecOn with
  | nil =>
    simp only [List.foldl_nil, polyNorm1_truncZJet, List.take_nil, polyNorm1_nil, List.length_nil,
      Nat.zero_mul, le_rfl]
  | append_singleton u a ih =>
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, List.length_append,
      List.length_singleton]
    have hu := ih fun b hb => hf b (List.mem_append_left _ hb)
    have ha := hf a (List.mem_append_right _ (List.mem_singleton_self a))
    rw [polyNorm1_truncZJet]
    exact (polyNorm1_take_le _ J).trans
      ((polyNorm1_polyAdd_le _ _).trans ((Nat.add_le_add hu ha).trans_eq (by ring)))

/-- **Stage-1 equation $\ell_1$-norm bound** ([OpenAI2026ETH], Appendix B.2, $B = w \cdot B_0^k$).
-/
theorem polyNorm1_evalClearedEquationJet_le {J k B₀ : ℕ} {dDen : ℤ} (hd : dDen.natAbs ≤ B₀)
    {varJets : List (List ℤ)} (hjets : ∀ q ∈ varJets, polyNorm1 (truncZJet J q) ≤ B₀)
    {eq : List (List ℕ)} (hdeg : ∀ mon ∈ eq, mon.length ≤ k) :
    polyNorm1 (evalClearedEquationJet J k dDen varJets eq) ≤ eq.length * B₀ ^ k :=
  foldl_addJet_norm_le J (evalClearedMonomialJet J k dDen varJets) (B₀ ^ k) eq fun mon hmon =>
    polyNorm1_evalClearedMonomialJet_le hd (hdeg mon hmon) fun v _ =>
      polyNorm1_truncZJet_getD_le hjets v

/-- **Stage-1 entry bit-length bound** ([OpenAI2026ETH], Appendix B.2) under `encIntBin`. -/
theorem length_encIntBin_mem_evalClearedEquationJet_le {J k B₀ : ℕ} {dDen : ℤ}
    (hd : dDen.natAbs ≤ B₀) {varJets : List (List ℤ)}
    (hjets : ∀ q ∈ varJets, polyNorm1 (truncZJet J q) ≤ B₀)
    {eq : List (List ℕ)} (hdeg : ∀ mon ∈ eq, mon.length ≤ k)
    {z : ℤ} (hz : z ∈ evalClearedEquationJet J k dDen varJets eq) :
    (encIntBin z).length ≤ eq.length.size + k * B₀.size + 2 := by
  have h1 : eq.length ≤ 2 ^ eq.length.size := (Nat.lt_size_self _).le
  have h2 : B₀ ^ k ≤ 2 ^ (k * B₀.size) :=
    (Nat.pow_le_pow_left (Nat.lt_size_self _).le k).trans_eq (by rw [← pow_mul, mul_comm])
  exact length_encIntBin_le_of_natAbs_le
    (((natAbs_mem_le_polyNorm1 hz).trans (polyNorm1_evalClearedEquationJet_le hd hjets hdeg)).trans
      ((Nat.mul_le_mul h1 h2).trans_eq (pow_add _ _ _).symm))

/-! ### 4. Composite Stage-1 $\to$ Stage-2 parity-factor $z$-jet (`evalEquationParityFactorJet`) -/

/-- Composite Stage-1 $\to$ Stage-2 single-equation parity-factor $z$-jet evaluator
([OpenAI2026ETH], §5.4 and Appendix B.2) with common equation scale $\Delta = d_{\mathrm{den}}^k$
(unconditionally matching `parityFactorCleared`, and clearing rational denominators by
$\Gamma = \Delta^{2 \ell - 1}$ when $d_{\mathrm{den}} \ne 0$). -/
def evalEquationParityFactorJet (J ℓ k : ℕ) (dDen : ℤ) (varJets : List (List ℤ))
    (eq : List (List ℕ)) : List (List ℤ) :=
  evalParityFactorJet J ℓ (dDen ^ k) (evalClearedEquationJet J k dDen varJets eq)

/-- `evalEquationParityFactorJet` has rectangular shape `J × ℓ` (`IsTableShape J ℓ`). -/
theorem isTableShape_evalEquationParityFactorJet (J ℓ k : ℕ) (dDen : ℤ)
    (varJets : List (List ℤ)) (eq : List (List ℕ)) :
    IsTableShape J ℓ (evalEquationParityFactorJet J ℓ k dDen varJets eq) :=
  isTableShape_evalParityFactorJet J ℓ (dDen ^ k) _

private lemma coeff_parityFactorCleared_congr_below {J ℓ s : ℕ} (Δ : ℤ) {A₁ A₂ : ℤ[X]}
    (hA : ∀ i < J, A₁.coeff i = A₂.coeff i) :
    ∀ j < J, ((parityFactorCleared ℓ (C Δ) A₁).coeff s).coeff j =
      ((parityFactorCleared ℓ (C Δ) A₂).coeff s).coeff j := by
  intro j hj; rw [coeff_parityFactorCleared, coeff_parityFactorCleared]
  split_ifs with hs
  · have hlin : ∀ i < J, (parityBaseDigitCleared ℓ s (C Δ) A₁).coeff i =
        (parityBaseDigitCleared ℓ s (C Δ) A₂).coeff i := fun i hi => by
      unfold parityBaseDigitCleared
      have hcast (c : ℤ) : (c : ℤ[X]) = C c := (eq_intCast C c).symm
      simp only [hcast, coeff_add, coeff_C_mul, hA i hi]
    have hh : ∀ i < J, (hPolyCleared (C Δ) A₁).coeff i = (hPolyCleared (C Δ) A₂).coeff i := by
      unfold hPolyCleared
      exact coeff_eq_below_mul hA fun i hi => by rw [coeff_sub, coeff_sub, hA i hi]
    have hpow : ∀ r, ∀ i < J, (hPolyCleared (C Δ) A₁ ^ r).coeff i =
        (hPolyCleared (C Δ) A₂ ^ r).coeff i := fun r => by
      induction r with
      | zero => intro _ _; simp only [pow_zero]
      | succ r ihr => intro i hi; rw [pow_succ', pow_succ']; exact coeff_eq_below_mul hh ihr i hi
    exact coeff_eq_below_mul (coeff_eq_below_mul (fun _ _ => rfl) hlin) (hpow s) j hj
  · rfl

/-- `Polynomial.taylor t` commutes with taking the $V^s$ coefficient of `parityFactorCleared`. -/
theorem taylor_coeff_parityFactorCleared (t Δ : ℤ) (ℓ s : ℕ) (A : ℤ[X]) :
    Polynomial.taylor t ((parityFactorCleared ℓ (C Δ) A).coeff s) =
      (parityFactorCleared ℓ (C Δ) (Polynomial.taylor t A)).coeff s := by
  rw [coeff_parityFactorCleared, coeff_parityFactorCleared]; split_ifs with hs
  · unfold parityBaseDigitCleared hPolyCleared
    have hcast (c : ℤ) : (c : ℤ[X]) = C c := (eq_intCast C c).symm
    rw [hcast, hcast]; simp only [taylor_mul, taylor_pow, map_add, map_sub, taylor_C]
  · exact map_zero (Polynomial.taylor t)

/-- **Composite Stage-1 $\to$ Stage-2 specification** ([OpenAI2026ETH], §5.4 and Appendix B.2)
against `Cslib.BitString.parityFactorCleared` for `j < J`. -/
theorem evalEquationParityFactorJet_entry_eq_parityFactorCleared {J k j : ℕ} (hj : j < J)
    (ℓ s : ℕ) (dDen : ℤ) {varJets : List (List ℤ)} {θ : ℕ → ℤ[X]} {eq : List (List ℕ)}
    (heq : IsCanonicalEquation eq) (hdeg : ∀ mon ∈ eq, mon.length ≤ k)
    (hθ : ∀ mon ∈ eq, ∀ v ∈ mon, ∀ i < J, rowEntry varJets v i = (θ v).coeff i) :
    rowEntry (evalEquationParityFactorJet J ℓ k dDen varJets eq) j s =
      ((parityFactorCleared ℓ (C (dDen ^ k))
        (clearedMonomialSumPoly dDen k θ (eq.map List.toFinset).toFinset)).coeff s).coeff j := by
  unfold evalEquationParityFactorJet
  rw [evalParityFactorJet_entry_eq_parityFactorCleared hj ℓ s (dDen ^ k)]
  refine coeff_parityFactorCleared_congr_below (dDen ^ k) (fun i hi => ?_) j hj
  have htake : ((evalClearedEquationJet J k dDen varJets eq).take J).getD i 0 =
      (evalClearedEquationJet J k dDen varJets eq).getD i 0 := by
    simpa only [List.drop_zero, zero_add] using
      List.getD_take_drop (evalClearedEquationJet J k dDen varJets eq) 0 hi 0
  rw [coeff_ofCoeffList, htake]; exact getD_evalClearedEquationJet_of_lt hi dDen heq hdeg hθ

/-- **Node-$t$ Taylor-shift specialization of `evalEquationParityFactorJet`** for `j < J`. -/
theorem evalEquationParityFactorJet_entry_eq_taylor_parityFactorCleared {J k j : ℕ} (hj : j < J)
    (ℓ s : ℕ) (t dDen : ℤ) {varJets : List (List ℤ)} {θ₀ : ℕ → ℤ[X]} {eq : List (List ℕ)}
    (heq : IsCanonicalEquation eq) (hdeg : ∀ mon ∈ eq, mon.length ≤ k)
    (hθ : ∀ mon ∈ eq, ∀ v ∈ mon, ∀ i < J,
      rowEntry varJets v i = (Polynomial.taylor t (θ₀ v)).coeff i) :
    rowEntry (evalEquationParityFactorJet J ℓ k dDen varJets eq) j s =
      (Polynomial.taylor t ((parityFactorCleared ℓ (C (dDen ^ k))
        (clearedMonomialSumPoly dDen k θ₀ (eq.map List.toFinset).toFinset)).coeff s)).coeff j := by
  rw [taylor_coeff_parityFactorCleared, taylor_clearedMonomialSumPoly]
  exact evalEquationParityFactorJet_entry_eq_parityFactorCleared hj ℓ s dDen heq hdeg hθ

/-- Constant-in-$z$ ($j = 0$) row-sum evaluation of `evalEquationParityFactorJet` (`1 ≤ J`). -/
theorem evalEquationParityFactorJet_row_zero_sum {J ℓ k : ℕ} (hJ : 1 ≤ J) (dDen : ℤ)
    {varJets : List (List ℤ)} {eq : List (List ℕ)} (heq : IsCanonicalEquation eq)
    (hdeg : ∀ mon ∈ eq, mon.length ≤ k) (x : ℕ → Bool)
    (hx : ∀ mon ∈ eq, ∀ v ∈ mon, rowEntry varJets v 0 = dDen * bitVal ℤ (x v)) :
    ((evalEquationParityFactorJet J ℓ k dDen varJets eq).getD 0 []).sum =
      (dDen ^ k) ^ (2 * ℓ - 1) *
        evalParityAmplifier ℓ (monomialSum ℤ (eq.map List.toFinset).toFinset x) :=
  evalParityFactorJet_row_zero_sum hJ (dDen ^ k) _
    (getD_zero_evalClearedEquationJet hJ dDen heq hdeg x hx)

/-- **Composite factor-table $\ell_1$-norm bound** ([OpenAI2026ETH], Appendix B.2, bound $B_1$). -/
theorem jetL1Norm_evalEquationParityFactorJet_le {J ℓ k B₀ : ℕ} {dDen : ℤ}
    (hd : dDen.natAbs ≤ B₀) {varJets : List (List ℤ)}
    (hjets : ∀ q ∈ varJets, polyNorm1 (truncZJet J q) ≤ B₀)
    {eq : List (List ℕ)} (hdeg : ∀ mon ∈ eq, mon.length ≤ k) :
    jetL1Norm (evalEquationParityFactorJet J ℓ k dDen varJets eq) ≤
      ℓ * 2 ^ (7 * ℓ ^ 2) * (eq.length * B₀ ^ k + dDen.natAbs ^ k + 2) ^ (2 * ℓ - 1) := by
  unfold evalEquationParityFactorJet
  refine (jetL1Norm_evalParityFactorJet_le J ℓ (dDen ^ k) _).trans ?_
  have hy := (polyNorm1_take_le _ J).trans (polyNorm1_evalClearedEquationJet_le hd hjets hdeg)
  rw [Int.natAbs_pow]; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)

/-- **Composite factor-table entry and row-prefix bit-length bound** under `encIntBin`. -/
theorem length_encIntBin_evalEquationParityFactorJet_le {J ℓ k B₀ : ℕ} {dDen : ℤ}
    (hd : dDen.natAbs ≤ B₀) {varJets : List (List ℤ)}
    (hjets : ∀ q ∈ varJets, polyNorm1 (truncZJet J q) ≤ B₀)
    {eq : List (List ℕ)} (hdeg : ∀ mon ∈ eq, mon.length ≤ k)
    {r : List ℤ} (hr : r ∈ evalEquationParityFactorJet J ℓ k dDen varJets eq) (m : ℕ) :
    (encIntBin (r.take m).sum).length ≤
        8 * ℓ ^ 2 + 2 * ℓ * (eq.length * B₀ ^ k + dDen.natAbs ^ k + 2).size + 2 ∧
      ∀ z ∈ r, (encIntBin z).length ≤
        8 * ℓ ^ 2 + 2 * ℓ * (eq.length * B₀ ^ k + dDen.natAbs ^ k + 2).size + 2 := by
  obtain ⟨hsum, hmem⟩ := length_encIntBin_evalParityFactorJet_le hr m
  have hy := (polyNorm1_take_le _ J).trans (polyNorm1_evalClearedEquationJet_le hd hjets hdeg)
  have hsize : (polyNorm1 ((evalClearedEquationJet J k dDen varJets eq).take J) +
      (dDen ^ k).natAbs + 2).size ≤ (eq.length * B₀ ^ k + dDen.natAbs ^ k + 2).size := by
    rw [Int.natAbs_pow]; exact Nat.size_le_size (by omega)
  refine ⟨by nlinarith, fun z hz => ?_⟩
  have hmz := hmem z hz; nlinarith

/-! ### 5. Plain polynomial-time certificates (`ComputableInPolyTime`) -/

section PolyTime

open Turing MultiTapeTM MultiTapeTM.ComputableInPolyTime

variable {α : Type} {encIn : α ↪ List Bool}

private theorem intBin_pow_polytime {base : α → ℤ} {exp : α → ℕ}
    (hb : ComputableInPolyTime base encIn encIntBin)
    (he : ComputableInPolyTime exp encIn encUnary) :
    ComputableInPolyTime (fun x => base x ^ exp x) encIn encIntBin :=
  (show ComputableInPolyTime (fun p : ℤ × ℕ => p.1 ^ p.2)
    (encPair encIntBin encUnary) encIntBin by fun_prop).comp (hb.prod he)

private theorem intBin_sum_polytime :
    ComputableInPolyTime List.sum (encList encIntBin) encIntBin := by fun_prop

private lemma natAbs_succ_le_two_pow_encIntBin (t : ℤ) :
    t.natAbs + 1 ≤ 2 ^ (encIntBin t).length := by
  rw [length_encIntBin]
  exact (Nat.succ_le_of_lt (Nat.lt_size_self t.natAbs)).trans
    (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ _))

private lemma polyNorm1_truncZJet_getD_le_two_pow (J : ℕ) (varJets : List (List ℤ)) (v : ℕ) :
    polyNorm1 (truncZJet J (varJets.getD v [])) ≤
      2 ^ (2 * (encList (encList encIntBin) varJets).length) := by
  refine polyNorm1_truncZJet_getD_le (fun q hq => ?_) v
  rw [polyNorm1_truncZJet]
  exact (polyNorm1_take_le q J).trans ((polyNorm1_le_two_pow_encList q).trans
    (Nat.pow_le_pow_right (by norm_num)
      (Nat.mul_le_mul_left 2 (length_le_encList_of_mem (encList encIntBin) hq))))

/-- Compositional plain polynomial-time certificate for `taylorShiftZJet` on unary `J`. -/
@[fun_prop] theorem computableInPolyTime_taylorShiftZJet {J : α → ℕ} {t : α → ℤ}
    {coeffs : α → List ℤ}
    (hJ : ComputableInPolyTime J encIn encUnary)
    (ht : ComputableInPolyTime t encIn encIntBin)
    (hcoeffs : ComputableInPolyTime coeffs encIn (encList encIntBin)) :
    ComputableInPolyTime (fun x => taylorShiftZJet (J x) (t x) (coeffs x))
      encIn (encList encIntBin) := by
  have hinit := computableInPolyTime_truncZJet hJ (const [])
  unfold taylorShiftZJet
  have hrev : ComputableInPolyTime (fun x => (coeffs x).reverse)
      encIn (encList encIntBin) := by fun_prop
  have hstep : ComputableInPolyTime
      (fun p : ((ℕ × ℤ) × List ℤ) × ℤ =>
        SparseMonomialJet.hornerShiftStep p.1.1.1 p.1.1.2 p.1.2 p.2)
      (encPair (encPair (encPair encUnary encIntBin) (encList encIntBin)) encIntBin)
      (encList encIntBin) := by
    unfold SparseMonomialJet.hornerShiftStep; fun_prop
  let bElem (Lt Lc : ℕ) : ℕ := 2 * Lc + Lc * Lt + 2
  let bound (n Lt Lc : ℕ) : ℕ := n * (2 * bElem Lt Lc + 1)
  have hLt := ht.polyBounded_length; have hLc := hcoeffs.polyBounded_length
  have hpb : PolyBounded (fun x => (encIn x).length)
      (fun x => bound (J x) (encIntBin (t x)).length (encList encIntBin (coeffs x)).length) :=
    hJ.polyBounded.mul (((PolyBounded.const 2).mul
      ((((PolyBounded.const 2).mul hLc).add (hLc.mul hLt)).add (.const 2))).add (.const 1))
  refine foldlWith (par := fun x => (J x, t x))
    (step := fun par acc c => SparseMonomialJet.hornerShiftStep par.1 par.2 acc c)
    (hJ.prod ht) hrev hinit hstep hpb fun x i _ => ?_
  set Lt := (encIntBin (t x)).length; set Lc := (encList encIntBin (coeffs x)).length
  set w := (coeffs x).reverse.take i
  set st := w.foldl (SparseMonomialJet.hornerShiftStep (J x) (t x)) (truncZJet (J x) [])
  obtain ⟨hlen_st, hnorm_st⟩ := foldl_hornerShiftStep_bounds (J x) (t x) w
  have hw_len : w.length ≤ Lc := (List.length_take_le' i (coeffs x).reverse).trans
    (List.length_reverse.trans_le (length_le_length_encList encIntBin (coeffs x)))
  have hw_norm : polyNorm1 w ≤ 2 ^ (2 * Lc) :=
    ((polyNorm1_take_le (coeffs x).reverse i).trans_eq (polyNorm1_reverse (coeffs x))).trans
      (polyNorm1_le_two_pow_encList (coeffs x))
  have ht_pow : ((t x).natAbs + 1) ^ w.length ≤ 2 ^ (Lc * Lt) :=
    ((Nat.pow_le_pow_left (natAbs_succ_le_two_pow_encIntBin (t x)) w.length).trans
      (Nat.pow_le_pow_right (by norm_num) hw_len)).trans_eq (by rw [← pow_mul, mul_comm])
  have hcap : polyNorm1 st ≤ 2 ^ (2 * Lc + Lc * Lt) :=
    hnorm_st.trans ((Nat.mul_le_mul hw_norm ht_pow).trans_eq (pow_add 2 _ _).symm)
  exact (length_encList_le encIntBin st fun z hz =>
    length_encIntBin_le_of_natAbs_le ((natAbs_mem_le_polyNorm1 hz).trans hcap)).trans_eq
    (by rw [hlen_st])

/-- Compositional plain polynomial-time certificate for `combineAffineInputZJet`. -/
@[fun_prop] theorem computableInPolyTime_combineAffineInputZJet
    {J : α → ℕ} {base : α → ℤ} {corrJet : α → List ℤ}
    (hJ : ComputableInPolyTime J encIn encUnary) (hbase : ComputableInPolyTime base encIn encIntBin)
    (hcorr : ComputableInPolyTime corrJet encIn (encList encIntBin)) :
    ComputableInPolyTime (fun a => combineAffineInputZJet (J a) (base a) (corrJet a))
      encIn (encList encIntBin) := by
  have htrunc := computableInPolyTime_truncZJet hJ hcorr
  have hcond := decide_eq' hJ (const 0)
  have hdrop : ComputableInPolyTime (fun a => (truncZJet (J a) (corrJet a)).drop 1)
      encIn (encList encIntBin) :=
    (show ComputableInPolyTime (fun l : List ℤ => l.drop 1)
      (encList encIntBin) (encList encIntBin) by fun_prop).comp htrunc
  have hcons := (show ComputableInPolyTime (fun p : ℤ × List ℤ => p.1 :: p.2)
      (encPair encIntBin (encList encIntBin)) (encList encIntBin) by fun_prop).comp
    (hbase.prod hdrop)
  simpa only [combineAffineInputZJet, Function.comp_apply, decide_eq_true_eq] using
    hcond.ite' (const []) hcons

/-- Compositional plain polynomial-time certificate for `evalBaselineAt` supporting any sized
Boolean list encoding `encX` (both `encBits` and `encList encBool`). -/
@[fun_prop] theorem computableInPolyTime_evalBaselineAt {encX : List Bool ↪ List Bool}
    {t : α → ℤ} {rowCoeffs : α → List (List ℤ)} {x : α → List Bool}
    (ht : ComputableInPolyTime t encIn encIntBin)
    (hrow : ComputableInPolyTime rowCoeffs encIn (encList (encList encIntBin)))
    (hx : ComputableInPolyTime x encIn encX)
    [ListEncoding encBool encX] [SizedListEncoding encBool encX] :
    ComputableInPolyTime (fun a => evalBaselineAt (t a) (rowCoeffs a) (x a)) encIn encIntBin := by
  have hrange := range.comp ((length_list (encList encIntBin)).comp hrow)
  have ha := fst encIn encUnary; have hu := snd encIn encUnary
  have hxu := listGetD_binary (encA := encBool) (encL := encX) false
    (hx.comp ha) (unary_to_binary.comp hu)
  have hcu : ComputableInPolyTime (fun p : α × ℕ => (rowCoeffs p.1).getD p.2 [])
      (encPair encIn encUnary) (encList encIntBin) :=
    listGetD_binary (encA := encList encIntBin) [] (hrow.comp ha) (unary_to_binary.comp hu)
  have hshift := computableInPolyTime_taylorShiftZJet (const 1) (ht.comp ha) hcu
  have hval := (listGetD (encA := encIntBin) (encL := encList encIntBin) 0).comp
    (hshift.prod (const 0))
  have hbody : ComputableInPolyTime
      (fun p : α × ℕ => if (x p.1).getD p.2 false then
        (taylorShiftZJet 1 (t p.1) ((rowCoeffs p.1).getD p.2 [])).getD 0 0 else 0)
      (encPair encIn encUnary) encIntBin := by
    simpa only [Function.comp_apply] using hxu.ite' hval (const 0)
  unfold evalBaselineAt; exact intBin_sum_polytime.comp (mapWithInput hrange hbody)

/-- Compositional plain polynomial-time certificate for `evalTaylorCorrectionZJet` supporting any
sized Boolean list encoding `encU` (both `encBits` and `encList encBool`). -/
@[fun_prop] theorem computableInPolyTime_evalTaylorCorrectionZJet {encU : List Bool ↪ List Bool}
    {J : α → ℕ} {t : α → ℤ} {rowCoeffs : α → List (List ℤ)} {U : α → List Bool}
    (hJ : ComputableInPolyTime J encIn encUnary) (ht : ComputableInPolyTime t encIn encIntBin)
    (hrow : ComputableInPolyTime rowCoeffs encIn (encList (encList encIntBin)))
    (hU : ComputableInPolyTime U encIn encU)
    [ListEncoding encBool encU] [SizedListEncoding encBool encU] :
    ComputableInPolyTime (fun a => evalTaylorCorrectionZJet (J a) (t a) (rowCoeffs a) (U a))
      encIn (encList encIntBin) := by
  let uTerm (a : α) (u : ℕ) : List ℤ :=
    if (U a).getD u false then
      combineAffineInputZJet (J a) 0 (taylorShiftZJet (J a) (t a) ((rowCoeffs a).getD u []))
    else truncZJet (J a) []
  have hrangeU := range.comp ((length_list (encList encIntBin)).comp hrow)
  have ha := fst encIn encUnary; have hu := snd encIn encUnary
  have hUu := listGetD_binary (encA := encBool) (encL := encU) false
    (hU.comp ha) (unary_to_binary.comp hu)
  have hcu : ComputableInPolyTime (fun p : α × ℕ => (rowCoeffs p.1).getD p.2 [])
      (encPair encIn encUnary) (encList encIntBin) :=
    listGetD_binary (encA := encList encIntBin) [] (hrow.comp ha) (unary_to_binary.comp hu)
  have hshift := computableInPolyTime_taylorShiftZJet (hJ.comp ha) (ht.comp ha) hcu
  have hjetT := computableInPolyTime_combineAffineInputZJet (hJ.comp ha) (const 0) hshift
  have hjetF := computableInPolyTime_truncZJet (hJ.comp ha) (const [])
  have hbodyU : ComputableInPolyTime (fun p : α × ℕ => uTerm p.1 p.2)
      (encPair encIn encUnary) (encList encIntBin) := by
    simpa only [uTerm, Function.comp_apply] using hUu.ite' hjetT hjetF
  have huJets : ComputableInPolyTime
      (fun a => (List.range (rowCoeffs a).length).map (uTerm a))
      encIn (encList (encList encIntBin)) := mapWithInput hrangeU hbodyU
  have hcol : ComputableInPolyTime
      (fun p : (α × ℕ) × List ℤ => p.2.getD p.1.2 0)
      (encPair (encPair encIn encUnary) (encList encIntBin)) encIntBin :=
    (listGetD (encA := encIntBin) (encL := encList encIntBin) 0).comp
      ((snd (encPair encIn encUnary) (encList encIntBin)).prod
        ((fst (encPair encIn encUnary) (encList encIntBin)).snd'))
  have hsumJ : ComputableInPolyTime
      (fun p : α × ℕ => (((List.range (rowCoeffs p.1).length).map (uTerm p.1)).map
        fun q => q.getD p.2 0).sum)
      (encPair encIn encUnary) encIntBin := intBin_sum_polytime.comp (mapWithInput (huJets.comp ha)
        hcol)
  unfold evalTaylorCorrectionZJet; exact mapWithInput (range.comp hJ) hsumJ

/-- Compositional plain polynomial-time certificate for `evalAffineInputZJet` supporting both
`encBits` and `encList encBool` for `(U, x)`. -/
@[fun_prop] theorem computableInPolyTime_evalAffineInputZJet {encU encX : List Bool ↪ List Bool}
    {J : α → ℕ} {t : α → ℤ} {rowCoeffs : α → List (List ℤ)} {U x : α → List Bool}
    (hJ : ComputableInPolyTime J encIn encUnary) (ht : ComputableInPolyTime t encIn encIntBin)
    (hrow : ComputableInPolyTime rowCoeffs encIn (encList (encList encIntBin)))
    (hU : ComputableInPolyTime U encIn encU) (hx : ComputableInPolyTime x encIn encX)
    [ListEncoding encBool encU] [SizedListEncoding encBool encU]
    [ListEncoding encBool encX] [SizedListEncoding encBool encX] :
    ComputableInPolyTime (fun a => evalAffineInputZJet (J a) (t a) (rowCoeffs a) (U a) (x a))
      encIn (encList encIntBin) :=
  computableInPolyTime_combineAffineInputZJet hJ (computableInPolyTime_evalBaselineAt ht hrow hx)
    (computableInPolyTime_evalTaylorCorrectionZJet hJ ht hrow hU)

/-- Compositional plain polynomial-time certificate for `evalAffineInputZJetTable` supporting both
`encBits` and `encList encBool` for `(U, x)`. -/
@[fun_prop] theorem computableInPolyTime_evalAffineInputZJetTable
    {encU encX : List Bool ↪ List Bool}
    {J : α → ℕ} {t : α → ℤ} {rowsCoeffs : α → List (List (List ℤ))} {U x : α → List Bool}
    (hJ : ComputableInPolyTime J encIn encUnary) (ht : ComputableInPolyTime t encIn encIntBin)
    (hrows : ComputableInPolyTime rowsCoeffs encIn (encList (encList (encList encIntBin))))
    (hU : ComputableInPolyTime U encIn encU) (hx : ComputableInPolyTime x encIn encX)
    [ListEncoding encBool encU] [SizedListEncoding encBool encU]
    [ListEncoding encBool encX] [SizedListEncoding encBool encX] :
    ComputableInPolyTime (fun a => evalAffineInputZJetTable (J a) (t a) (rowsCoeffs a) (U a) (x a))
      encIn (encList (encList encIntBin)) := by
  let encRow := encList (encList encIntBin)
  have hp1 : ComputableInPolyTime (Prod.fst (α := α) (β := List (List ℤ)))
      (encPair encIn encRow) encIn := fst encIn encRow
  have hp2 : ComputableInPolyTime (Prod.snd (α := α) (β := List (List ℤ)))
      (encPair encIn encRow) encRow := snd encIn encRow
  unfold evalAffineInputZJetTable
  exact mapWithInput hrows (computableInPolyTime_evalAffineInputZJet
    (hJ.comp hp1) (ht.comp hp1) hp2 (hU.comp hp1) (hx.comp hp1))

private theorem prodMonomialJet_polytime {J : α → ℕ} {varJets : α → List (List ℤ)}
    {mon : α → List ℕ}
    (hJ : ComputableInPolyTime J encIn encUnary)
    (hvarJets : ComputableInPolyTime varJets encIn (encList (encList encIntBin)))
    (hmon : ComputableInPolyTime mon encIn (encList encNat)) :
    ComputableInPolyTime (fun x => SparseMonomialJet.prodMonomialJet (J x) (varJets x) (mon x))
      encIn (encList encIntBin) := by
  have hinit := computableInPolyTime_truncZJet hJ (const [1])
  unfold SparseMonomialJet.prodMonomialJet
  let stepFn (par : ℕ × List (List ℤ)) (acc : List ℤ) (v : ℕ) : List ℤ :=
    mulZJet par.1 acc (truncZJet par.1 (par.2.getD v []))
  have hstep : ComputableInPolyTime
      (fun p : ((ℕ × List (List ℤ)) × List ℤ) × ℕ => stepFn p.1.1 p.1.2 p.2)
      (encPair (encPair (encPair encUnary (encList (encList encIntBin))) (encList encIntBin))
        encNat)
      (encList encIntBin) := by
    let encLeft := encPair (encPair encUnary (encList (encList encIntBin))) (encList encIntBin)
    have hget : ComputableInPolyTime
        (fun p : ((ℕ × List (List ℤ)) × List ℤ) × ℕ => p.1.1.2.getD p.2 [])
        (encPair encLeft encNat) (encList encIntBin) :=
      listGetD_binary (encA := encList encIntBin) []
        (fst encLeft encNat).fst'.snd' (snd encLeft encNat)
    dsimp only [stepFn]; fun_prop
  let bElem (Lv Lm : ℕ) : ℕ := 2 * Lv * Lm + 2
  let bound (n Lv Lm : ℕ) : ℕ := n * (2 * bElem Lv Lm + 1)
  have hLv := hvarJets.polyBounded_length; have hLm := hmon.polyBounded_length
  have hpb : PolyBounded (fun x => (encIn x).length)
      (fun x => bound (J x) (encList (encList encIntBin) (varJets x)).length
        (encList encNat (mon x)).length) :=
    hJ.polyBounded.mul (((PolyBounded.const 2).mul
      ((((PolyBounded.const 2).mul hLv).mul hLm).add (.const 2))).add (.const 1))
  refine foldlWith (par := fun x => (J x, varJets x)) (step := stepFn)
    (hJ.prod hvarJets) hmon hinit hstep hpb fun x i _ => ?_
  set Lv := (encList (encList encIntBin) (varJets x)).length
  set Lm := (encList encNat (mon x)).length; set w := (mon x).take i
  set st := SparseMonomialJet.prodMonomialJet (J x) (varJets x) w
  change (encList encIntBin st).length ≤ bound (J x) Lv Lm
  have hw_len : w.length ≤ Lm :=
    (List.length_take_le' i (mon x)).trans (length_le_length_encList encNat (mon x))
  have hnorm : polyNorm1 st ≤ 2 ^ (2 * Lv * Lm) :=
    (polyNorm1_prodMonomialJet_le fun v _ =>
      polyNorm1_truncZJet_getD_le_two_pow (J x) (varJets x) v).trans
      ((Nat.pow_le_pow_right Nat.one_le_two_pow hw_len).trans_eq (pow_mul 2 (2 * Lv) Lm).symm)
  exact (length_encList_le encIntBin st fun z hz =>
    length_encIntBin_le_of_natAbs_le ((natAbs_mem_le_polyNorm1 hz).trans hnorm)).trans_eq
    (by rw [length_prodMonomialJet])

/-- Compositional plain polynomial-time certificate for `evalClearedMonomialJet` on unary `(J, k)`.
-/
@[fun_prop] theorem computableInPolyTime_evalClearedMonomialJet {J k : α → ℕ} {dDen : α → ℤ}
    {varJets : α → List (List ℤ)} {mon : α → List ℕ}
    (hJ : ComputableInPolyTime J encIn encUnary)
    (hk : ComputableInPolyTime k encIn encUnary)
    (hdDen : ComputableInPolyTime dDen encIn encIntBin)
    (hvarJets : ComputableInPolyTime varJets encIn (encList (encList encIntBin)))
    (hmon : ComputableInPolyTime mon encIn (encList encNat)) :
    ComputableInPolyTime
      (fun x => evalClearedMonomialJet (J x) (k x) (dDen x) (varJets x) (mon x))
      encIn (encList encIntBin) := by
  have hexp := unary_sub.comp (hk.prod ((length_list encNat).comp hmon))
  have hscale := singleton_intBin_polytime (intBin_pow_polytime hdDen hexp)
  unfold evalClearedMonomialJet
  exact computableInPolyTime_mulZJet hJ hscale (prodMonomialJet_polytime hJ hvarJets hmon)

/-- Compositional plain polynomial-time certificate for `evalClearedEquationJet` on unary `(J, k)`.
-/
@[fun_prop] theorem computableInPolyTime_evalClearedEquationJet {J k : α → ℕ} {dDen : α → ℤ}
    {varJets : α → List (List ℤ)} {eq : α → List (List ℕ)}
    (hJ : ComputableInPolyTime J encIn encUnary)
    (hk : ComputableInPolyTime k encIn encUnary)
    (hdDen : ComputableInPolyTime dDen encIn encIntBin)
    (hvarJets : ComputableInPolyTime varJets encIn (encList (encList encIntBin)))
    (heq : ComputableInPolyTime eq encIn (encList (encList encNat))) :
    ComputableInPolyTime
      (fun x => evalClearedEquationJet (J x) (k x) (dDen x) (varJets x) (eq x))
      encIn (encList encIntBin) := by
  have hinit := computableInPolyTime_truncZJet hJ (const [])
  unfold evalClearedEquationJet
  let stepFn (par : (ℕ × ℕ) × (ℤ × List (List ℤ))) (acc : List ℤ) (mon : List ℕ) : List ℤ :=
    truncZJet par.1.1 (polyAdd acc (evalClearedMonomialJet par.1.1 par.1.2 par.2.1 par.2.2 mon))
  have hstep : ComputableInPolyTime
      (fun p : (((ℕ × ℕ) × (ℤ × List (List ℤ))) × List ℤ) × List ℕ =>
        stepFn p.1.1 p.1.2 p.2)
      (encPair
        (encPair (encPair (encPair encUnary encUnary) (encPair encIntBin
          (encList (encList encIntBin)))) (encList encIntBin))
        (encList encNat))
      (encList encIntBin) := by dsimp only [stepFn]; fun_prop
  let bElem (K Ld Lv Le : ℕ) : ℕ := Le + K * Ld + 2 * Lv * Le + 2
  let bound (n K Ld Lv Le : ℕ) : ℕ := n * (2 * bElem K Ld Lv Le + 1)
  have hK := hk.polyBounded; have hLd := hdDen.polyBounded_length
  have hLv := hvarJets.polyBounded_length; have hLe := heq.polyBounded_length
  have hpb_elem : PolyBounded (fun x => (encIn x).length)
      (fun x => bElem (k x) (encIntBin (dDen x)).length
        (encList (encList encIntBin) (varJets x)).length
        (encList (encList encNat) (eq x)).length) :=
    ((hLe.add (hK.mul hLd)).add (((PolyBounded.const 2).mul hLv).mul hLe)).add (.const 2)
  have hpb : PolyBounded (fun x => (encIn x).length)
      (fun x => bound (J x) (k x) (encIntBin (dDen x)).length
        (encList (encList encIntBin) (varJets x)).length
        (encList (encList encNat) (eq x)).length) :=
    hJ.polyBounded.mul (((PolyBounded.const 2).mul hpb_elem).add (.const 1))
  refine foldlWith (par := fun x => ((J x, k x), (dDen x, varJets x))) (step := stepFn)
    ((hJ.prod hk).prod (hdDen.prod hvarJets)) heq hinit hstep hpb fun x i _ => ?_
  set K := k x; set Ld := (encIntBin (dDen x)).length
  set Lv := (encList (encList encIntBin) (varJets x)).length
  set Le := (encList (encList encNat) (eq x)).length; set w := (eq x).take i
  set st := evalClearedEquationJet (J x) K (dDen x) (varJets x) w
  change (encList encIntBin st).length ≤ bound (J x) K Ld Lv Le
  have hw_len : w.length ≤ Le :=
    (List.length_take_le' i (eq x)).trans (length_le_length_encList (encList encNat) (eq x))
  have hd_pow : ∀ m : List ℕ, polyNorm1 ([(dDen x) ^ (K - m.length)].take (J x)) ≤ 2 ^ (K * Ld) :=
    fun m => by
      refine (polyNorm1_take_le _ (J x)).trans ?_
      simp only [polyNorm1_cons, polyNorm1_nil, add_zero, Int.natAbs_pow]
      have hd_le := (Nat.le_succ _).trans (natAbs_succ_le_two_pow_encIntBin (dDen x))
      exact ((Nat.pow_le_pow_left hd_le (K - m.length)).trans
        (Nat.pow_le_pow_right Nat.one_le_two_pow (Nat.sub_le K m.length))).trans_eq
        (by rw [← pow_mul, mul_comm])
  have hmon_norm : ∀ m ∈ w,
      polyNorm1 (evalClearedMonomialJet (J x) K (dDen x) (varJets x) m) ≤
        2 ^ (K * Ld + 2 * Lv * Le) := fun m hm => by
    have hm_eq := List.mem_of_mem_take hm
    have hm_len := (length_le_length_encList encNat m).trans
      (length_le_encList_of_mem (encList encNat) hm_eq)
    have hp_le : polyNorm1 (SparseMonomialJet.prodMonomialJet (J x) (varJets x) m) ≤
        2 ^ (2 * Lv * Le) :=
      (polyNorm1_prodMonomialJet_le fun v _ =>
        polyNorm1_truncZJet_getD_le_two_pow (J x) (varJets x) v).trans
        ((Nat.pow_le_pow_right Nat.one_le_two_pow hm_len).trans_eq (pow_mul 2 (2 * Lv) Le).symm)
    exact (polyNorm1_mulZJet_le (J x) _ _).trans
      ((Nat.mul_le_mul (hd_pow m) ((polyNorm1_take_le _ (J x)).trans hp_le)).trans_eq
        (pow_add 2 _ _).symm)
  have hsum_norm : polyNorm1 st ≤ 2 ^ (Le + K * Ld + 2 * Lv * Le) :=
    (foldl_addJet_norm_le (J x) _ _ w hmon_norm).trans
      ((Nat.mul_le_mul_right _ (hw_len.trans Nat.lt_two_pow_self.le)).trans_eq
        (by rw [← pow_add]; congr 1; omega))
  exact (length_encList_le encIntBin st fun z hz =>
    length_encIntBin_le_of_natAbs_le ((natAbs_mem_le_polyNorm1 hz).trans hsum_norm)).trans_eq
    (by rw [length_evalClearedEquationJet])

/-- Compositional plain polynomial-time certificate for `evalEquationParityFactorJet`
([OpenAI2026ETH], Appendix B.2) on unary `(J, ℓ, k)`. -/
@[fun_prop] theorem computableInPolyTime_evalEquationParityFactorJet {J ℓ k : α → ℕ}
    {dDen : α → ℤ} {varJets : α → List (List ℤ)} {eq : α → List (List ℕ)}
    (hJ : ComputableInPolyTime J encIn encUnary)
    (hℓ : ComputableInPolyTime ℓ encIn encUnary)
    (hk : ComputableInPolyTime k encIn encUnary)
    (hdDen : ComputableInPolyTime dDen encIn encIntBin)
    (hvarJets : ComputableInPolyTime varJets encIn (encList (encList encIntBin)))
    (heq : ComputableInPolyTime eq encIn (encList (encList encNat))) :
    ComputableInPolyTime
      (fun x => evalEquationParityFactorJet (J x) (ℓ x) (k x) (dDen x) (varJets x) (eq x))
      encIn (encList (encList encIntBin)) :=
  computableInPolyTime_evalParityFactorJet hJ hℓ (intBin_pow_polytime hdDen hk)
    (computableInPolyTime_evalClearedEquationJet hJ hk hdDen hvarJets heq)

end PolyTime

end Cslib
