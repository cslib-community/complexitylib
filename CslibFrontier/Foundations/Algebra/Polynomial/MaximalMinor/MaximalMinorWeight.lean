/-
Copyright (c) 2026 Yuqing Kong, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuqing Kong, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Algebra.Polynomial.MaximalMinor.MaximalMinorFiltration

/-!
# A weight valuation for generic maximal minors

This file tags selected auxiliary variables by a new univariate variable.
The trailing degree of the resulting polynomial records the least selected
weight occurring in the original multivariate polynomial.  It will be
applied to the last inner `Y`-column in the standard `X ↦ YZ` substitution.

Ported by Christian Reitwiessner from Yuqing Kong's Apache-2.0 formalization,
`MaximalMinorWeight.lean` at commit
`4e27ef9d167be69902385307d40123ec665dc532` of
https://github.com/yuqkong-1844/finite-sample-information-monotones .
The mathematical source is [Kong2027]. This general algebra is intended for
Mathlib; its placement exception is recorded in `UPSTREAM.md`.
-/

public section

namespace Cslib

noncomputable section

open scoped BigOperators MonomialOrder

namespace GenericMaximalMinor

section WeightTag

variable {D σ : Type*} [CommSemiring D]

/-- The additive weight of a multivariate monomial exponent. -/
def monomialWeight (w : σ → ℕ) (d : σ →₀ ℕ) : ℕ :=
  d.sum fun i e ↦ e * w i

@[simp] lemma monomialWeight_zero (w : σ → ℕ) :
    monomialWeight w 0 = 0 := by
  simp [monomialWeight]

/-- Retain every old variable in the coefficient ring and additionally tag
it by `X ^ w i`.  Retaining the old variable makes the transformation
injective on monomials. -/
def weightTagHom (w : σ → ℕ) :
    MvPolynomial σ D →+* Polynomial (MvPolynomial σ D) :=
  MvPolynomial.eval₂Hom
    ((Polynomial.C : MvPolynomial σ D →+*
      Polynomial (MvPolynomial σ D)).comp MvPolynomial.C)
    (fun i ↦ Polynomial.C (MvPolynomial.X i) * Polynomial.X ^ w i)

@[simp] lemma weightTagHom_C (w : σ → ℕ) (a : D) :
    weightTagHom w (MvPolynomial.C a) =
      Polynomial.C (MvPolynomial.C a) := by
  simp [weightTagHom]

@[simp] lemma weightTagHom_X (w : σ → ℕ) (i : σ) :
    weightTagHom w (MvPolynomial.X i) =
      Polynomial.C (MvPolynomial.X i : MvPolynomial σ D) *
        Polynomial.X ^ w i := by
  simp [weightTagHom]

/-- A tagged monomial remains a single monomial; its new exponent is its
additive weight and its coefficient remembers the entire old monomial. -/
lemma weightTagHom_monomial (w : σ → ℕ) (d : σ →₀ ℕ) (a : D) :
    weightTagHom w (MvPolynomial.monomial d a) =
      Polynomial.monomial (monomialWeight w d)
        (MvPolynomial.monomial d a) := by
  classical
  rw [weightTagHom, MvPolynomial.eval₂Hom_monomial]
  simp only [RingHom.coe_comp, Function.comp_apply]
  change Polynomial.C (MvPolynomial.C a) *
      (∏ i ∈ d.support,
        (Polynomial.C (MvPolynomial.X i) *
          Polynomial.X ^ w i) ^ d i) = _
  simp_rw [mul_pow]
  rw [Finset.prod_mul_distrib]
  have hCpow (i : σ) :
      (Polynomial.C (MvPolynomial.X i : MvPolynomial σ D)) ^ d i =
        Polynomial.C ((MvPolynomial.X i : MvPolynomial σ D) ^ d i) := by
    exact (map_pow Polynomial.C
      (MvPolynomial.X i : MvPolynomial σ D) (d i)).symm
  simp_rw [hCpow]
  have hCprod :
      (∏ i ∈ d.support,
        Polynomial.C ((MvPolynomial.X i : MvPolynomial σ D) ^ d i)) =
        Polynomial.C (∏ i ∈ d.support,
          (MvPolynomial.X i : MvPolynomial σ D) ^ d i) := by
    exact (map_prod Polynomial.C
      (fun i ↦ (MvPolynomial.X i : MvPolynomial σ D) ^ d i)
      d.support).symm
  rw [hCprod]
  rw [MvPolynomial.prod_X_pow_eq_monomial]
  rw [← mul_assoc, ← map_mul]
  rw [MvPolynomial.C_mul_monomial]
  simp only [mul_one]
  rw [← Polynomial.C_mul_X_pow_eq_monomial]
  congr 1
  simp_rw [← pow_mul]
  rw [Finset.prod_pow_eq_pow_sum]
  simp [monomialWeight, Finsupp.sum, mul_comm]

lemma weightTagHom_eq_sum (w : σ → ℕ) (p : MvPolynomial σ D) :
    weightTagHom w p =
      ∑ d ∈ p.support,
        Polynomial.monomial (monomialWeight w d)
          (MvPolynomial.monomial d (p.coeff d)) := by
  conv_lhs => rw [MvPolynomial.as_sum p]
  simp only [map_sum, weightTagHom_monomial]

/-- Exact recovery formula for every old and new exponent. -/
lemma coeff_coeff_weightTagHom_eq_ite (w : σ → ℕ)
    (p : MvPolynomial σ D) (d : σ →₀ ℕ) (k : ℕ) :
    (((weightTagHom w p).coeff k).coeff d) =
      if monomialWeight w d = k then p.coeff d else 0 := by
  classical
  rw [weightTagHom_eq_sum]
  change (MvPolynomial.lcoeff D d)
      ((Polynomial.lcoeff (MvPolynomial σ D) k)
        (∑ e ∈ p.support,
          Polynomial.monomial (monomialWeight w e)
            (MvPolynomial.monomial e (p.coeff e)))) = _
  simp only [map_sum, Polynomial.lcoeff_apply,
    MvPolynomial.lcoeff_apply, Polynomial.coeff_monomial]
  by_cases hd : d ∈ p.support
  · rw [Finset.sum_eq_single d]
    · by_cases hw : monomialWeight w d = k
      · rw [ite_eq_left hw, MvPolynomial.coeff_monomial,
          ite_eq_left rfl, ite_eq_left hw]
      · rw [ite_eq_right hw, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, ite_eq_right hw]
    · intro e he hed
      by_cases hw : monomialWeight w e = k
      · rw [ite_eq_left hw, MvPolynomial.coeff_monomial]
        exact ite_eq_right hed
      · rw [ite_eq_right hw, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    · intro hnot
      exact (hnot hd).elim
  · have hcoeff : p.coeff d = 0 := by
      simpa [MvPolynomial.mem_support_iff] using hd
    rw [hcoeff]
    simp only [ite_self]
    apply Finset.sum_eq_zero
    intro e he
    have hed : e ≠ d := by
      intro hed
      subst e
      exact hd he
    by_cases hw : monomialWeight w e = k
    · rw [ite_eq_left hw, MvPolynomial.coeff_monomial]
      exact ite_eq_right hed
    · rw [ite_eq_right hw, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]

/-- The coefficient of the tagged polynomial at the weight of `d` still
has old monomial coefficient `p.coeff d` at the old exponent `d`. -/
lemma coeff_coeff_weightTagHom (w : σ → ℕ)
    (p : MvPolynomial σ D) (d : σ →₀ ℕ) :
    (((weightTagHom w p).coeff (monomialWeight w d)).coeff d) =
      p.coeff d := by
  simpa using coeff_coeff_weightTagHom_eq_ite w p d (monomialWeight w d)

lemma support_coeff_weightTagHom_subset (w : σ → ℕ)
    (p : MvPolynomial σ D) (k : ℕ) :
    ((weightTagHom w p).coeff k).support ⊆ p.support := by
  intro d hd
  have hcoeff : (((weightTagHom w p).coeff k).coeff d) ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hd
  rw [coeff_coeff_weightTagHom_eq_ite] at hcoeff
  by_cases hw : monomialWeight w d = k
  · rw [ite_eq_left hw] at hcoeff
    exact MvPolynomial.mem_support_iff.mpr hcoeff
  · rw [ite_eq_right hw] at hcoeff
    exact (hcoeff rfl).elim

lemma monomialWeight_eq_of_mem_support_coeff_weightTagHom
    (w : σ → ℕ) (p : MvPolynomial σ D) (k : ℕ)
    {d : σ →₀ ℕ} (hd : d ∈ ((weightTagHom w p).coeff k).support) :
    monomialWeight w d = k := by
  have hcoeff : (((weightTagHom w p).coeff k).coeff d) ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hd
  rw [coeff_coeff_weightTagHom_eq_ite] at hcoeff
  by_contra hw
  rw [ite_eq_right hw] at hcoeff
  exact hcoeff rfl

/-- The weight tag is injective: the coefficient ring remembers every old
monomial, while the new polynomial exponent records only its weight. -/
lemma weightTagHom_injective (w : σ → ℕ) :
    Function.Injective (weightTagHom (D := D) w) := by
  intro p q hpq
  apply MvPolynomial.ext
  intro d
  rw [← coeff_coeff_weightTagHom w p d,
    ← coeff_coeff_weightTagHom w q d, hpq]

end WeightTag

section ZeroWeight

variable {D σ : Type*} [CommSemiring D]

/-- Set all positive-weight variables to zero and retain the weight-zero
variables. -/
def zeroWeightHom (w : σ → ℕ) :
    MvPolynomial σ D →+* MvPolynomial σ D :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun i ↦ if w i = 0 then MvPolynomial.X i else 0)

@[simp] lemma zeroWeightHom_C (w : σ → ℕ) (a : D) :
    zeroWeightHom w (MvPolynomial.C a) = MvPolynomial.C a := by
  simp [zeroWeightHom]

@[simp] lemma zeroWeightHom_X (w : σ → ℕ) (i : σ) :
    zeroWeightHom w (MvPolynomial.X i : MvPolynomial σ D) =
      if w i = 0 then (MvPolynomial.X i : MvPolynomial σ D) else 0 := by
  simp [zeroWeightHom]

/-- The constant coefficient of the tag is obtained by setting every
positive-weight old variable to zero. -/
lemma coeff_zero_weightTagHom (w : σ → ℕ) (p : MvPolynomial σ D) :
    (weightTagHom w p).coeff 0 = zeroWeightHom w p := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  have hhom :
      (Polynomial.evalRingHom (0 : MvPolynomial σ D)).comp
          (weightTagHom (D := D) w) =
        zeroWeightHom w := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [weightTagHom, zeroWeightHom]
    · intro i
      by_cases hi : w i = 0
      · simp [weightTagHom, zeroWeightHom, hi]
      · simp [weightTagHom, zeroWeightHom, hi]
  exact RingHom.congr_fun hhom p

end ZeroWeight

section LastYWeight

/-- Weight one precisely on the auxiliary `Y` variables in the final inner
column, and weight zero on every other auxiliary variable. -/
def lastYVarWeight (n m : ℕ) : StandardAuxVar (n + 1) m → ℕ :=
  fun v ↦
    if (ofLex v).1 = Fin.last n then
      match ofLex (ofLex v).2 with
      | Sum.inl _ => 1
      | Sum.inr _ => 0
    else 0

@[simp] lemma lastYVarWeight_standardAuxYVar_last
    {n m : ℕ} (i : Fin (n + 1)) :
    lastYVarWeight n m (standardAuxYVar (Fin.last n) i) = 1 := by
  simp [lastYVarWeight, standardAuxYVar]

@[simp] lemma lastYVarWeight_standardAuxYVar_of_ne
    {n m : ℕ} (q i : Fin (n + 1)) (hq : q ≠ Fin.last n) :
    lastYVarWeight n m (standardAuxYVar q i) = 0 := by
  simp [lastYVarWeight, standardAuxYVar, hq]

@[simp] lemma lastYVarWeight_standardAuxZVar
    {n m : ℕ} (q : Fin (n + 1)) (j : Fin m) :
    lastYVarWeight n m (standardAuxZVar q j) = 0 := by
  by_cases hq : q = Fin.last n
  · subst q
    simp [lastYVarWeight, standardAuxZVar]
  · simp [lastYVarWeight, standardAuxZVar, hq]

/-- The abstract monomial weight is the sum of the exponents of the final
inner-column `Y` variables. -/
lemma monomialWeight_lastYVarWeight {n m : ℕ}
    (d : StandardAuxVar (n + 1) m →₀ ℕ) :
    monomialWeight (lastYVarWeight n m) d =
      ∑ i : Fin (n + 1), d (standardAuxYVar (Fin.last n) i) := by
  classical
  rw [monomialWeight, Finsupp.sum_fintype]
  · let e : (Fin (n + 1) × (Fin (n + 1) ⊕ Fin m)) ≃
        StandardAuxVar (n + 1) m :=
      (Equiv.prodCongr (Equiv.refl _) toLex).trans toLex
    rw [← e.sum_comp]
    rw [Fintype.sum_prod_type]
    simp [e, Fintype.sum_sum_type, lastYVarWeight,
      standardAuxYVar]
  · intro i
    simp

/-- Number of maximal-minor factors in a product.  On a standard product
these are exactly its initial maximal factors. -/
@[expose] def maximalMinorCount {n m : ℕ} :
    List (FinsetMinorIndex n m) → ℕ
  | [] => 0
  | d :: l => if d.rows.card = n then maximalMinorCount l + 1
      else maximalMinorCount l

@[simp] lemma maximalMinorCount_nil {n m : ℕ} :
    maximalMinorCount ([] : List (FinsetMinorIndex n m)) = 0 := rfl

@[simp] lemma maximalMinorCount_cons {n m : ℕ}
    (d : FinsetMinorIndex n m) (l : List (FinsetMinorIndex n m)) :
    maximalMinorCount (d :: l) =
      if d.rows.card = n then maximalMinorCount l + 1
      else maximalMinorCount l := rfl

lemma isStandardMinorList_tail {n m : ℕ}
    (d : FinsetMinorIndex n m) (l : List (FinsetMinorIndex n m))
    (hl : IsStandardMinorList (d :: l)) : IsStandardMinorList l := by
  cases l with
  | nil => trivial
  | cons e l => exact hl.2

lemma maximalMinorCount_eq_zero_of_standard_head_not_maximal
    {n m : ℕ} (d : FinsetMinorIndex n m)
    (l : List (FinsetMinorIndex n m))
    (hl : IsStandardMinorList (d :: l)) (hd : ¬d.IsMaximal) :
    maximalMinorCount (d :: l) = 0 := by
  induction l generalizing d with
  | nil =>
      unfold FinsetMinorIndex.IsMaximal at hd
      simp [maximalMinorCount, hd]
  | cons e l ih =>
      have hde : d ≼ᵢ e := hl.1
      have he : ¬e.IsMaximal := by
        intro he
        exact hd (d.isMaximal_of_le_of_isMaximal hde he)
      have htail : IsStandardMinorList (e :: l) := hl.2
      have hdcard : ¬d.rows.card = n := by
        simpa [FinsetMinorIndex.IsMaximal] using hd
      rw [maximalMinorCount_cons, ite_eq_right hdcard]
      exact ih e htail he

/-- On a standard list the maximal factors form exactly an initial segment,
so a prefix of length `r` exists precisely when the total maximal count is
at least `r`. -/
lemma hasMaximalPrefix_iff_le_maximalMinorCount {n m r : ℕ}
    (l : List (FinsetMinorIndex n m)) (hl : IsStandardMinorList l) :
    HasMaximalPrefix r l ↔ r ≤ maximalMinorCount l := by
  induction r generalizing l with
  | zero => simp
  | succ r ih =>
      cases l with
      | nil => simp [HasMaximalPrefix]
      | cons d l =>
          by_cases hd : d.IsMaximal
          · have htail := isStandardMinorList_tail d l hl
            have hdcard : d.rows.card = n := hd
            simp [HasMaximalPrefix, maximalMinorCount, hd, hdcard,
              ih l htail]
          · have hzero :=
              maximalMinorCount_eq_zero_of_standard_head_not_maximal d l hl hd
            simp [HasMaximalPrefix, hd, hzero]

/-- Reading the final possible row position keeps precisely the maximal
minor factors. -/
lemma minorRowProfile_last_card {n m : ℕ}
    (l : List (FinsetMinorIndex (n + 1) m)) :
    (minorRowProfile l n).card = maximalMinorCount l := by
  change (minorRowColumn l n).length = maximalMinorCount l
  induction l with
  | nil => simp [minorRowColumn]
  | cons d l ih =>
      by_cases hd : d.IsMaximal
      · have hlt : n < d.rows.card := by
          unfold FinsetMinorIndex.IsMaximal at hd
          omega
        change (List.filterMap (fun x ↦ x.rowAt? n) (d :: l)).length = _
        rw [List.filterMap_cons,
          FinsetMinorIndex.rowAt?_eq_some d n hlt]
        change (minorRowColumn l n).length + 1 = _
        rw [ih]
        unfold FinsetMinorIndex.IsMaximal at hd
        simp [maximalMinorCount, hd]
      · have hle : d.rows.card ≤ n := by
          have hcard := d.card_rows_le
          unfold FinsetMinorIndex.IsMaximal at hd
          omega
        change (List.filterMap (fun x ↦ x.rowAt? n) (d :: l)).length = _
        rw [List.filterMap_cons,
          FinsetMinorIndex.rowAt?_eq_none d n hle]
        change (minorRowColumn l n).length = _
        rw [ih]
        unfold FinsetMinorIndex.IsMaximal at hd
        simp [maximalMinorCount, hd]

/-- The diagonal leading exponent of a standard product has final-`Y`
weight equal to the number of maximal-minor factors. -/
lemma monomialWeight_standardDiagonalCode {n m : ℕ}
    (l : List (FinsetMinorIndex (n + 1) m)) :
    monomialWeight (lastYVarWeight n m) (standardDiagonalCode l) =
      maximalMinorCount l := by
  rw [monomialWeight_lastYVarWeight]
  simp only [standardDiagonalCode_row_apply, Fin.val_last]
  calc
    ∑ i : Fin (n + 1), Multiset.count i (minorRowProfile l n) =
        (minorRowProfile l n).card := by
      simp
    _ = maximalMinorCount l := minorRowProfile_last_card l

/-- After `X ↦ YZ`, a maximal minor has zero weight-zero component: an
injective choice of all `n+1` inner indices must use the final one. -/
lemma coeff_zero_weightTag_standardYZHom_maximalMinor
    {D : Type*} [CommRing D] {n m : ℕ}
    (d : FinsetMinorIndex (n + 1) m) (hd : d.IsMaximal) :
    (weightTagHom (lastYVarWeight n m)
        (standardYZHom D (n + 1) m d.poly)).coeff 0 = 0 := by
  rw [coeff_zero_weightTagHom]
  rw [standardYZHom_finsetMinorIndex_poly_injective_expansion]
  simp only [map_sum]
  apply Finset.sum_eq_zero
  intro f hf
  have hinj : Function.Injective f :=
    (Finset.mem_filter.mp hf).2
  have hcard : Fintype.card (Fin d.rows.card) =
      Fintype.card (Fin (n + 1)) := by
    simpa [FinsetMinorIndex.IsMaximal] using hd
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, hcard⟩
  obtain ⟨i, hi⟩ := hbij.2 (Fin.last n)
  have hyzero :
      zeroWeightHom (D := D) (lastYVarWeight n m)
          (∏ j, auxY (D := D) (d.rows.orderEmbOfFin rfl j) (f j)) = 0 := by
    rw [map_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rw [hi]
    simp [auxY, zeroWeightHom]
  rw [map_mul, hyzero, zero_mul]

/-- The composite `X ↦ YZ` substitution followed by the final-`Y` weight
tag. -/
def maximalMinorWeightHom (D : Type*) [CommSemiring D] (n m : ℕ) :
    GenericPoly D (n + 1) m →+*
      Polynomial (StandardAuxPoly D (n + 1) m) :=
  (weightTagHom (D := D) (lastYVarWeight n m)).comp
    (standardYZHom D (n + 1) m).toRingHom

lemma X_dvd_maximalMinorWeightHom_minor_of_maximal
    {D : Type*} [CommRing D] {n m : ℕ}
    (d : FinsetMinorIndex (n + 1) m) (hd : d.IsMaximal) :
    Polynomial.X ∣ maximalMinorWeightHom D n m d.poly := by
  rw [Polynomial.X_dvd_iff]
  exact coeff_zero_weightTag_standardYZHom_maximalMinor d hd

/-- Every maximal factor supplies one factor of the tag variable. -/
lemma X_pow_maximalMinorCount_dvd_maximalMinorWeightHom_minorListPoly
    {D : Type*} [CommRing D] {n m : ℕ}
    (l : List (FinsetMinorIndex (n + 1) m)) :
    Polynomial.X ^ maximalMinorCount l ∣
      maximalMinorWeightHom D n m (minorListPoly (D := D) l) := by
  induction l with
  | nil => simp [maximalMinorWeightHom, minorListPoly]
  | cons d l ih =>
      rw [minorListPoly_cons, map_mul]
      by_cases hd : d.IsMaximal
      · have hx := X_dvd_maximalMinorWeightHom_minor_of_maximal
          (D := D) d hd
        have hmul := mul_dvd_mul hx ih
        unfold FinsetMinorIndex.IsMaximal at hd
        simpa [maximalMinorCount, hd, pow_succ', mul_comm,
          mul_left_comm, mul_assoc] using hmul
      · have hright := dvd_mul_of_dvd_right ih
          (maximalMinorWeightHom D n m d.poly)
        unfold FinsetMinorIndex.IsMaximal at hd
        simpa [maximalMinorCount, hd] using hright

/-- A standard basis product has tagged trailing degree exactly equal to its
number of maximal-minor factors. -/
lemma natTrailingDegree_maximalMinorWeightHom_minorListPoly
    {D : Type*} [CommRing D] [Nontrivial D] {n m : ℕ}
    (l : List (FinsetMinorIndex (n + 1) m))
    (hne : HasNoEmptyMinors l) :
    (maximalMinorWeightHom D n m
      (minorListPoly (D := D) l)).natTrailingDegree =
        maximalMinorCount l := by
  let P : StandardAuxPoly D (n + 1) m :=
    standardYZHom D (n + 1) m (minorListPoly (D := D) l)
  let Q : Polynomial (StandardAuxPoly D (n + 1) m) :=
    maximalMinorWeightHom D n m (minorListPoly (D := D) l)
  have hlead := standardYZHom_minorListPoly_degree_code_monic
    (D := D) l hne
  have hPcoeff : P.coeff (standardDiagonalCode l) = 1 := by
    change (standardYZHom D (n + 1) m
      (minorListPoly (D := D) l)).coeff (standardDiagonalCode l) = 1
    rw [← hlead.1]
    exact hlead.2.coeff_degree
  have hQcoeff_old :
      ((Q.coeff (maximalMinorCount l)).coeff (standardDiagonalCode l)) = 1 := by
    change (((weightTagHom (D := D) (lastYVarWeight n m) P).coeff
        (maximalMinorCount l)).coeff (standardDiagonalCode l)) = 1
    rw [← monomialWeight_standardDiagonalCode l,
      coeff_coeff_weightTagHom]
    exact hPcoeff
  have hQcoeff : Q.coeff (maximalMinorCount l) ≠ 0 := by
    intro hz
    rw [hz, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at hQcoeff_old
    exact zero_ne_one hQcoeff_old
  have hQne : Q ≠ 0 := by
    intro hQ
    rw [hQ, Polynomial.coeff_zero] at hQcoeff
    exact hQcoeff rfl
  apply le_antisymm
  · exact Polynomial.natTrailingDegree_le_of_ne_zero hQcoeff
  · apply Polynomial.le_natTrailingDegree hQne
    exact Polynomial.X_pow_dvd_iff.mp
      (X_pow_maximalMinorCount_dvd_maximalMinorWeightHom_minorListPoly
        (D := D) l)

/-- The first nonzero tagged coefficient retains the same monic diagonal
leading term as the original standard product. -/
lemma trailingCoeffSlice_degree_code_monic
    {D : Type*} [CommRing D] [Nontrivial D] {n m : ℕ}
    (l : List (FinsetMinorIndex (n + 1) m))
    (hne : HasNoEmptyMinors l) :
    let S := (maximalMinorWeightHom D n m
      (minorListPoly (D := D) l)).coeff (maximalMinorCount l)
    (MonomialOrder.lex : MonomialOrder (StandardAuxVar (n + 1) m)).degree S =
        standardDiagonalCode l ∧
      (MonomialOrder.lex : MonomialOrder (StandardAuxVar (n + 1) m)).Monic S := by
  let P : StandardAuxPoly D (n + 1) m :=
    standardYZHom D (n + 1) m (minorListPoly (D := D) l)
  let S : StandardAuxPoly D (n + 1) m :=
    (maximalMinorWeightHom D n m
      (minorListPoly (D := D) l)).coeff (maximalMinorCount l)
  let ord : MonomialOrder (StandardAuxVar (n + 1) m) := MonomialOrder.lex
  have hlead := standardYZHom_minorListPoly_degree_code_monic
    (D := D) l hne
  have hcodecoeff : S.coeff (standardDiagonalCode l) = 1 := by
    change (((weightTagHom (D := D) (lastYVarWeight n m) P).coeff
        (maximalMinorCount l)).coeff (standardDiagonalCode l)) = 1
    rw [← monomialWeight_standardDiagonalCode l,
      coeff_coeff_weightTagHom]
    change (standardYZHom D (n + 1) m
      (minorListPoly (D := D) l)).coeff (standardDiagonalCode l) = 1
    rw [← hlead.1]
    exact hlead.2.coeff_degree
  have hcodeMem : standardDiagonalCode l ∈ S.support :=
    MvPolynomial.mem_support_iff.mpr (by
      rw [hcodecoeff]
      exact one_ne_zero)
  have hupper : ord.toSyn (ord.degree S) ≤
      ord.toSyn (standardDiagonalCode l) := by
    rw [ord.degree_le_iff]
    intro d hd
    have hdP : d ∈ P.support := by
      apply support_coeff_weightTagHom_subset
        (w := lastYVarWeight n m) (p := P)
      exact hd
    have hle := ord.le_degree hdP
    change ord.toSyn d ≤ ord.toSyn (ord.degree P) at hle
    simpa [P, ord, hlead.1] using hle
  have hlower : ord.toSyn (standardDiagonalCode l) ≤
      ord.toSyn (ord.degree S) := ord.le_degree hcodeMem
  have hdegree : ord.degree S = standardDiagonalCode l := by
    apply ord.toSyn.injective
    exact le_antisymm hupper hlower
  constructor
  · exact hdegree
  · rw [MonomialOrder.Monic, MonomialOrder.leadingCoeff, hdegree]
    exact hcodecoeff

/-- The first tagged coefficient of every standard basis product is a
linearly independent family. -/
lemma trailingCoeffSlice_standardBasis_linearIndependent
    {D : Type*} [CommRing D] [Nontrivial D] {n m : ℕ} :
    LinearIndependent D
      (fun s : StandardMinorProductIndex (n + 1) m ↦
        (maximalMinorWeightHom D n m
          (minorListPoly (D := D) s.1)).coeff
            (maximalMinorCount s.1)) := by
  apply monic_family_linearIndependent_of_degree_injective
    (m := (MonomialOrder.lex :
      MonomialOrder (StandardAuxVar (n + 1) m)))
  · intro s
    exact (trailingCoeffSlice_degree_code_monic
      (D := D) s.1 s.2.2).2
  · intro s t hdegree
    have hs := (trailingCoeffSlice_degree_code_monic
      (D := D) s.1 s.2.2).1
    have ht := (trailingCoeffSlice_degree_code_monic
      (D := D) t.1 t.2.2).1
    apply Subtype.ext
    apply standardDiagonalCode_injective_on_standard
      s.2.1 t.2.1 s.2.2 t.2.2
    rw [← hs, ← ht]
    exact hdegree

lemma maximalMinorWeightHom_coeff_smul
    {D : Type*} [CommRing D] {n m k : ℕ}
    (a : D) (f : GenericPoly D (n + 1) m) :
    (maximalMinorWeightHom D n m (a • f)).coeff k =
      a • (maximalMinorWeightHom D n m f).coeff k := by
  rw [MvPolynomial.smul_eq_C_mul, map_mul]
  rw [show maximalMinorWeightHom D n m (MvPolynomial.C a) =
      Polynomial.C (MvPolynomial.C a) by
    simp [maximalMinorWeightHom, standardYZHom, weightTagHom]]
  rw [Polynomial.coeff_C_mul]
  exact (MvPolynomial.smul_eq_C_mul
    ((maximalMinorWeightHom D n m f).coeff k) a).symm

lemma maximalMinorWeightHom_basis_coeff_eq_zero_of_lt_count
    {D : Type*} [CommRing D] {n m k : ℕ}
    (s : StandardMinorProductIndex (n + 1) m)
    (hk : k < maximalMinorCount s.1) :
    (maximalMinorWeightHom D n m
      (minorListPoly (D := D) s.1)).coeff k = 0 := by
  exact (Polynomial.X_pow_dvd_iff.mp
    (X_pow_maximalMinorCount_dvd_maximalMinorWeightHom_minorListPoly
      (D := D) s.1)) k hk

/-- For an arbitrary nonzero polynomial, any certified least
maximal-minor count in its standard-basis support is its tagged trailing
degree. -/
theorem natTrailingDegree_maximalMinorWeightHom_eq_of_isMinCount
    {D : Type*} [CommRing D] [Nontrivial D] {n m : ℕ}
    (f : GenericPoly D (n + 1) m) (_hf : f ≠ 0) (c : ℕ)
    (hc_exists : ∃ s ∈
      ((standardMinorProductBasis D (n + 1) m).repr f).support,
        maximalMinorCount s.1 = c)
    (hc_min : ∀ s ∈
      ((standardMinorProductBasis D (n + 1) m).repr f).support,
        c ≤ maximalMinorCount s.1) :
    (maximalMinorWeightHom D n m f).natTrailingDegree = c := by
  let b := standardMinorProductBasis D (n + 1) m
  let S := (b.repr f).support
  obtain ⟨s₀, hs₀S, hs₀c⟩ :
      ∃ s₀ ∈ S, maximalMinorCount s₀.1 = c := by
    simpa [b, S] using hc_exists
  have hc_le (s : StandardMinorProductIndex (n + 1) m) (hs : s ∈ S) :
      c ≤ maximalMinorCount s.1 := by
    exact hc_min s (by simpa [b, S] using hs)
  have hexpand :
      (b.repr f).sum (fun s a ↦ a • b s) = f := by
    rw [← Finsupp.linearCombination_apply, ← b.repr_symm_apply]
    exact b.repr.symm_apply_apply f
  have hcoeffExpand (k : ℕ) :
      (maximalMinorWeightHom D n m f).coeff k =
        ∑ s ∈ S, (b.repr f) s •
          (maximalMinorWeightHom D n m
            (minorListPoly (D := D) s.1)).coeff k := by
    conv_lhs => rw [← hexpand]
    change (Polynomial.lcoeff (StandardAuxPoly D (n + 1) m) k)
        (maximalMinorWeightHom D n m
          (∑ s ∈ S, (b.repr f) s • b s)) = _
    rw [map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro s hs
    rw [Polynomial.lcoeff_apply]
    rw [maximalMinorWeightHom_coeff_smul]
    change (b.repr f) s •
        (maximalMinorWeightHom D n m
          (standardMinorProductBasis D (n + 1) m s)).coeff k = _
    rw [standardMinorProductBasis_apply]
  have hQc : (maximalMinorWeightHom D n m f).coeff c ≠ 0 := by
    intro hzero
    have hrel :
        ∑ s ∈ S,
          (if maximalMinorCount s.1 = c then (b.repr f) s else 0) •
            (maximalMinorWeightHom D n m
              (minorListPoly (D := D) s.1)).coeff
                (maximalMinorCount s.1) = 0 := by
      rw [← hzero, hcoeffExpand c]
      apply Finset.sum_congr rfl
      intro s hs
      by_cases hsc : maximalMinorCount s.1 = c
      · simp [hsc]
      · have hlt : c < maximalMinorCount s.1 :=
          lt_of_le_of_ne (hc_le s hs) (Ne.symm hsc)
        rw [maximalMinorWeightHom_basis_coeff_eq_zero_of_lt_count s hlt]
        simp [hsc]
    have hzeroCoeff :=
      (linearIndependent_iff'.mp
        (trailingCoeffSlice_standardBasis_linearIndependent
          (D := D) (n := n) (m := m)))
        S (fun s ↦ if maximalMinorCount s.1 = c then (b.repr f) s else 0)
        hrel s₀ hs₀S
    rw [ite_eq_left hs₀c] at hzeroCoeff
    have hs₀ne : (b.repr f) s₀ ≠ 0 := by
      exact Finsupp.mem_support_iff.mp hs₀S
    exact hs₀ne hzeroCoeff
  have hQne : maximalMinorWeightHom D n m f ≠ 0 := by
    intro hQ
    rw [hQ, Polynomial.coeff_zero] at hQc
    exact hQc rfl
  apply le_antisymm
  · exact Polynomial.natTrailingDegree_le_of_ne_zero hQc
  · apply Polynomial.le_natTrailingDegree hQne
    intro k hk
    rw [hcoeffExpand]
    apply Finset.sum_eq_zero
    intro s hs
    have hks : k < maximalMinorCount s.1 :=
      lt_of_lt_of_le hk (hc_le s hs)
    rw [maximalMinorWeightHom_basis_coeff_eq_zero_of_lt_count s hks]
    simp

/-- Least maximal-minor count occurring in the standard-basis support;
defined as zero only for the zero polynomial. -/
noncomputable def standardBasisMaximalOrder
    (D : Type*) [CommRing D] [Nontrivial D] (n m : ℕ)
    (f : GenericPoly D (n + 1) m) : ℕ :=
  let b := standardMinorProductBasis D (n + 1) m
  let S := (b.repr f).support
  if hS : S.Nonempty then
    (S.image (fun s ↦ maximalMinorCount s.1)).min' (hS.image _)
  else 0

lemma natTrailingDegree_maximalMinorWeightHom_eq_standardBasisMaximalOrder
    {D : Type*} [CommRing D] [Nontrivial D] {n m : ℕ}
    (f : GenericPoly D (n + 1) m) (hf : f ≠ 0) :
    (maximalMinorWeightHom D n m f).natTrailingDegree =
      standardBasisMaximalOrder D n m f := by
  let b := standardMinorProductBasis D (n + 1) m
  let S := (b.repr f).support
  have hrepr : b.repr f ≠ 0 := by
    intro hzero
    apply hf
    have h := congrArg b.repr.symm hzero
    simpa using h
  have hS : S.Nonempty := Finsupp.support_nonempty_iff.mpr hrepr
  let C := S.image (fun s ↦ maximalMinorCount s.1)
  have hC : C.Nonempty := hS.image _
  let c := C.min' hC
  have hc_exists : ∃ s ∈
      ((standardMinorProductBasis D (n + 1) m).repr f).support,
        maximalMinorCount s.1 = c := by
    have hcC : c ∈ C := C.min'_mem hC
    rcases Finset.mem_image.mp hcC with ⟨s, hs, hsc⟩
    exact ⟨s, by simpa [b, S] using hs, hsc⟩
  have hc_min : ∀ s ∈
      ((standardMinorProductBasis D (n + 1) m).repr f).support,
        c ≤ maximalMinorCount s.1 := by
    intro s hs
    exact C.min'_le _ (Finset.mem_image.mpr
      ⟨s, by simpa [b, S] using hs, rfl⟩)
  have htrail :=
    natTrailingDegree_maximalMinorWeightHom_eq_of_isMinCount
      (D := D) f hf c hc_exists hc_min
  rw [htrail]
  simp [standardBasisMaximalOrder, b, S, hS, C, c]

lemma le_standardBasisMaximalOrder_iff
    {D : Type*} [CommRing D] [Nontrivial D] {n m r : ℕ}
    (f : GenericPoly D (n + 1) m) (hf : f ≠ 0) :
    r ≤ standardBasisMaximalOrder D n m f ↔
      ∀ s ∈ ((standardMinorProductBasis D (n + 1) m).repr f).support,
        r ≤ maximalMinorCount s.1 := by
  let b := standardMinorProductBasis D (n + 1) m
  let S := (b.repr f).support
  have hrepr : b.repr f ≠ 0 := by
    intro hzero
    apply hf
    have h := congrArg b.repr.symm hzero
    simpa using h
  have hS : S.Nonempty := Finsupp.support_nonempty_iff.mpr hrepr
  let C := S.image (fun s ↦ maximalMinorCount s.1)
  have hC : C.Nonempty := hS.image _
  let c := C.min' hC
  have horder : standardBasisMaximalOrder D n m f = c := by
    simp [standardBasisMaximalOrder, b, S, hS, C, c]
  rw [horder]
  constructor
  · intro hrc s hs
    exact hrc.trans (C.min'_le _ (Finset.mem_image.mpr
      ⟨s, by simpa [b, S] using hs, rfl⟩))
  · intro hall
    have hcC : c ∈ C := C.min'_mem hC
    rcases Finset.mem_image.mp hcC with ⟨s, hs, hsc⟩
    rw [← hsc]
    exact hall s (by simpa [b, S] using hs)

lemma mem_maximalMinorIdealOver_pow_iff_repr_hasMaximalPrefix
    {D : Type*} [CommRing D] [Nontrivial D] {n m r : ℕ}
    (hnm : n + 1 ≤ m) (f : GenericPoly D (n + 1) m) :
    f ∈ maximalMinorIdealOver D (n + 1) m hnm ^ r ↔
      ∀ s ∈ ((standardMinorProductBasis D (n + 1) m).repr f).support,
        HasMaximalPrefix r s.1 := by
  rw [← standardMaximalPrefixIdeal_eq_maximalMinorIdealOver_pow
    D hnm r]
  change f ∈ standardMaximalPrefixSubmodule D (n + 1) m r ↔ _
  rw [standardMaximalPrefixSubmodule_eq_standardBasisPrefixSubmodule
    D (Nat.succ_pos n) r]
  let b := standardMinorProductBasis D (n + 1) m
  let Q : Set (StandardMinorProductIndex (n + 1) m) :=
    {s | HasMaximalPrefix r s.1}
  change f ∈ Submodule.span D (b '' Q) ↔ _
  rw [Module.Basis.mem_span_image (b := b)]
  rfl

/-- Ideal-power membership is exactly the lower bound on the multiplicative
tagged order (with the zero polynomial handled separately). -/
theorem mem_maximalMinorIdealOver_pow_iff_trailingDegree
    {D : Type*} [CommRing D] [Nontrivial D] {n m r : ℕ}
    (hnm : n + 1 ≤ m) (f : GenericPoly D (n + 1) m) :
    f ∈ maximalMinorIdealOver D (n + 1) m hnm ^ r ↔
      f = 0 ∨ r ≤ (maximalMinorWeightHom D n m f).natTrailingDegree := by
  by_cases hf : f = 0
  · subst f
    simp
  · rw [mem_maximalMinorIdealOver_pow_iff_repr_hasMaximalPrefix
      hnm f]
    simp only [hf, false_or]
    rw [natTrailingDegree_maximalMinorWeightHom_eq_standardBasisMaximalOrder
      f hf]
    rw [le_standardBasisMaximalOrder_iff f hf]
    apply forall_congr'
    intro s
    apply imp_congr_right
    intro hs
    exact hasMaximalPrefix_iff_le_maximalMinorCount s.1 s.2.1

end LastYWeight

section YZLeftInverse

/-- Evaluate the auxiliary `Y` matrix at the identity and the auxiliary `Z`
matrix at the original generic matrix. -/
def standardYZEvalBack (D : Type*) [CommSemiring D] (n m : ℕ) :
    StandardAuxPoly D n m →ₐ[D] GenericPoly D n m :=
  MvPolynomial.bind₁ fun v ↦
    match ofLex (ofLex v).2 with
    | Sum.inl i =>
        if (ofLex v).1 = i then 1 else 0
    | Sum.inr j =>
        MvPolynomial.X ((ofLex v).1, j)

@[simp] lemma standardYZEvalBack_auxY
    {D : Type*} [CommSemiring D] {n m : ℕ} (i q : Fin n) :
    standardYZEvalBack D n m (auxY (D := D) i q) =
      if q = i then 1 else 0 := by
  classical
  by_cases h : q = i <;> simp [standardYZEvalBack, auxY, standardAuxYVar, h]

@[simp] lemma standardYZEvalBack_auxZ
    {D : Type*} [CommSemiring D] {n m : ℕ} (q : Fin n) (j : Fin m) :
    standardYZEvalBack D n m (auxZ (D := D) q j) =
      MvPolynomial.X (q, j) := by
  simp [standardYZEvalBack, auxZ, standardAuxZVar]

@[simp] lemma standardYZEvalBack_auxYZEntry
    {D : Type*} [CommSemiring D] {n m : ℕ} (i : Fin n) (j : Fin m) :
    standardYZEvalBack D n m (auxYZEntry (D := D) i j) =
      MvPolynomial.X (i, j) := by
  simp [auxYZEntry]

/-- Evaluation at `Y = 1` is a left inverse to the `X ↦ YZ`
substitution. -/
lemma standardYZEvalBack_standardYZHom
    {D : Type*} [CommSemiring D] {n m : ℕ}
    (f : GenericPoly D n m) :
    standardYZEvalBack D n m (standardYZHom D n m f) = f := by
  have hhom :
      (standardYZEvalBack D n m).toRingHom.comp
          (standardYZHom D n m).toRingHom =
        RingHom.id (GenericPoly D n m) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [standardYZEvalBack, standardYZHom]
    · rintro ⟨i, j⟩
      simp
  exact RingHom.congr_fun hhom f

lemma standardYZHom_injective
    {D : Type*} [CommSemiring D] {n m : ℕ} :
    Function.Injective (standardYZHom D n m) :=
  Function.LeftInverse.injective
    (standardYZEvalBack_standardYZHom (D := D) (n := n) (m := m))

/-- Consequently the composite weight map is also injective. -/
lemma maximalMinorWeightHom_injective
    {D : Type*} [CommSemiring D] {n m : ℕ} :
    Function.Injective (maximalMinorWeightHom D n m) := by
  intro f g hfg
  apply standardYZHom_injective
  apply weightTagHom_injective (lastYVarWeight n m)
  exact hfg

end YZLeftInverse

section PrimeAndPrimary

/-- Strong cancellation detected by the tagged order: if the left factor is
not in the maximal-minor ideal, it can be cancelled modulo every power. -/
theorem mem_maximalMinorIdealOver_pow_of_mul_mem_of_not_mem
    {D : Type*} [CommRing D] [IsDomain D] {n m r : ℕ}
    (hnm : n + 1 ≤ m)
    {a b : GenericPoly D (n + 1) m}
    (hab : a * b ∈ maximalMinorIdealOver D (n + 1) m hnm ^ r)
    (ha : a ∉ maximalMinorIdealOver D (n + 1) m hnm) :
    b ∈ maximalMinorIdealOver D (n + 1) m hnm ^ r := by
  have ha_ne : a ≠ 0 := by
    intro ha0
    apply ha
    rw [ha0]
    exact Ideal.zero_mem _
  have hva : (maximalMinorWeightHom D n m a).natTrailingDegree = 0 := by
    have hnot : ¬(a = 0 ∨
        1 ≤ (maximalMinorWeightHom D n m a).natTrailingDegree) := by
      intro h
      have haPow := (mem_maximalMinorIdealOver_pow_iff_trailingDegree
        (D := D) (r := 1) hnm a).mpr h
      exact ha (by simpa using haPow)
    omega
  rcases (mem_maximalMinorIdealOver_pow_iff_trailingDegree
    (D := D) hnm (a * b)).mp hab with hab0 | habOrder
  · have hb0 : b = 0 := (mul_eq_zero.mp hab0).resolve_left ha_ne
    rw [hb0]
    exact Ideal.zero_mem _
  · by_cases hb0 : b = 0
    · rw [hb0]
      exact Ideal.zero_mem _
    · apply (mem_maximalMinorIdealOver_pow_iff_trailingDegree
        (D := D) hnm b).mpr
      right
      have hQa : maximalMinorWeightHom D n m a ≠ 0 :=
        fun hzero ↦ ha_ne (maximalMinorWeightHom_injective
          (by simpa using hzero))
      have hQb : maximalMinorWeightHom D n m b ≠ 0 :=
        fun hzero ↦ hb0 (maximalMinorWeightHom_injective
          (by simpa using hzero))
      have hmul :
          (maximalMinorWeightHom D n m (a * b)).natTrailingDegree =
            (maximalMinorWeightHom D n m a).natTrailingDegree +
              (maximalMinorWeightHom D n m b).natTrailingDegree := by
        rw [map_mul, Polynomial.natTrailingDegree_mul hQa hQb]
      rw [hmul, hva, zero_add] at habOrder
      exact habOrder

/-- The generic maximal-minor ideal over an integral domain is prime. -/
theorem maximalMinorIdealOver_isPrime
    {D : Type*} [CommRing D] [IsDomain D] {n m : ℕ}
    (hnm : n + 1 ≤ m) :
    (maximalMinorIdealOver D (n + 1) m hnm).IsPrime := by
  rw [Ideal.isPrime_iff]
  constructor
  · intro htop
    have h1 : (1 : GenericPoly D (n + 1) m) ∈
        maximalMinorIdealOver D (n + 1) m hnm := by
      simp [htop]
    have h1pow : (1 : GenericPoly D (n + 1) m) ∈
        maximalMinorIdealOver D (n + 1) m hnm ^ 1 := by
      simpa using h1
    have hbad := (mem_maximalMinorIdealOver_pow_iff_trailingDegree
      (D := D) (r := 1) hnm 1).mp h1pow
    simp [maximalMinorWeightHom] at hbad
  · intro x y hxy
    by_cases hx : x ∈ maximalMinorIdealOver D (n + 1) m hnm
    · exact Or.inl hx
    · right
      have hxypow : x * y ∈
          maximalMinorIdealOver D (n + 1) m hnm ^ 1 := by
        simpa using hxy
      simpa using
        (mem_maximalMinorIdealOver_pow_of_mul_mem_of_not_mem
          (D := D) (r := 1) hnm hxypow hx)

/-- Every positive power of the generic maximal-minor ideal is primary over
an integral domain. -/
theorem maximalMinorIdealOver_pow_isPrimary
    {D : Type*} [CommRing D] [IsDomain D] {n m r : ℕ}
    (hnm : n + 1 ≤ m) (hr : 0 < r) :
    (maximalMinorIdealOver D (n + 1) m hnm ^ r).IsPrimary := by
  let P := maximalMinorIdealOver D (n + 1) m hnm
  have hprime : P.IsPrime := maximalMinorIdealOver_isPrime (D := D) hnm
  have hradical : (P ^ r).radical = P := by
    rw [Ideal.radical_pow P (Nat.ne_of_gt hr), hprime.radical]
  rw [Ideal.isPrimary_iff]
  constructor
  · intro htop
    have h1 : (1 : GenericPoly D (n + 1) m) ∈ P ^ r := by
      simp [P, htop]
    have hbad := (mem_maximalMinorIdealOver_pow_iff_trailingDegree
      (D := D) hnm 1).mp h1
    rcases hbad with hbad | hbad
    · exact one_ne_zero hbad
    · have :
        (maximalMinorWeightHom D n m
          (1 : GenericPoly D (n + 1) m)).natTrailingDegree = 0 := by
        simp [maximalMinorWeightHom]
      omega
  · intro x y hxy
    by_cases hy : y ∈ P
    · right
      rwa [hradical]
    · left
      apply mem_maximalMinorIdealOver_pow_of_mul_mem_of_not_mem
        (D := D) (r := r) hnm (a := y) (b := x) ?_ hy
      simpa [mul_comm] using hxy

/-- Paper-facing square case. -/
theorem maximalMinorIdealOver_sq_isPrimary
    {D : Type*} [CommRing D] [IsDomain D] {n m : ℕ}
    (hnm : n + 1 ≤ m) :
    (maximalMinorIdealOver D (n + 1) m hnm ^ 2).IsPrimary := by
  exact maximalMinorIdealOver_pow_isPrimary (D := D) hnm (by norm_num)

end PrimeAndPrimary

end GenericMaximalMinor

end

end Cslib
