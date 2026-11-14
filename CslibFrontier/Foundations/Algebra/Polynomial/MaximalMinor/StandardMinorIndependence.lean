/-
Copyright (c) 2026 Yuqing Kong, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuqing Kong, Christian Reitwiessner
-/

module
-- upstream: candidate (Mathlib, generic maximal minors)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Algebra.Polynomial.MaximalMinor.StandardMinorProducts
import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Diagonal codes for standard products of minors

This file develops the combinatorial half of linear independence for standard
products.  A minor is read in increasing row and column order.  At a fixed
position `q`, a standard list gives a weakly increasing column; consequently
the multiset of entries occurring in that column determines their order.

Ported by Christian Reitwiessner from Yuqing Kong's Apache-2.0 formalization,
`StandardMinorIndependence.lean` at commit
`4e27ef9d167be69902385307d40123ec665dc532` of
https://github.com/yuqkong-1844/finite-sample-information-monotones .
The mathematical source is [Kong2027]. This general algebra is intended for
Mathlib; its destination is recorded in the upstream marker above.
-/

public section

namespace Cslib

noncomputable section

open scoped BigOperators MonomialOrder

namespace GenericMaximalMinor

/-- A standard list is pairwise ordered, not merely ordered at adjacent
positions. -/
lemma isStandardMinorList_pairwise {n m : ℕ}
    {l : List (FinsetMinorIndex n m)} (hl : IsStandardMinorList l) :
    l.Pairwise (· ≼ᵢ ·) := by
  induction l with
  | nil => simp
  | cons d l ih =>
      cases l with
      | nil => simp
      | cons e l =>
          have hde : d ≼ᵢ e := hl.1
          have htail : IsStandardMinorList (e :: l) := hl.2
          have hpair : (e :: l).Pairwise (· ≼ᵢ ·) := ih htail
          rw [List.pairwise_cons]
          refine ⟨?_, hpair⟩
          intro f hf
          simp only [List.mem_cons] at hf
          rcases hf with rfl | hf
          · exact hde
          · exact finsetMinorIndex_le_trans hde
              ((List.pairwise_cons.mp hpair).1 f hf)

lemma rows_card_anti_of_finsetMinorIndex_le {n m : ℕ}
    {d e : FinsetMinorIndex n m} (hde : d ≼ᵢ e) :
    e.rows.card ≤ d.rows.card :=
  card_ge_of_prefixLE hde.1

lemma cols_card_anti_of_finsetMinorIndex_le {n m : ℕ}
    {d e : FinsetMinorIndex n m} (hde : d ≼ᵢ e) :
    e.cols.card ≤ d.cols.card :=
  card_ge_of_prefixLE hde.2

/-- The `q`-th row entry of a minor, when it exists. -/
@[expose] def FinsetMinorIndex.rowAt? {n m : ℕ} (d : FinsetMinorIndex n m)
    (q : ℕ) : Option (Fin n) :=
  if hq : q < d.rows.card then
    some (d.rows.orderEmbOfFin rfl ⟨q, hq⟩)
  else none

/-- The `q`-th column entry of a minor, when it exists. -/
@[expose] def FinsetMinorIndex.colAt? {n m : ℕ} (d : FinsetMinorIndex n m)
    (q : ℕ) : Option (Fin m) :=
  if hq : q < d.cols.card then
    some (d.cols.orderEmbOfFin rfl ⟨q, hq⟩)
  else none

@[simp] lemma FinsetMinorIndex.rowAt?_eq_some {n m : ℕ}
    (d : FinsetMinorIndex n m) (q : ℕ) (hq : q < d.rows.card) :
    d.rowAt? q = some (d.rows.orderEmbOfFin rfl ⟨q, hq⟩) := by
  simp [FinsetMinorIndex.rowAt?, hq]

@[simp] lemma FinsetMinorIndex.rowAt?_eq_none {n m : ℕ}
    (d : FinsetMinorIndex n m) (q : ℕ) (hq : d.rows.card ≤ q) :
    d.rowAt? q = none := by
  simp [FinsetMinorIndex.rowAt?, hq]

@[simp] lemma FinsetMinorIndex.colAt?_eq_some {n m : ℕ}
    (d : FinsetMinorIndex n m) (q : ℕ) (hq : q < d.cols.card) :
    d.colAt? q = some (d.cols.orderEmbOfFin rfl ⟨q, hq⟩) := by
  simp [FinsetMinorIndex.colAt?, hq]

@[simp] lemma FinsetMinorIndex.colAt?_eq_none {n m : ℕ}
    (d : FinsetMinorIndex n m) (q : ℕ) (hq : d.cols.card ≤ q) :
    d.colAt? q = none := by
  simp [FinsetMinorIndex.colAt?, hq]

/-- The existing `q`-th row entries, in factor order. -/
@[expose] def minorRowColumn {n m : ℕ} (l : List (FinsetMinorIndex n m))
    (q : ℕ) : List (Fin n) :=
  l.filterMap (fun d ↦ d.rowAt? q)

/-- The existing `q`-th column entries, in factor order. -/
def minorColColumn {n m : ℕ} (l : List (FinsetMinorIndex n m))
    (q : ℕ) : List (Fin m) :=
  l.filterMap (fun d ↦ d.colAt? q)

lemma rowAt?_mono_of_finsetMinorIndex_le {n m : ℕ}
    {d e : FinsetMinorIndex n m} (hde : d ≼ᵢ e) {q : ℕ}
    {a b : Fin n} (hda : d.rowAt? q = some a)
    (heb : e.rowAt? q = some b) : a ≤ b := by
  by_cases hdq : q < d.rows.card
  · simp only [FinsetMinorIndex.rowAt?, hdq, dite_true,
      Option.some.injEq] at hda
    by_cases heq : q < e.rows.card
    · simp only [FinsetMinorIndex.rowAt?, heq, dite_true,
        Option.some.injEq] at heb
      subst a
      subst b
      simpa using orderEmbOfFin_le_of_prefixLE hde.1 ⟨q, heq⟩
    · simp [FinsetMinorIndex.rowAt?, heq] at heb
  · simp [FinsetMinorIndex.rowAt?, hdq] at hda

lemma colAt?_mono_of_finsetMinorIndex_le {n m : ℕ}
    {d e : FinsetMinorIndex n m} (hde : d ≼ᵢ e) {q : ℕ}
    {a b : Fin m} (hda : d.colAt? q = some a)
    (heb : e.colAt? q = some b) : a ≤ b := by
  by_cases hdq : q < d.cols.card
  · simp only [FinsetMinorIndex.colAt?, hdq, dite_true,
      Option.some.injEq] at hda
    by_cases heq : q < e.cols.card
    · simp only [FinsetMinorIndex.colAt?, heq, dite_true,
        Option.some.injEq] at heb
      subst a
      subst b
      simpa using orderEmbOfFin_le_of_prefixLE hde.2 ⟨q, heq⟩
    · simp [FinsetMinorIndex.colAt?, heq] at heb
  · simp [FinsetMinorIndex.colAt?, hdq] at hda

/-- Every row-column read from a standard product is sorted. -/
lemma minorRowColumn_sorted {n m : ℕ}
    {l : List (FinsetMinorIndex n m)} (hl : IsStandardMinorList l)
    (q : ℕ) : (minorRowColumn l q).SortedLE := by
  unfold minorRowColumn
  exact (List.Pairwise.filterMap (fun d ↦ d.rowAt? q)
    (fun d e hde a hda b heb ↦
      rowAt?_mono_of_finsetMinorIndex_le hde hda heb)
    (isStandardMinorList_pairwise hl)).sortedLE

/-- Every column-column read from a standard product is sorted. -/
lemma minorColColumn_sorted {n m : ℕ}
    {l : List (FinsetMinorIndex n m)} (hl : IsStandardMinorList l)
    (q : ℕ) : (minorColColumn l q).SortedLE := by
  unfold minorColColumn
  exact (List.Pairwise.filterMap (fun d ↦ d.colAt? q)
    (fun d e hde a hda b heb ↦
      colAt?_mono_of_finsetMinorIndex_le hde hda heb)
    (isStandardMinorList_pairwise hl)).sortedLE

/-- The multiset-valued diagonal code of a list of minors.  This is exactly
the exponent data that will occur in the `Y` variables of the leading
monomial after the `X ↦ YZ` substitution. -/
@[expose] def minorRowProfile {n m : ℕ} (l : List (FinsetMinorIndex n m)) :
    ℕ → Multiset (Fin n) :=
  fun q ↦ (minorRowColumn l q : Multiset (Fin n))

/-- Column half of the diagonal exponent data. -/
def minorColProfile {n m : ℕ} (l : List (FinsetMinorIndex n m)) :
    ℕ → Multiset (Fin m) :=
  fun q ↦ (minorColColumn l q : Multiset (Fin m))

lemma minorRowColumn_eq_of_profile_eq_of_standard {n m : ℕ}
    {l₁ l₂ : List (FinsetMinorIndex n m)}
    (hl₁ : IsStandardMinorList l₁) (hl₂ : IsStandardMinorList l₂)
    (hprofile : minorRowProfile l₁ = minorRowProfile l₂) (q : ℕ) :
    minorRowColumn l₁ q = minorRowColumn l₂ q := by
  apply List.Perm.eq_of_sortedLE (minorRowColumn_sorted hl₁ q)
    (minorRowColumn_sorted hl₂ q)
  rw [← Multiset.coe_eq_coe]
  exact congrFun hprofile q

lemma minorColColumn_eq_of_profile_eq_of_standard {n m : ℕ}
    {l₁ l₂ : List (FinsetMinorIndex n m)}
    (hl₁ : IsStandardMinorList l₁) (hl₂ : IsStandardMinorList l₂)
    (hprofile : minorColProfile l₁ = minorColProfile l₂) (q : ℕ) :
    minorColColumn l₁ q = minorColColumn l₂ q := by
  apply List.Perm.eq_of_sortedLE (minorColColumn_sorted hl₁ q)
    (minorColColumn_sorted hl₂ q)
  rw [← Multiset.coe_eq_coe]
  exact congrFun hprofile q

/-- For a list whose minor sizes weakly decrease, filtering out the factors
which have no `q`-th row does not shift any later existing entry: once one
factor is too short, every later factor is too short. -/
lemma minorRowColumn_get?_eq {n m : ℕ}
    {l : List (FinsetMinorIndex n m)}
    (hl : l.Pairwise (· ≼ᵢ ·)) (i q : ℕ) :
    (minorRowColumn l q)[i]? =
      l[i]?.bind (fun d ↦ d.rowAt? q) := by
  induction l generalizing i with
  | nil => simp [minorRowColumn]
  | cons d l ih =>
      have hhead := (List.pairwise_cons.mp hl).1
      have htail := (List.pairwise_cons.mp hl).2
      by_cases hq : q < d.rows.card
      · cases i with
        | zero => simp [minorRowColumn, FinsetMinorIndex.rowAt?, hq]
        | succ i =>
            simpa [minorRowColumn, FinsetMinorIndex.rowAt?, hq] using
              ih htail i
      · have hq' : d.rows.card ≤ q := Nat.le_of_not_gt hq
        have hall : ∀ e ∈ l, e.rows.card ≤ q := by
          intro e he
          exact (rows_card_anti_of_finsetMinorIndex_le
            (hhead e he)).trans hq'
        have hnone : minorRowColumn l q = [] := by
          rw [minorRowColumn, List.filterMap_eq_nil_iff]
          intro e he
          exact e.rowAt?_eq_none q (hall e he)
        have hout : minorRowColumn (d :: l) q = [] := by
          simpa only [minorRowColumn, List.filterMap_cons,
            d.rowAt?_eq_none q hq'] using hnone
        cases i with
        | zero => simp [hout, FinsetMinorIndex.rowAt?, hq]
        | succ i =>
            have hi := ih htail i
            rw [hnone] at hi
            rw [hout]
            simpa using hi

lemma minorColColumn_get?_eq {n m : ℕ}
    {l : List (FinsetMinorIndex n m)}
    (hl : l.Pairwise (· ≼ᵢ ·)) (i q : ℕ) :
    (minorColColumn l q)[i]? =
      l[i]?.bind (fun d ↦ d.colAt? q) := by
  induction l generalizing i with
  | nil => simp [minorColColumn]
  | cons d l ih =>
      have hhead := (List.pairwise_cons.mp hl).1
      have htail := (List.pairwise_cons.mp hl).2
      by_cases hq : q < d.cols.card
      · cases i with
        | zero => simp [minorColColumn, FinsetMinorIndex.colAt?, hq]
        | succ i =>
            simpa [minorColColumn, FinsetMinorIndex.colAt?, hq] using
              ih htail i
      · have hq' : d.cols.card ≤ q := Nat.le_of_not_gt hq
        have hall : ∀ e ∈ l, e.cols.card ≤ q := by
          intro e he
          exact (cols_card_anti_of_finsetMinorIndex_le
            (hhead e he)).trans hq'
        have hnone : minorColColumn l q = [] := by
          rw [minorColColumn, List.filterMap_eq_nil_iff]
          intro e he
          exact e.colAt?_eq_none q (hall e he)
        have hout : minorColColumn (d :: l) q = [] := by
          simpa only [minorColColumn, List.filterMap_cons,
            d.colAt?_eq_none q hq'] using hnone
        cases i with
        | zero => simp [hout, FinsetMinorIndex.colAt?, hq]
        | succ i =>
            have hi := ih htail i
            rw [hnone] at hi
            rw [hout]
            simpa using hi

/-- Empty minors represent the unit and are therefore omitted from the
indexing family for linear independence. -/
@[expose] def HasNoEmptyMinors {n m : ℕ}
    (l : List (FinsetMinorIndex n m)) : Prop :=
  ∀ d ∈ l, d.rows.Nonempty

lemma minorRowColumn_zero_length {n m : ℕ}
    {l : List (FinsetMinorIndex n m)} (hl : HasNoEmptyMinors l) :
    (minorRowColumn l 0).length = l.length := by
  revert hl
  induction l with
  | nil => intro; simp [minorRowColumn]
  | cons d l ih =>
      intro hl
      have hd : 0 < d.rows.card := Finset.card_pos.mpr (hl d (by simp))
      have htail : HasNoEmptyMinors l := by
        intro e he
        exact hl e (by simp [he])
      change
        (List.filterMap (fun e ↦ e.rowAt? 0) (d :: l)).length =
          (d :: l).length
      rw [List.filterMap_cons, d.rowAt?_eq_some 0 hd]
      simp only [List.length_cons]
      exact congrArg Nat.succ (ih htail)

lemma rows_eq_of_rowAt?_eq {n m : ℕ}
    {d e : FinsetMinorIndex n m}
    (h : ∀ q : ℕ, d.rowAt? q = e.rowAt? q) : d.rows = e.rows := by
  have hnotlt₁ : ¬d.rows.card < e.rows.card := by
    intro hlt
    have hq := h d.rows.card
    simp [FinsetMinorIndex.rowAt?, hlt] at hq
  have hnotlt₂ : ¬e.rows.card < d.rows.card := by
    intro hlt
    have hq := h e.rows.card
    simp [FinsetMinorIndex.rowAt?, hlt] at hq
  have hcard : d.rows.card = e.rows.card := by omega
  have hpoint (q : Fin d.rows.card) :
      d.rows.orderEmbOfFin rfl q =
        e.rows.orderEmbOfFin rfl
          ⟨q.val, by simpa [hcard] using q.isLt⟩ := by
    let qe : Fin e.rows.card :=
      ⟨q.val, by simpa [hcard] using q.isLt⟩
    have hdq : d.rowAt? q.val = some (d.rows.orderEmbOfFin rfl q) := by
      simp
    have heq : e.rowAt? q.val = some (e.rows.orderEmbOfFin rfl qe) := by
      simpa using e.rowAt?_eq_some q.val qe.isLt
    have hq := h q.val
    rw [hdq, heq] at hq
    exact Option.some.inj hq
  apply Finset.Subset.antisymm
  · intro x hx
    have hxset : x ∈ (d.rows : Set (Fin n)) := hx
    rw [← d.rows.range_orderEmbOfFin rfl] at hxset
    obtain ⟨q, rfl⟩ := hxset
    rw [hpoint q]
    exact e.rows.orderEmbOfFin_mem rfl _
  · intro x hx
    have hxset : x ∈ (e.rows : Set (Fin n)) := hx
    rw [← e.rows.range_orderEmbOfFin rfl] at hxset
    obtain ⟨q, rfl⟩ := hxset
    let qd : Fin d.rows.card := ⟨q.val, by simp [hcard]⟩
    have hp := hpoint qd
    have hqe : (⟨qd.val, by simpa [hcard] using qd.isLt⟩ :
        Fin e.rows.card) = q := Fin.ext rfl
    rw [hqe] at hp
    rw [← hp]
    exact d.rows.orderEmbOfFin_mem rfl qd

lemma cols_eq_of_colAt?_eq {n m : ℕ}
    {d e : FinsetMinorIndex n m}
    (h : ∀ q : ℕ, d.colAt? q = e.colAt? q) : d.cols = e.cols := by
  have hnotlt₁ : ¬d.cols.card < e.cols.card := by
    intro hlt
    have hq := h d.cols.card
    simp [FinsetMinorIndex.colAt?, hlt] at hq
  have hnotlt₂ : ¬e.cols.card < d.cols.card := by
    intro hlt
    have hq := h e.cols.card
    simp [FinsetMinorIndex.colAt?, hlt] at hq
  have hcard : d.cols.card = e.cols.card := by omega
  have hpoint (q : Fin d.cols.card) :
      d.cols.orderEmbOfFin rfl q =
        e.cols.orderEmbOfFin rfl
          ⟨q.val, by simpa [hcard] using q.isLt⟩ := by
    let qe : Fin e.cols.card :=
      ⟨q.val, by simpa [hcard] using q.isLt⟩
    have hdq : d.colAt? q.val = some (d.cols.orderEmbOfFin rfl q) := by
      simp
    have heq : e.colAt? q.val = some (e.cols.orderEmbOfFin rfl qe) := by
      simpa using e.colAt?_eq_some q.val qe.isLt
    have hq := h q.val
    rw [hdq, heq] at hq
    exact Option.some.inj hq
  apply Finset.Subset.antisymm
  · intro x hx
    have hxset : x ∈ (d.cols : Set (Fin m)) := hx
    rw [← d.cols.range_orderEmbOfFin rfl] at hxset
    obtain ⟨q, rfl⟩ := hxset
    rw [hpoint q]
    exact e.cols.orderEmbOfFin_mem rfl _
  · intro x hx
    have hxset : x ∈ (e.cols : Set (Fin m)) := hx
    rw [← e.cols.range_orderEmbOfFin rfl] at hxset
    obtain ⟨q, rfl⟩ := hxset
    let qd : Fin d.cols.card := ⟨q.val, by simp [hcard]⟩
    have hp := hpoint qd
    have hqe : (⟨qd.val, by simpa [hcard] using qd.isLt⟩ :
        Fin e.cols.card) = q := Fin.ext rfl
    rw [hqe] at hp
    rw [← hp]
    exact d.cols.orderEmbOfFin_mem rfl qd

/-- A standard list of nonempty minors is uniquely determined by the row and
column exponent profiles of its diagonal monomial. -/
theorem eq_of_standard_minor_profiles {n m : ℕ}
    {l₁ l₂ : List (FinsetMinorIndex n m)}
    (hl₁ : IsStandardMinorList l₁) (hl₂ : IsStandardMinorList l₂)
    (hne₁ : HasNoEmptyMinors l₁) (hne₂ : HasNoEmptyMinors l₂)
    (hrow : minorRowProfile l₁ = minorRowProfile l₂)
    (hcol : minorColProfile l₁ = minorColProfile l₂) : l₁ = l₂ := by
  have hrowColumn : ∀ q, minorRowColumn l₁ q = minorRowColumn l₂ q :=
    minorRowColumn_eq_of_profile_eq_of_standard hl₁ hl₂ hrow
  have hcolColumn : ∀ q, minorColColumn l₁ q = minorColColumn l₂ q :=
    minorColColumn_eq_of_profile_eq_of_standard hl₁ hl₂ hcol
  have hlen : l₁.length = l₂.length := by
    calc
      l₁.length = (minorRowColumn l₁ 0).length :=
        (minorRowColumn_zero_length hne₁).symm
      _ = (minorRowColumn l₂ 0).length := by rw [hrowColumn 0]
      _ = l₂.length := minorRowColumn_zero_length hne₂
  apply List.ext_get hlen
  intro i hi₁ hi₂
  let d₁ := l₁.get ⟨i, hi₁⟩
  let d₂ := l₂.get ⟨i, hi₂⟩
  have hrowAt : ∀ q, d₁.rowAt? q = d₂.rowAt? q := by
    intro q
    have hg₁ := minorRowColumn_get?_eq
      (isStandardMinorList_pairwise hl₁) i q
    have hg₂ := minorRowColumn_get?_eq
      (isStandardMinorList_pairwise hl₂) i q
    rw [List.getElem?_eq_getElem hi₁] at hg₁
    rw [List.getElem?_eq_getElem hi₂] at hg₂
    simpa [d₁, d₂] using
      hg₁.symm.trans ((congrArg (fun s ↦ s[i]?) (hrowColumn q)).trans hg₂)
  have hcolAt : ∀ q, d₁.colAt? q = d₂.colAt? q := by
    intro q
    have hg₁ := minorColColumn_get?_eq
      (isStandardMinorList_pairwise hl₁) i q
    have hg₂ := minorColColumn_get?_eq
      (isStandardMinorList_pairwise hl₂) i q
    rw [List.getElem?_eq_getElem hi₁] at hg₁
    rw [List.getElem?_eq_getElem hi₂] at hg₂
    simpa [d₁, d₂] using
      hg₁.symm.trans ((congrArg (fun s ↦ s[i]?) (hcolColumn q)).trans hg₂)
  exact finsetMinorIndex_ext (rows_eq_of_rowAt?_eq hrowAt)
    (cols_eq_of_colAt?_eq hcolAt)

/-- Variables in the auxiliary `Y,Z` ring, ordered in blocks indexed by the
inner matrix coordinate. -/
abbrev StandardAuxVar (n m : ℕ) := Fin n ×ₗ (Fin n ⊕ₗ Fin m)

/-- The auxiliary polynomial ring for the generic matrix factorization. -/
abbrev StandardAuxPoly (D : Type*) [CommSemiring D] (n m : ℕ) :=
  MvPolynomial (StandardAuxVar n m) D

/-- An auxiliary variable in the first factor of the generic matrix factorization. -/
@[expose] def standardAuxYVar {n m : ℕ} (q i : Fin n) : StandardAuxVar n m :=
  toLex (q, toLex (Sum.inl i))

/-- An auxiliary variable in the second factor of the generic matrix factorization. -/
@[expose] def standardAuxZVar {n m : ℕ} (q : Fin n) (j : Fin m) :
    StandardAuxVar n m :=
  toLex (q, toLex (Sum.inr j))

lemma Equiv.Perm.exists_first_moved_up {p : ℕ}
    (u : Equiv.Perm (Fin p)) (hu : u ≠ 1) :
    ∃ i : Fin p, (∀ j, j < i → u j = j) ∧ i < u i := by
  let moved : Finset (Fin p) := Finset.univ.filter fun i ↦ u i ≠ i
  have hmoved : moved.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    apply hu
    apply Equiv.ext
    intro i
    have hi : i ∉ moved := by simp [hempty]
    simpa [moved] using hi
  let i := moved.min' hmoved
  have hiMoved : u i ≠ i := by
    have hi := moved.min'_mem hmoved
    simpa [moved] using hi
  have hprev : ∀ j, j < i → u j = j := by
    intro j hji
    by_contra hj
    have hjmem : j ∈ moved := by simp [moved, hj]
    have hmin : i ≤ j := moved.min'_le j hjmem
    exact (not_le_of_gt hji) hmin
  refine ⟨i, hprev, ?_⟩
  have hnotlt : ¬u i < i := by
    intro hui
    have hfix : u (u i) = u i := hprev (u i) hui
    exact hiMoved (u.injective hfix)
  exact lt_of_le_of_ne (le_of_not_gt hnotlt) hiMoved.symm

/-- A strictly increasing choice of `p` elements of `Fin n` which is not the
initial choice first moves to the right. -/
lemma OrderEmbedding.Fin.exists_first_ne_castLE_up {p n : ℕ} (hpn : p ≤ n)
    (q : Fin p ↪o Fin n) (hq : q ≠ Fin.castLEOrderEmb hpn) :
    ∃ i : Fin p,
      (∀ j, j < i → q j = Fin.castLEOrderEmb hpn j) ∧
        Fin.castLEOrderEmb hpn i < q i := by
  let moved : Finset (Fin p) := Finset.univ.filter fun i ↦
    q i ≠ Fin.castLEOrderEmb hpn i
  have hmoved : moved.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    apply hq
    apply RelEmbedding.ext
    intro i
    by_contra hi
    have himem : i ∈ moved := Finset.mem_filter.mpr
      ⟨Finset.mem_univ i, hi⟩
    simp [hempty] at himem
  let i := moved.min' hmoved
  have hiMoved : q i ≠ Fin.castLEOrderEmb hpn i := by
    have hi := moved.min'_mem hmoved
    exact (Finset.mem_filter.mp hi).2
  have hprev : ∀ j, j < i → q j = Fin.castLEOrderEmb hpn j := by
    intro j hji
    by_contra hj
    have hjmem : j ∈ moved := Finset.mem_filter.mpr
      ⟨Finset.mem_univ j, hj⟩
    have hmin : i ≤ j := moved.min'_le j hjmem
    exact (not_le_of_gt hji) hmin
  refine ⟨i, hprev, ?_⟩
  have hnotlt : ¬q i < Fin.castLEOrderEmb hpn i := by
    intro hqi
    let j : Fin p := ⟨(q i).val, by
      have : (q i).val < i.val := by
        change (q i).val < i.val at hqi
        exact hqi
      exact this.trans i.isLt⟩
    have hji : j < i := by
      change (q i).val < i.val
      change (q i).val < i.val at hqi
      exact hqi
    have hqj : q j = Fin.castLEOrderEmb hpn j := hprev j hji
    have hcast : Fin.castLEOrderEmb hpn j = q i := by
      apply Fin.ext
      rfl
    have hjiEq : j = i := q.injective (hqj.trans hcast)
    exact (ne_of_lt hji) hjiEq
  exact lt_of_le_of_ne (le_of_not_gt hnotlt) hiMoved.symm

/-- Exponent vector of the determinant term indexed by a permutation.  The
outer embedding gives the variable blocks and the inner embedding gives the
ordered variables within each block. -/
def blockPermutationExponent {p n m : ℕ}
    (q : Fin p ↪o Fin n) (a : Fin p ↪o (Fin n ⊕ₗ Fin m))
    (u : Equiv.Perm (Fin p)) : StandardAuxVar n m →₀ ℕ :=
  ∑ j, Finsupp.single (toLex (q j, a (u j))) 1

/-- The combined diagonal exponent of two determinants using the same outer
blocks (the `Y` and `Z` determinants in Cauchy--Binet). -/
def twoBlockDiagonalExponent {p n m : ℕ}
    (q : Fin p ↪o Fin n)
    (a b : Fin p ↪o (Fin n ⊕ₗ Fin m)) : StandardAuxVar n m →₀ ℕ :=
  blockPermutationExponent q a 1 + blockPermutationExponent q b 1

lemma finsupp_fintype_sum_apply {I α : Type*} [Fintype I]
    {M : Type*} [AddCommMonoid M] (f : I → α →₀ M) (x : α) :
    (∑ i, f i) x = ∑ i, f i x := by
  classical
  change (Finsupp.applyAddHom x) (∑ i, f i) = _
  rw [map_sum]
  simp only [Finsupp.applyAddHom_apply]

lemma blockPermutationExponent_apply_own {p n m : ℕ}
    (q : Fin p ↪o Fin n) (a : Fin p ↪o (Fin n ⊕ₗ Fin m))
    (u : Equiv.Perm (Fin p)) (k : Fin p) :
    blockPermutationExponent q a u (toLex (q k, a (u k))) = 1 := by
  classical
  rw [blockPermutationExponent]
  rw [finsupp_fintype_sum_apply]
  rw [Finset.sum_eq_single k]
  · simp
  · intro j hj hjk
    simp only [Finsupp.single_apply]
    rw [ite_eq_right]
    intro heq
    exact hjk (q.injective (congrArg (fun v ↦ (ofLex v).1) heq))
  · simp

lemma blockPermutationExponent_apply_same_outer {p n m : ℕ}
    (q : Fin p ↪o Fin n) (a : Fin p ↪o (Fin n ⊕ₗ Fin m))
    (i : Fin p) (c : Fin n ⊕ₗ Fin m) :
    blockPermutationExponent q a 1 (toLex (q i, c)) =
      if a i = c then 1 else 0 := by
  classical
  rw [blockPermutationExponent, finsupp_fintype_sum_apply]
  rw [Finset.sum_eq_single i]
  · simp [Finsupp.single_apply]
  · intro j hj hji
    simp only [Equiv.Perm.one_apply, Finsupp.single_apply]
    rw [ite_eq_right]
    intro heq
    exact hji (q.injective (congrArg (fun v ↦ (ofLex v).1) heq))
  · simp

lemma blockPermutationExponent_apply_of_outer_ne {p n m : ℕ}
    (q : Fin p ↪o Fin n) (a : Fin p ↪o (Fin n ⊕ₗ Fin m))
    (r : Fin n) (c : Fin n ⊕ₗ Fin m) (hr : ∀ i, q i ≠ r) :
    blockPermutationExponent q a 1 (toLex (r, c)) = 0 := by
  classical
  rw [blockPermutationExponent, finsupp_fintype_sum_apply]
  apply Finset.sum_eq_zero
  intro i hi
  simp only [Equiv.Perm.one_apply, Finsupp.single_apply]
  rw [ite_eq_right]
  intro heq
  exact hr i (congrArg (fun v ↦ (ofLex v).1) heq)

lemma blockPermutationExponent_apply_identity_zero_of_moved
    {p n m : ℕ}
    (q : Fin p ↪o Fin n) (a : Fin p ↪o (Fin n ⊕ₗ Fin m))
    (u : Equiv.Perm (Fin p)) (i : Fin p) (hui : u i ≠ i) :
    blockPermutationExponent q a u (toLex (q i, a i)) = 0 := by
  classical
  rw [blockPermutationExponent]
  rw [finsupp_fintype_sum_apply]
  apply Finset.sum_eq_zero
  intro j hj
  simp only [Finsupp.single_apply]
  rw [ite_eq_right]
  intro heq
  have hji : j = i := q.injective (congrArg (fun v ↦ (ofLex v).1) heq)
  subst j
  have hai : a (u i) = a i := congrArg (fun v ↦ (ofLex v).2) heq
  exact hui (a.injective hai)

/-- In lexicographic order, the identity term of a generic determinant is
strictly larger than every other permutation term. -/
lemma blockPermutationExponent_lt_identity {p n m : ℕ}
    (q : Fin p ↪o Fin n) (a : Fin p ↪o (Fin n ⊕ₗ Fin m))
    (u : Equiv.Perm (Fin p)) (hu : u ≠ 1) :
    blockPermutationExponent q a u ≺[MonomialOrder.lex]
      blockPermutationExponent q a 1 := by
  classical
  obtain ⟨i, hprev, hiu⟩ := Equiv.Perm.exists_first_moved_up u hu
  rw [MonomialOrder.lex_lt_iff, Finsupp.Lex.lt_iff]
  refine ⟨toLex (q i, a i), ?_, ?_⟩
  · intro v hv
    simp only [ofLex_toLex]
    rw [blockPermutationExponent, blockPermutationExponent,
      finsupp_fintype_sum_apply, finsupp_fintype_sum_apply]
    simp only [Equiv.Perm.one_apply]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hji : j < i
    · rw [hprev j hji]
    · have hij : i ≤ j := le_of_not_gt hji
      have hneId : toLex (q j, a j) ≠ v := by
        intro heq
        rw [← heq] at hv
        simp only [Prod.Lex.lt_iff, ofLex_toLex] at hv
        rcases hv with hqji | ⟨hqji, haji⟩
        · exact (not_lt_of_ge hij) (q.lt_iff_lt.mp hqji)
        · have hji' : j = i := q.injective hqji
          subst j
          exact lt_irrefl _ haji
      have hneU : toLex (q j, a (u j)) ≠ v := by
        intro heq
        rw [← heq] at hv
        simp only [Prod.Lex.lt_iff, ofLex_toLex] at hv
        rcases hv with hqji | ⟨hqji, haui⟩
        · exact (not_lt_of_ge hij) (q.lt_iff_lt.mp hqji)
        · have hji' : j = i := q.injective hqji
          subst j
          exact (not_lt_of_ge (a.monotone hiu.le)) haui
      simp [hneId, hneU]
  · change blockPermutationExponent q a u (toLex (q i, a i)) <
      blockPermutationExponent q a 1 (toLex (q i, a i))
    rw [blockPermutationExponent_apply_identity_zero_of_moved
      q a u i hiu.ne']
    have hval : blockPermutationExponent q a 1 (toLex (q i, a i)) = 1 := by
      simpa using blockPermutationExponent_apply_own q a
        (1 : Equiv.Perm (Fin p)) i
    rw [hval]
    norm_num

/-- Among increasing choices of outer blocks, the initial segment has the
unique largest combined diagonal exponent. -/
lemma twoBlockDiagonalExponent_lt_initial {p n m : ℕ} (hpn : p ≤ n)
    (q : Fin p ↪o Fin n) (a b : Fin p ↪o (Fin n ⊕ₗ Fin m))
    (hab : ∀ i, a i < b i) (hq : q ≠ Fin.castLEOrderEmb hpn) :
    twoBlockDiagonalExponent q a b ≺[MonomialOrder.lex]
      twoBlockDiagonalExponent (Fin.castLEOrderEmb hpn) a b := by
  classical
  obtain ⟨i, hprev, hiq⟩ :=
    OrderEmbedding.Fin.exists_first_ne_castLE_up hpn q hq
  rw [MonomialOrder.lex_lt_iff, Finsupp.Lex.lt_iff]
  refine ⟨toLex (Fin.castLEOrderEmb hpn i, a i), ?_, ?_⟩
  · intro v hv
    simp only [ofLex_toLex]
    rw [twoBlockDiagonalExponent, twoBlockDiagonalExponent,
      Finsupp.add_apply, Finsupp.add_apply,
      blockPermutationExponent, blockPermutationExponent,
      blockPermutationExponent, blockPermutationExponent]
    simp only [Equiv.Perm.one_apply, finsupp_fintype_sum_apply]
    apply congrArg₂ (· + ·)
    · apply Finset.sum_congr rfl
      intro j hj
      by_cases hji : j < i
      · rw [hprev j hji]
      · have hij : i ≤ j := le_of_not_gt hji
        have hInitialNe :
            toLex (Fin.castLE hpn j, a j) ≠ v := by
          intro heq
          rw [← heq] at hv
          simp only [Prod.Lex.lt_iff, ofLex_toLex] at hv
          rcases hv with houter | ⟨houter, hinner⟩
          · exact (not_lt_of_ge hij) ((Fin.castLEOrderEmb hpn).lt_iff_lt.mp houter)
          · have hjiEq : j = i :=
              (Fin.castLEOrderEmb hpn).injective houter
            subst j
            exact lt_irrefl _ hinner
        have hActualNe : toLex (q j, a j) ≠ v := by
          intro heq
          rw [← heq] at hv
          simp only [Prod.Lex.lt_iff, ofLex_toLex] at hv
          rcases hv with houter | ⟨houter, hinner⟩
          · exact (not_lt_of_ge (hiq.le.trans (q.monotone hij))) houter
          · exact (ne_of_gt (hiq.trans_le (q.monotone hij))) houter
        simp [hInitialNe, hActualNe]
    · apply Finset.sum_congr rfl
      intro j hj
      by_cases hji : j < i
      · rw [hprev j hji]
      · have hij : i ≤ j := le_of_not_gt hji
        have hInitialNe :
            toLex (Fin.castLE hpn j, b j) ≠ v := by
          intro heq
          rw [← heq] at hv
          simp only [Prod.Lex.lt_iff, ofLex_toLex] at hv
          rcases hv with houter | ⟨houter, hinner⟩
          · exact (not_lt_of_ge hij) ((Fin.castLEOrderEmb hpn).lt_iff_lt.mp houter)
          · have hjiEq : j = i :=
              (Fin.castLEOrderEmb hpn).injective houter
            subst j
            exact (not_lt_of_ge (hab i).le) hinner
        have hActualNe : toLex (q j, b j) ≠ v := by
          intro heq
          rw [← heq] at hv
          simp only [Prod.Lex.lt_iff, ofLex_toLex] at hv
          rcases hv with houter | ⟨houter, hinner⟩
          · exact (not_lt_of_ge (hiq.le.trans (q.monotone hij))) houter
          · exact (ne_of_gt (hiq.trans_le (q.monotone hij))) houter
        simp [hInitialNe, hActualNe]
  · simp only [ofLex_toLex]
    rw [twoBlockDiagonalExponent, twoBlockDiagonalExponent,
      Finsupp.add_apply, Finsupp.add_apply]
    have hActualA : blockPermutationExponent q a 1
        (toLex (Fin.castLEOrderEmb hpn i, a i)) = 0 := by
      rw [blockPermutationExponent, finsupp_fintype_sum_apply]
      apply Finset.sum_eq_zero
      intro j hj
      simp only [Equiv.Perm.one_apply, Finsupp.single_apply]
      rw [ite_eq_right]
      intro heq
      have houter : q j = Fin.castLEOrderEmb hpn i :=
        congrArg (fun x ↦ (ofLex x).1) heq
      by_cases hji : j < i
      · rw [hprev j hji] at houter
        exact (ne_of_lt hji) ((Fin.castLEOrderEmb hpn).injective houter)
      · exact (ne_of_gt (hiq.trans_le (q.monotone (le_of_not_gt hji)))) houter
    have hActualB : blockPermutationExponent q b 1
        (toLex (Fin.castLEOrderEmb hpn i, a i)) = 0 := by
      rw [blockPermutationExponent, finsupp_fintype_sum_apply]
      apply Finset.sum_eq_zero
      intro j hj
      simp only [Equiv.Perm.one_apply, Finsupp.single_apply]
      rw [ite_eq_right]
      intro heq
      have houter : q j = Fin.castLEOrderEmb hpn i :=
        congrArg (fun x ↦ (ofLex x).1) heq
      by_cases hji : j < i
      · rw [hprev j hji] at houter
        exact (ne_of_lt hji) ((Fin.castLEOrderEmb hpn).injective houter)
      · exact (ne_of_gt (hiq.trans_le (q.monotone (le_of_not_gt hji)))) houter
    have hInitialA : blockPermutationExponent (Fin.castLEOrderEmb hpn) a 1
        (toLex (Fin.castLEOrderEmb hpn i, a i)) = 1 := by
      simpa using blockPermutationExponent_apply_own
        (Fin.castLEOrderEmb hpn) a (1 : Equiv.Perm (Fin p)) i
    have hInitialB : blockPermutationExponent (Fin.castLEOrderEmb hpn) b 1
        (toLex (Fin.castLEOrderEmb hpn i, a i)) = 0 := by
      rw [blockPermutationExponent, finsupp_fintype_sum_apply]
      apply Finset.sum_eq_zero
      intro j hj
      simp only [Equiv.Perm.one_apply, Finsupp.single_apply]
      rw [ite_eq_right]
      intro heq
      have houter : Fin.castLEOrderEmb hpn j = Fin.castLEOrderEmb hpn i :=
        congrArg (fun x ↦ (ofLex x).1) heq
      have hji : j = i := (Fin.castLEOrderEmb hpn).injective houter
      subst j
      have hinner : b i = a i := congrArg (fun x ↦ (ofLex x).2) heq
      exact (ne_of_gt (hab i)) hinner
    rw [hActualA, hActualB, hInitialA, hInitialB]
    norm_num

/-- The increasing inner-row embedding attached to a finite-subset minor. -/
@[expose] def FinsetMinorIndex.rowInnerOrderEmbedding {n m : ℕ}
    (d : FinsetMinorIndex n m) : Fin d.rows.card ↪o (Fin n ⊕ₗ Fin m) where
  toFun i := toLex (Sum.inl (d.rows.orderEmbOfFin rfl i))
  inj' := by
    intro i j hij
    have hsum := toLex.injective hij
    have hrow := Sum.inl_injective hsum
    exact (d.rows.orderEmbOfFin rfl).injective hrow
  map_rel_iff' := by
    intro i j
    change toLex (Sum.inl (d.rows.orderEmbOfFin rfl i) : Fin n ⊕ Fin m) ≤
      toLex (Sum.inl (d.rows.orderEmbOfFin rfl j) : Fin n ⊕ Fin m) ↔ i ≤ j
    simpa only [Sum.Lex.inl_le_inl_iff] using
      (d.rows.orderEmbOfFin rfl).le_iff_le

/-- The increasing inner-column embedding attached to a finite-subset minor. -/
@[expose] def FinsetMinorIndex.colInnerOrderEmbedding {n m : ℕ}
    (d : FinsetMinorIndex n m) : Fin d.cols.card ↪o (Fin n ⊕ₗ Fin m) where
  toFun i := toLex (Sum.inr (d.cols.orderEmbOfFin rfl i))
  inj' := by
    intro i j hij
    have hsum := toLex.injective hij
    have hcol := Sum.inr_injective hsum
    exact (d.cols.orderEmbOfFin rfl).injective hcol
  map_rel_iff' := by
    intro i j
    change toLex (Sum.inr (d.cols.orderEmbOfFin rfl i) : Fin n ⊕ Fin m) ≤
      toLex (Sum.inr (d.cols.orderEmbOfFin rfl j) : Fin n ⊕ Fin m) ↔ i ≤ j
    simpa only [Sum.Lex.inr_le_inr_iff] using
      (d.cols.orderEmbOfFin rfl).le_iff_le

/-- Column variables indexed using the row cardinality of the minor. -/
@[expose] def FinsetMinorIndex.colInnerFromRowsOrderEmbedding {n m : ℕ}
    (d : FinsetMinorIndex n m) :
    Fin d.rows.card ↪o (Fin n ⊕ₗ Fin m) where
  toFun i := toLex (Sum.inr (d.cols.orderEmbOfFin d.card_eq.symm i))
  inj' := by
    intro i j hij
    have hsum := toLex.injective hij
    have hcol := Sum.inr_injective hsum
    exact (d.cols.orderEmbOfFin d.card_eq.symm).injective hcol
  map_rel_iff' := by
    intro i j
    change toLex (Sum.inr
        (d.cols.orderEmbOfFin d.card_eq.symm i) : Fin n ⊕ Fin m) ≤
      toLex (Sum.inr
        (d.cols.orderEmbOfFin d.card_eq.symm j) : Fin n ⊕ Fin m) ↔ i ≤ j
    simpa only [Sum.Lex.inr_le_inr_iff] using
      (d.cols.orderEmbOfFin d.card_eq.symm).le_iff_le

lemma FinsetMinorIndex.rowInnerOrderEmbedding_lt_colInnerFromRowsOrderEmbedding
    {n m : ℕ} (d : FinsetMinorIndex n m) (i : Fin d.rows.card) :
    d.rowInnerOrderEmbedding i < d.colInnerFromRowsOrderEmbedding i := by
  exact Sum.Lex.inl_lt_inr _ _

lemma FinsetMinorIndex.rowInnerOrderEmbedding_lt_colInnerOrderEmbedding
    {n m : ℕ} (d : FinsetMinorIndex n m) (i : Fin d.rows.card) :
    d.rowInnerOrderEmbedding i <
      d.colInnerOrderEmbedding (Fin.cast d.card_eq i) := by
  exact Sum.Lex.inl_lt_inr _ _

/-- The order embedding of the initial inner-index set
`{0, ..., rows.card - 1}`. -/
@[expose] def FinsetMinorIndex.initialInnerOrderEmbedding {n m : ℕ}
    (d : FinsetMinorIndex n m) : Fin d.rows.card ↪o Fin n :=
  Fin.castLEOrderEmb (by simpa using Finset.card_le_univ d.rows)

lemma FinsetMinorIndex.twoBlockDiagonalExponent_lt_initial
    {n m : ℕ} (d : FinsetMinorIndex n m)
    (q : Fin d.rows.card ↪o Fin n)
    (hq : q ≠ d.initialInnerOrderEmbedding) :
    twoBlockDiagonalExponent q d.rowInnerOrderEmbedding
        ((Fin.castOrderIso d.card_eq).toOrderEmbedding.comp
          d.colInnerOrderEmbedding) ≺[MonomialOrder.lex]
      twoBlockDiagonalExponent d.initialInnerOrderEmbedding
        d.rowInnerOrderEmbedding
        ((Fin.castOrderIso d.card_eq).toOrderEmbedding.comp
          d.colInnerOrderEmbedding) := by
  let hpn : d.rows.card ≤ n := by
    simpa using Finset.card_le_univ d.rows
  have hq' : q ≠ Fin.castLEOrderEmb hpn := by
    simpa [FinsetMinorIndex.initialInnerOrderEmbedding] using hq
  exact GenericMaximalMinor.twoBlockDiagonalExponent_lt_initial
    (p := d.rows.card) (n := n) (m := m) hpn q
    d.rowInnerOrderEmbedding
    ((Fin.castOrderIso d.card_eq).toOrderEmbedding.comp
      d.colInnerOrderEmbedding)
    (fun i ↦ d.rowInnerOrderEmbedding_lt_colInnerOrderEmbedding i) hq'

/-- Increasing enumeration of the image of an injective finite function. -/
def injectionRangeOrderEmbedding {p n : ℕ} (f : Fin p → Fin n)
    (hf : Function.Injective f) : Fin p ↪o Fin n :=
  (Finset.univ.image f).orderEmbOfFin (by
    rw [Finset.card_image_of_injective _ hf]
    simp)

lemma injectionRangeOrderEmbedding_range {p n : ℕ} (f : Fin p → Fin n)
    (hf : Function.Injective f) :
    Set.range (injectionRangeOrderEmbedding f hf) = Set.range f := by
  rw [injectionRangeOrderEmbedding, Finset.range_orderEmbOfFin]
  ext x
  simp

lemma exists_injectionRangeOrderEmbedding_eq {p n : ℕ}
    (f : Fin p → Fin n) (hf : Function.Injective f) (i : Fin p) :
    ∃ j, injectionRangeOrderEmbedding f hf j = f i := by
  have hi : f i ∈ Set.range (injectionRangeOrderEmbedding f hf) := by
    rw [injectionRangeOrderEmbedding_range f hf]
    exact ⟨i, rfl⟩
  exact hi

/-- The index of `f i` in the increasing enumeration of the image of `f`. -/
def injectionSortingIndex {p n : ℕ} (f : Fin p → Fin n)
    (hf : Function.Injective f) (i : Fin p) : Fin p :=
  Classical.choose (exists_injectionRangeOrderEmbedding_eq f hf i)

@[simp] lemma injectionRangeOrderEmbedding_sortingIndex {p n : ℕ}
    (f : Fin p → Fin n) (hf : Function.Injective f) (i : Fin p) :
    injectionRangeOrderEmbedding f hf (injectionSortingIndex f hf i) = f i :=
  Classical.choose_spec (exists_injectionRangeOrderEmbedding_eq f hf i)

lemma injectionSortingIndex_injective {p n : ℕ} (f : Fin p → Fin n)
    (hf : Function.Injective f) : Function.Injective (injectionSortingIndex f hf) := by
  intro i j hij
  apply hf
  rw [← injectionRangeOrderEmbedding_sortingIndex f hf i,
    ← injectionRangeOrderEmbedding_sortingIndex f hf j, hij]

/-- Permutation which records how an injective function differs from the
increasing enumeration of its image. -/
def injectionSortingPerm {p n : ℕ} (f : Fin p → Fin n)
    (hf : Function.Injective f) : Equiv.Perm (Fin p) :=
  Equiv.ofBijective (injectionSortingIndex f hf)
    ⟨injectionSortingIndex_injective f hf,
      Finite.injective_iff_surjective.mp
        (injectionSortingIndex_injective f hf)⟩

@[simp] lemma injectionRangeOrderEmbedding_sortingPerm {p n : ℕ}
    (f : Fin p → Fin n) (hf : Function.Injective f) (i : Fin p) :
    injectionRangeOrderEmbedding f hf (injectionSortingPerm f hf i) = f i := by
  exact injectionRangeOrderEmbedding_sortingIndex f hf i

@[simp] lemma injectionRangeOrderEmbedding_of_orderEmbedding {p n : ℕ}
    (q : Fin p ↪o Fin n) :
    injectionRangeOrderEmbedding q q.injective = q := by
  rw [injectionRangeOrderEmbedding]
  symm
  apply Finset.orderEmbOfFin_unique'
  intro i
  simp

@[simp] lemma injectionSortingPerm_of_orderEmbedding {p n : ℕ}
    (q : Fin p ↪o Fin n) :
    injectionSortingPerm q q.injective = 1 := by
  apply Equiv.ext
  intro i
  apply q.injective
  have hi := injectionRangeOrderEmbedding_sortingPerm
    (q : Fin p → Fin n) q.injective i
  simpa using hi

/-- Generic block matrix whose diagonal term is controlled by
`blockPermutationExponent`. -/
def blockGenericMatrix {D : Type*} [CommRing D] {p n m : ℕ}
    (q : Fin p ↪o Fin n) (a : Fin p ↪o (Fin n ⊕ₗ Fin m)) :
    Matrix (Fin p) (Fin p) (StandardAuxPoly D n m) :=
  fun i j ↦ MvPolynomial.X (toLex (q j, a i))

/-- Sorting the rows selected by an injective function changes the
corresponding block determinant only by the sign of the sorting
permutation. -/
lemma det_injectiveRows_eq_sign_mul_blockGenericMatrix
    {D : Type*} [CommRing D] {p n m : ℕ}
    (f : Fin p → Fin n) (hf : Function.Injective f)
    (a : Fin p ↪o (Fin n ⊕ₗ Fin m)) :
    Matrix.det (fun i j : Fin p ↦
        (MvPolynomial.X (toLex (f i, a j)) : StandardAuxPoly D n m)) =
      (((injectionSortingPerm f hf).sign : ℤ) : StandardAuxPoly D n m) *
        Matrix.det (blockGenericMatrix (D := D)
          (injectionRangeOrderEmbedding f hf) a) := by
  let q := injectionRangeOrderEmbedding f hf
  let u := injectionSortingPerm f hf
  let A : Matrix (Fin p) (Fin p) (StandardAuxPoly D n m) :=
    Matrix.of (fun i j ↦ MvPolynomial.X (toLex (f i, a j)))
  let B : Matrix (Fin p) (Fin p) (StandardAuxPoly D n m) :=
    blockGenericMatrix (D := D) q a
  have htranspose : A.transpose = B.submatrix id u := by
    ext i j
    simp only [A, B, Matrix.of_apply, Matrix.transpose_apply, Matrix.submatrix_apply,
      Function.id_def, blockGenericMatrix, q, u]
    rw [injectionRangeOrderEmbedding_sortingPerm]
  calc
    Matrix.det (fun i j : Fin p ↦
        (MvPolynomial.X (toLex (f i, a j)) : StandardAuxPoly D n m)) =
        Matrix.det A := rfl
    _ = Matrix.det A.transpose := (Matrix.det_transpose A).symm
    _ = Matrix.det (B.submatrix id u) := congrArg Matrix.det htranspose
    _ = (((u.sign : ℤ) : StandardAuxPoly D n m) * Matrix.det B) :=
      Matrix.det_permute' u B
    _ = _ := rfl

lemma blockGenericMatrix_det_term
    {D : Type*} [CommRing D] {p n m : ℕ}
    (q : Fin p ↪o Fin n) (a : Fin p ↪o (Fin n ⊕ₗ Fin m))
    (u : Equiv.Perm (Fin p)) :
    (((u.sign : ℤ) : StandardAuxPoly D n m) *
        ∏ j, blockGenericMatrix (D := D) q a (u j) j) =
      MvPolynomial.monomial (blockPermutationExponent q a u)
        ((u.sign : ℤ) : D) := by
  classical
  have hmono := MvPolynomial.monomial_sum_index
    (R := D) (Finset.univ : Finset (Fin p))
    (fun j ↦ Finsupp.single (toLex (q j, a (u j))) 1)
    ((u.sign : ℤ) : D)
  symm
  rw [blockPermutationExponent]
  calc
    MvPolynomial.monomial
        (∑ j, Finsupp.single (toLex (q j, a (u j))) 1)
        ((u.sign : ℤ) : D) =
        MvPolynomial.C ((u.sign : ℤ) : D) *
          ∏ j, MvPolynomial.monomial
            (Finsupp.single (toLex (q j, a (u j))) 1) 1 := hmono
    _ = (((u.sign : ℤ) : StandardAuxPoly D n m) *
        ∏ j, blockGenericMatrix (D := D) q a (u j) j) := by
      simp [blockGenericMatrix, MvPolynomial.X]

/-- In a generic block determinant, the diagonal monomial is the unique
largest monomial for lexicographic order, and its coefficient is one. -/
lemma blockGenericMatrix_det_degree_monic
    {D : Type*} [CommRing D] [Nontrivial D] {p n m : ℕ} (hp : 0 < p)
    (q : Fin p ↪o Fin n) (a : Fin p ↪o (Fin n ⊕ₗ Fin m)) :
    (MonomialOrder.lex : MonomialOrder (StandardAuxVar n m)).degree
        (Matrix.det (blockGenericMatrix (D := D) q a)) =
          blockPermutationExponent q a 1 ∧
      (MonomialOrder.lex : MonomialOrder (StandardAuxVar n m)).Monic
        (Matrix.det (blockGenericMatrix (D := D) q a)) := by
  classical
  let term : Equiv.Perm (Fin p) → StandardAuxPoly D n m := fun u ↦
    ((u.sign : ℤ) : StandardAuxPoly D n m) *
      ∏ j, blockGenericMatrix (D := D) q a (u j) j
  have hterm (u : Equiv.Perm (Fin p)) :
      term u = MvPolynomial.monomial (blockPermutationExponent q a u)
        ((u.sign : ℤ) : D) :=
    blockGenericMatrix_det_term q a u
  have hid : term 1 =
      MvPolynomial.monomial (blockPermutationExponent q a 1) 1 := by
    rw [hterm]
    simp
  have he_ne : blockPermutationExponent q a 1 ≠ 0 := by
    let i : Fin p := ⟨0, hp⟩
    intro he
    have hvalue := blockPermutationExponent_apply_own q a
      (1 : Equiv.Perm (Fin p)) i
    rw [he] at hvalue
    simp at hvalue
  have he_pos :
      (0 : (MonomialOrder.lex : MonomialOrder
        (StandardAuxVar n m)).syn) <
        (MonomialOrder.lex : MonomialOrder
          (StandardAuxVar n m)).toSyn (blockPermutationExponent q a 1) := by
    rw [MonomialOrder.toSyn_lt_iff_ne_zero]
    intro he
    exact he_ne ((MonomialOrder.toSyn_eq_zero_iff
      (MonomialOrder.lex : MonomialOrder (StandardAuxVar n m))
      (blockPermutationExponent q a 1)).mp he)
  have hdet : Matrix.det (blockGenericMatrix (D := D) q a) =
      term 1 + ∑ u ∈ (Finset.univ.erase
        (1 : Equiv.Perm (Fin p))), term u := by
    rw [Matrix.det_apply']
    exact (Finset.add_sum_erase Finset.univ term
      (Finset.mem_univ (1 : Equiv.Perm (Fin p)))).symm
  have hrest :
      (MonomialOrder.lex : MonomialOrder
          (StandardAuxVar n m)).toSyn
          ((MonomialOrder.lex : MonomialOrder
            (StandardAuxVar n m)).degree
            (∑ u ∈ (Finset.univ.erase
              (1 : Equiv.Perm (Fin p))), term u)) <
        (MonomialOrder.lex : MonomialOrder
          (StandardAuxVar n m)).toSyn (blockPermutationExponent q a 1) := by
    refine lt_of_le_of_lt MonomialOrder.degree_sum_le ?_
    rw [Finset.sup_lt_iff he_pos]
    intro u hu
    rw [hterm, MonomialOrder.degree_monomial]
    have hsign : ((u.sign : ℤ) : D) ≠ 0 := by
      rcases Int.units_eq_one_or u.sign with hs | hs <;> simp [hs]
    rw [ite_eq_right hsign]
    exact blockPermutationExponent_lt_identity q a u
      (Finset.mem_erase.mp hu).1
  have hdiagDegree :
      (MonomialOrder.lex : MonomialOrder
          (StandardAuxVar n m)).degree
          (MvPolynomial.monomial (blockPermutationExponent q a 1) (1 : D)) =
        blockPermutationExponent q a 1 := by
    simp [MonomialOrder.degree_monomial]
  rw [hdet, hid]
  constructor
  · calc
      (MonomialOrder.lex : MonomialOrder
          (StandardAuxVar n m)).degree
          (MvPolynomial.monomial (blockPermutationExponent q a 1) (1 : D) +
            ∑ u ∈ (Finset.univ.erase
              (1 : Equiv.Perm (Fin p))), term u) =
          (MonomialOrder.lex : MonomialOrder
            (StandardAuxVar n m)).degree
            (MvPolynomial.monomial
              (blockPermutationExponent q a 1) (1 : D)) := by
            apply (MonomialOrder.lex : MonomialOrder
              (StandardAuxVar n m)).degree_add_of_lt
            simpa only [hdiagDegree] using hrest
      _ = blockPermutationExponent q a 1 := hdiagDegree
  · apply MonomialOrder.Monic.add_of_lt
      (m := (MonomialOrder.lex : MonomialOrder (StandardAuxVar n m)))
      MonomialOrder.monic_monomial_one
    simpa only [hdiagDegree] using hrest

/-- The product of two generic block determinants has the sum of their
diagonal exponents as degree and is monic. -/
lemma blockGenericMatrix_det_mul_degree_monic
    {D : Type*} [CommRing D] [Nontrivial D] {p n m : ℕ} (hp : 0 < p)
    (q : Fin p ↪o Fin n)
    (a b : Fin p ↪o (Fin n ⊕ₗ Fin m)) :
    (MonomialOrder.lex : MonomialOrder (StandardAuxVar n m)).degree
        (Matrix.det (blockGenericMatrix (D := D) q a) *
          Matrix.det (blockGenericMatrix (D := D) q b)) =
          twoBlockDiagonalExponent q a b ∧
      (MonomialOrder.lex : MonomialOrder (StandardAuxVar n m)).Monic
        (Matrix.det (blockGenericMatrix (D := D) q a) *
          Matrix.det (blockGenericMatrix (D := D) q b)) := by
  have ha := blockGenericMatrix_det_degree_monic (D := D) hp q a
  have hb := blockGenericMatrix_det_degree_monic (D := D) hp q b
  constructor
  · rw [(MonomialOrder.lex : MonomialOrder
      (StandardAuxVar n m)).degree_mul_of_mul_leadingCoeff_ne_zero]
    · exact congrArg₂ (· + ·) ha.1 hb.1
    · rw [ha.2.leadingCoeff_eq_one, hb.2.leadingCoeff_eq_one]
      simp
  · exact ha.2.mul hb.2

/-- Exponent vector of the diagonal monomial attached to a list of minors.
The first summand records `Y` variables and the second records `Z` variables. -/
@[expose] def standardDiagonalCode {n m : ℕ}
    (l : List (FinsetMinorIndex n m)) : StandardAuxVar n m →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun qc ↦
    match ofLex (ofLex qc).2 with
    | Sum.inl a => Multiset.count a (minorRowProfile l (ofLex qc).1.val)
    | Sum.inr b => Multiset.count b (minorColProfile l (ofLex qc).1.val)

@[simp] lemma standardDiagonalCode_row_apply {n m : ℕ}
    (l : List (FinsetMinorIndex n m)) (q : Fin n) (a : Fin n) :
    standardDiagonalCode l (standardAuxYVar q a) =
      Multiset.count a (minorRowProfile l q.val) := by
  simp [standardDiagonalCode, standardAuxYVar]

@[simp] lemma standardDiagonalCode_col_apply {n m : ℕ}
    (l : List (FinsetMinorIndex n m)) (q : Fin n) (b : Fin m) :
    standardDiagonalCode l (standardAuxZVar q b) =
      Multiset.count b (minorColProfile l q.val) := by
  simp [standardDiagonalCode, standardAuxZVar]

lemma initialTwoBlockDiagonalExponent_row_apply_of_lt {n m : ℕ}
    (d : FinsetMinorIndex n m) (q : Fin n) (a : Fin n)
    (hq : q.val < d.rows.card) :
    twoBlockDiagonalExponent d.initialInnerOrderEmbedding
        d.rowInnerOrderEmbedding d.colInnerFromRowsOrderEmbedding
        (standardAuxYVar q a) =
      if d.rows.orderEmbOfFin rfl ⟨q.val, hq⟩ = a then 1 else 0 := by
  let i : Fin d.rows.card := ⟨q.val, hq⟩
  have hqi : d.initialInnerOrderEmbedding i = q := by
    apply Fin.ext
    rfl
  change twoBlockDiagonalExponent d.initialInnerOrderEmbedding
      d.rowInnerOrderEmbedding d.colInnerFromRowsOrderEmbedding
      (toLex (q, toLex (Sum.inl a))) =
        if d.rows.orderEmbOfFin rfl i = a then 1 else 0
  rw [← hqi, twoBlockDiagonalExponent, Finsupp.add_apply,
    blockPermutationExponent_apply_same_outer,
    blockPermutationExponent_apply_same_outer]
  simp [FinsetMinorIndex.rowInnerOrderEmbedding,
    FinsetMinorIndex.colInnerFromRowsOrderEmbedding, i]

lemma initialTwoBlockDiagonalExponent_row_apply_of_ge {n m : ℕ}
    (d : FinsetMinorIndex n m) (q : Fin n) (a : Fin n)
    (hq : d.rows.card ≤ q.val) :
    twoBlockDiagonalExponent d.initialInnerOrderEmbedding
        d.rowInnerOrderEmbedding d.colInnerFromRowsOrderEmbedding
        (standardAuxYVar q a) = 0 := by
  have houter : ∀ i, d.initialInnerOrderEmbedding i ≠ q := by
    intro i hi
    have hval : i.val = q.val := congrArg Fin.val hi
    exact (not_lt_of_ge hq) (hval ▸ i.isLt)
  change twoBlockDiagonalExponent d.initialInnerOrderEmbedding
      d.rowInnerOrderEmbedding d.colInnerFromRowsOrderEmbedding
      (toLex (q, toLex (Sum.inl a))) = 0
  rw [twoBlockDiagonalExponent, Finsupp.add_apply,
    blockPermutationExponent_apply_of_outer_ne _ _ _ _ houter,
    blockPermutationExponent_apply_of_outer_ne _ _ _ _ houter,
    add_zero]

lemma initialTwoBlockDiagonalExponent_col_apply_of_lt {n m : ℕ}
    (d : FinsetMinorIndex n m) (q : Fin n) (b : Fin m)
    (hq : q.val < d.rows.card) :
    twoBlockDiagonalExponent d.initialInnerOrderEmbedding
        d.rowInnerOrderEmbedding d.colInnerFromRowsOrderEmbedding
        (standardAuxZVar q b) =
      if d.cols.orderEmbOfFin d.card_eq.symm ⟨q.val, hq⟩ = b then 1 else 0 := by
  let i : Fin d.rows.card := ⟨q.val, hq⟩
  have hqi : d.initialInnerOrderEmbedding i = q := by
    apply Fin.ext
    rfl
  change twoBlockDiagonalExponent d.initialInnerOrderEmbedding
      d.rowInnerOrderEmbedding d.colInnerFromRowsOrderEmbedding
      (toLex (q, toLex (Sum.inr b))) =
        if d.cols.orderEmbOfFin d.card_eq.symm i = b then 1 else 0
  rw [← hqi, twoBlockDiagonalExponent, Finsupp.add_apply,
    blockPermutationExponent_apply_same_outer,
    blockPermutationExponent_apply_same_outer]
  simp [FinsetMinorIndex.rowInnerOrderEmbedding,
    FinsetMinorIndex.colInnerFromRowsOrderEmbedding, i]

lemma initialTwoBlockDiagonalExponent_col_apply_of_ge {n m : ℕ}
    (d : FinsetMinorIndex n m) (q : Fin n) (b : Fin m)
    (hq : d.rows.card ≤ q.val) :
    twoBlockDiagonalExponent d.initialInnerOrderEmbedding
        d.rowInnerOrderEmbedding d.colInnerFromRowsOrderEmbedding
        (standardAuxZVar q b) = 0 := by
  have houter : ∀ i, d.initialInnerOrderEmbedding i ≠ q := by
    intro i hi
    have hval : i.val = q.val := congrArg Fin.val hi
    exact (not_lt_of_ge hq) (hval ▸ i.isLt)
  change twoBlockDiagonalExponent d.initialInnerOrderEmbedding
      d.rowInnerOrderEmbedding d.colInnerFromRowsOrderEmbedding
      (toLex (q, toLex (Sum.inr b))) = 0
  rw [twoBlockDiagonalExponent, Finsupp.add_apply,
    blockPermutationExponent_apply_of_outer_ne _ _ _ _ houter,
    blockPermutationExponent_apply_of_outer_ne _ _ _ _ houter,
    add_zero]

lemma standardDiagonalCode_singleton_row_apply_of_lt {n m : ℕ}
    (d : FinsetMinorIndex n m) (q : Fin n) (a : Fin n)
    (hq : q.val < d.rows.card) :
    standardDiagonalCode [d] (standardAuxYVar q a) =
      if d.rows.orderEmbOfFin rfl ⟨q.val, hq⟩ = a then 1 else 0 := by
  rw [standardDiagonalCode_row_apply]
  change Multiset.count a (minorRowColumn [d] q.val : Multiset (Fin n)) = _
  rw [minorRowColumn]
  simp only [List.filterMap_cons, List.filterMap_nil]
  rw [d.rowAt?_eq_some q.val hq]
  by_cases ha : d.rows.orderEmbOfFin rfl ⟨q.val, hq⟩ = a
  · simp [ha]
  · have ha' : a ≠ d.rows.orderEmbOfFin rfl ⟨q.val, hq⟩ := by
      exact fun h ↦ ha h.symm
    simp [ha, ha']

lemma standardDiagonalCode_singleton_row_apply_of_ge {n m : ℕ}
    (d : FinsetMinorIndex n m) (q : Fin n) (a : Fin n)
    (hq : d.rows.card ≤ q.val) :
    standardDiagonalCode [d] (standardAuxYVar q a) = 0 := by
  rw [standardDiagonalCode_row_apply]
  simp [minorRowProfile, minorRowColumn, FinsetMinorIndex.rowAt?, hq]

lemma standardDiagonalCode_singleton_col_apply_of_lt {n m : ℕ}
    (d : FinsetMinorIndex n m) (q : Fin n) (b : Fin m)
    (hq : q.val < d.rows.card) :
    standardDiagonalCode [d] (standardAuxZVar q b) =
      if d.cols.orderEmbOfFin d.card_eq.symm ⟨q.val, hq⟩ = b then 1 else 0 := by
  have hqc : q.val < d.cols.card := by
    rwa [← d.card_eq]
  rw [standardDiagonalCode_col_apply]
  change Multiset.count b (minorColColumn [d] q.val : Multiset (Fin m)) = _
  rw [minorColColumn]
  simp only [List.filterMap_cons, List.filterMap_nil]
  rw [d.colAt?_eq_some q.val hqc]
  have hvalue : d.cols.orderEmbOfFin rfl ⟨q.val, hqc⟩ =
      d.cols.orderEmbOfFin d.card_eq.symm ⟨q.val, hq⟩ := by
    rw [Finset.orderEmbOfFin_eq_orderEmbOfFin_iff]
  by_cases hb : d.cols.orderEmbOfFin d.card_eq.symm ⟨q.val, hq⟩ = b
  · rw [hvalue, hb]
    simp
  · have hb' : b ≠ d.cols.orderEmbOfFin rfl ⟨q.val, hqc⟩ := by
      intro h
      apply hb
      rw [← hvalue]
      exact h.symm
    simp [hb, hb']

lemma standardDiagonalCode_singleton_col_apply_of_ge {n m : ℕ}
    (d : FinsetMinorIndex n m) (q : Fin n) (b : Fin m)
    (hq : d.rows.card ≤ q.val) :
    standardDiagonalCode [d] (standardAuxZVar q b) = 0 := by
  have hqc : d.cols.card ≤ q.val := by
    rwa [← d.card_eq]
  rw [standardDiagonalCode_col_apply]
  simp [minorColProfile, minorColColumn, FinsetMinorIndex.colAt?, hqc]

/-- The initial diagonal exponent computed from the two auxiliary
determinants is exactly the profile code of the singleton minor list. -/
lemma initialTwoBlockDiagonalExponent_eq_standardDiagonalCode_singleton
    {n m : ℕ} (d : FinsetMinorIndex n m) :
    twoBlockDiagonalExponent d.initialInnerOrderEmbedding
        d.rowInnerOrderEmbedding d.colInnerFromRowsOrderEmbedding =
      standardDiagonalCode [d] := by
  apply Finsupp.ext
  intro qc
  let q : Fin n := (ofLex qc).1
  cases hinner : ofLex (ofLex qc).2 with
  | inl a =>
      have hqc : qc = standardAuxYVar q a := by
        calc
          qc = toLex (ofLex qc) := by simp
          _ = toLex (q, toLex (Sum.inl a)) := by
            apply congrArg (fun x : Fin n × (Fin n ⊕ₗ Fin m) ↦ toLex x)
            apply Prod.ext
            · rfl
            · apply toLex.injective
              exact hinner
      rw [hqc]
      by_cases hqrow : q.val < d.rows.card
      · rw [initialTwoBlockDiagonalExponent_row_apply_of_lt d q a hqrow,
          standardDiagonalCode_singleton_row_apply_of_lt d q a hqrow]
      · have hqrow' : d.rows.card ≤ q.val := Nat.le_of_not_gt hqrow
        rw [initialTwoBlockDiagonalExponent_row_apply_of_ge d q a hqrow',
          standardDiagonalCode_singleton_row_apply_of_ge d q a hqrow']
  | inr b =>
      have hqc : qc = standardAuxZVar q b := by
        calc
          qc = toLex (ofLex qc) := by simp
          _ = toLex (q, toLex (Sum.inr b)) := by
            apply congrArg (fun x : Fin n × (Fin n ⊕ₗ Fin m) ↦ toLex x)
            apply Prod.ext
            · rfl
            · apply toLex.injective
              exact hinner
      rw [hqc]
      by_cases hqrow : q.val < d.rows.card
      · rw [initialTwoBlockDiagonalExponent_col_apply_of_lt d q b hqrow,
          standardDiagonalCode_singleton_col_apply_of_lt d q b hqrow]
      · have hqrow' : d.rows.card ≤ q.val := Nat.le_of_not_gt hqrow
        rw [initialTwoBlockDiagonalExponent_col_apply_of_ge d q b hqrow',
          standardDiagonalCode_singleton_col_apply_of_ge d q b hqrow']

lemma standardDiagonalCode_cons {n m : ℕ} (d : FinsetMinorIndex n m)
    (l : List (FinsetMinorIndex n m)) :
    standardDiagonalCode (d :: l) =
      standardDiagonalCode [d] + standardDiagonalCode l := by
  apply Finsupp.ext
  intro qc
  cases hinner : ofLex (ofLex qc).2 with
  | inl a =>
      simp only [standardDiagonalCode, minorRowProfile, minorRowColumn, Multiset.coe_count,
        minorColProfile, minorColColumn, Finsupp.equivFunOnFinite_symm_apply_apply,
        hinner, Finsupp.coe_add, Finsupp.coe_equivFunOnFinite_symm, Pi.add_apply]
      cases hopt : d.rowAt? (ofLex qc).1.val with
      | none => simp [hopt]
      | some x =>
          by_cases hx : x = a <;> simp [hopt, hx, Nat.add_comm]
  | inr b =>
      simp only [standardDiagonalCode, minorRowProfile, minorRowColumn, Multiset.coe_count,
        minorColProfile, minorColColumn, Finsupp.equivFunOnFinite_symm_apply_apply,
        hinner, Finsupp.coe_add, Finsupp.coe_equivFunOnFinite_symm, Pi.add_apply]
      cases hopt : d.colAt? (ofLex qc).1.val with
      | none => simp [hopt]
      | some x =>
          by_cases hx : x = b <;> simp [hopt, hx, Nat.add_comm]

@[simp] lemma standardDiagonalCode_nil {n m : ℕ} :
    standardDiagonalCode ([] : List (FinsetMinorIndex n m)) = 0 := by
  apply Finsupp.ext
  intro qc
  cases hinner : ofLex (ofLex qc).2 <;>
    simp [standardDiagonalCode, minorRowProfile, minorRowColumn,
      minorColProfile, minorColColumn, hinner]

lemma minorRowColumn_eq_nil_of_n_le {n m : ℕ}
    (l : List (FinsetMinorIndex n m)) {q : ℕ} (hq : n ≤ q) :
    minorRowColumn l q = [] := by
  rw [minorRowColumn, List.filterMap_eq_nil_iff]
  intro d hd
  have hcard : d.rows.card ≤ n := by
    simpa using Finset.card_le_univ d.rows
  exact d.rowAt?_eq_none q (hcard.trans hq)

lemma minorColColumn_eq_nil_of_n_le {n m : ℕ}
    (l : List (FinsetMinorIndex n m)) {q : ℕ} (hq : n ≤ q) :
    minorColColumn l q = [] := by
  rw [minorColColumn, List.filterMap_eq_nil_iff]
  intro d hd
  apply d.colAt?_eq_none q
  calc
    d.cols.card = d.rows.card := d.card_eq.symm
    _ ≤ n := by simpa using Finset.card_le_univ d.rows
    _ ≤ q := hq

lemma rowProfile_eq_of_standardDiagonalCode_eq {n m : ℕ}
    {l₁ l₂ : List (FinsetMinorIndex n m)}
    (hcode : standardDiagonalCode l₁ = standardDiagonalCode l₂) :
    minorRowProfile l₁ = minorRowProfile l₂ := by
  funext q
  apply Multiset.ext.mpr
  intro a
  by_cases hq : q < n
  · let qn : Fin n := ⟨q, hq⟩
    have h := congrArg (fun c ↦ c (standardAuxYVar qn a)) hcode
    simpa using h
  · have hnq : n ≤ q := Nat.le_of_not_gt hq
    change Multiset.count a (minorRowColumn l₁ q : Multiset (Fin n)) =
      Multiset.count a (minorRowColumn l₂ q : Multiset (Fin n))
    rw [minorRowColumn_eq_nil_of_n_le l₁ hnq,
      minorRowColumn_eq_nil_of_n_le l₂ hnq]

lemma colProfile_eq_of_standardDiagonalCode_eq {n m : ℕ}
    {l₁ l₂ : List (FinsetMinorIndex n m)}
    (hcode : standardDiagonalCode l₁ = standardDiagonalCode l₂) :
    minorColProfile l₁ = minorColProfile l₂ := by
  funext q
  apply Multiset.ext.mpr
  intro b
  by_cases hq : q < n
  · let qn : Fin n := ⟨q, hq⟩
    have h := congrArg (fun c ↦ c (standardAuxZVar qn b)) hcode
    simpa using h
  · have hnq : n ≤ q := Nat.le_of_not_gt hq
    change Multiset.count b (minorColColumn l₁ q : Multiset (Fin m)) =
      Multiset.count b (minorColColumn l₂ q : Multiset (Fin m))
    rw [minorColColumn_eq_nil_of_n_le l₁ hnq,
      minorColColumn_eq_nil_of_n_le l₂ hnq]

/-- The diagonal exponent code is injective on standard products of nonempty
minors.  This is the recovery lemma used in the leading-term proof. -/
theorem standardDiagonalCode_injective_on_standard {n m : ℕ}
    {l₁ l₂ : List (FinsetMinorIndex n m)}
    (hl₁ : IsStandardMinorList l₁) (hl₂ : IsStandardMinorList l₂)
    (hne₁ : HasNoEmptyMinors l₁) (hne₂ : HasNoEmptyMinors l₂)
    (hcode : standardDiagonalCode l₁ = standardDiagonalCode l₂) :
    l₁ = l₂ :=
  eq_of_standard_minor_profiles hl₁ hl₂ hne₁ hne₂
    (rowProfile_eq_of_standardDiagonalCode_eq hcode)
    (colProfile_eq_of_standardDiagonalCode_eq hcode)

/-! ## The `X ↦ YZ` substitution -/

/-- The auxiliary polynomial variable for the first matrix factor. -/
@[expose] def auxY {D : Type*} [CommSemiring D] {n m : ℕ}
    (i q : Fin n) : StandardAuxPoly D n m :=
  MvPolynomial.X (standardAuxYVar q i)

/-- The auxiliary polynomial variable for the second matrix factor. -/
@[expose] def auxZ {D : Type*} [CommSemiring D] {n m : ℕ}
    (q : Fin n) (j : Fin m) : StandardAuxPoly D n m :=
  MvPolynomial.X (standardAuxZVar q j)

/-- Entry of the product of the auxiliary generic matrices `Y` and `Z`. -/
@[expose] def auxYZEntry {D : Type*} [CommSemiring D] {n m : ℕ}
    (i : Fin n) (j : Fin m) : StandardAuxPoly D n m :=
  ∑ q : Fin n, auxY (D := D) i q * auxZ (D := D) q j

/-- The coefficient-preserving substitution from the generic matrix `X` to
the product of the auxiliary matrices `Y Z`. -/
@[expose] def standardYZHom (D : Type*) [CommSemiring D] (n m : ℕ) :
    GenericPoly D n m →ₐ[D] StandardAuxPoly D n m :=
  MvPolynomial.bind₁ fun ij ↦ auxYZEntry (D := D) ij.1 ij.2

@[simp] lemma standardYZHom_X {D : Type*} [CommSemiring D] {n m : ℕ}
    (i : Fin n) (j : Fin m) :
    standardYZHom D n m (MvPolynomial.X (i, j)) =
      auxYZEntry (D := D) i j := by
  simp [standardYZHom]

lemma standardYZHom_minorPoly
    {D : Type*} [CommRing D] {n m : ℕ} (d : MinorIndex n m) :
    standardYZHom D n m (minorPoly d) =
      Matrix.det (fun a b : Fin d.size.val ↦
        auxYZEntry (D := D) (d.rows a) (d.cols b)) := by
  let N : Matrix (Fin d.size.val) (Fin d.size.val)
      (StandardAuxPoly D n m) :=
    fun a b ↦ auxYZEntry (D := D) (d.rows a) (d.cols b)
  change standardYZHom D n m (Matrix.det (minorMatrix d)) = Matrix.det N
  calc
    standardYZHom D n m (Matrix.det (minorMatrix d)) =
        Matrix.det ((standardYZHom D n m).toRingHom.mapMatrix
          (minorMatrix d)) :=
      (standardYZHom D n m).toRingHom.map_det (minorMatrix d)
    _ = Matrix.det N := by
      congr 1
      ext a b
      simp [N, minorMatrix]

/-- Under `X ↦ YZ`, a finite-set minor becomes the determinant of the
corresponding submatrix of `YZ`. -/
lemma standardYZHom_finsetMinorIndex_poly
    {D : Type*} [CommRing D] {n m : ℕ} (d : FinsetMinorIndex n m) :
    standardYZHom D n m d.poly =
      Matrix.det (fun a b : Fin d.rows.card ↦
        auxYZEntry (D := D)
          (d.rows.orderEmbOfFin rfl a)
          (d.cols.orderEmbOfFin d.card_eq.symm b)) := by
  unfold FinsetMinorIndex.poly
  rw [finsetMinorPoly_of_card_eq (hcard := d.card_eq)]
  rw [standardYZHom_minorPoly]
  rfl

/-- Row-multilinear expansion of the preceding determinant.  Terms are
indexed by all choices of an inner index; noninjective choices will vanish by
alternation in the next stage of the leading-term proof. -/
lemma standardYZHom_finsetMinorIndex_poly_expansion
    {D : Type*} [CommRing D] {n m : ℕ} (d : FinsetMinorIndex n m) :
    standardYZHom D n m d.poly =
      ∑ f : Fin d.rows.card → Fin n,
        (∏ i, auxY (D := D) (d.rows.orderEmbOfFin rfl i) (f i)) *
          Matrix.det (fun i j : Fin d.rows.card ↦
            auxZ (D := D) (f i)
              (d.cols.orderEmbOfFin d.card_eq.symm j)) := by
  rw [standardYZHom_finsetMinorIndex_poly]
  let y : Fin d.rows.card → Fin n → StandardAuxPoly D n m :=
    fun i q ↦ auxY (D := D) (d.rows.orderEmbOfFin rfl i) q
  let zrow : Fin n → Fin d.rows.card → StandardAuxPoly D n m :=
    fun q j ↦ auxZ (D := D) q
      (d.cols.orderEmbOfFin d.card_eq.symm j)
  change Matrix.det (fun i j ↦ ∑ q, y i q * zrow q j) = _
  change Matrix.detRowAlternating
      (fun i j ↦ ∑ q, y i q * zrow q j) = _
  calc
    Matrix.detRowAlternating (fun i j ↦ ∑ q, y i q * zrow q j) =
        ∑ f : Fin d.rows.card → Fin n,
          Matrix.detRowAlternating (fun i j ↦ y i (f i) * zrow (f i) j) := by
      have hmap := Matrix.detRowAlternating.toMultilinearMap.map_sum
        (g := fun i q j ↦ y i q * zrow q j)
      have hrows :
          (fun i j ↦ ∑ q, y i q * zrow q j) =
            (fun i ↦ ∑ q, (fun j ↦ y i q * zrow q j)) := by
        funext i j
        simp
      rw [hrows]
      exact hmap
    _ = ∑ f : Fin d.rows.card → Fin n,
        (∏ i, y i (f i)) * Matrix.det (fun i j ↦ zrow (f i) j) := by
      apply Finset.sum_congr rfl
      intro f hf
      change Matrix.detRowAlternating
          (fun i ↦ y i (f i) • zrow (f i)) = _
      rw [Matrix.detRowAlternating.map_smul_univ]
      rfl
    _ = _ := by rfl

lemma prod_X_eq_monomial_fintype
    {D : Type*} [CommSemiring D] {ι σ : Type*} [Fintype ι]
    (x : ι → σ) :
    (∏ i, MvPolynomial.X (x i) : MvPolynomial σ D) =
      MvPolynomial.monomial (∑ i, Finsupp.single (x i) 1) 1 := by
  classical
  symm
  have h := MvPolynomial.monomial_sum_index
    (R := D) (Finset.univ : Finset ι)
    (fun i ↦ Finsupp.single (x i) 1) (1 : D)
  simpa [MvPolynomial.X] using h

/-- The product of `X` variables selected by an injective function has the
permutation exponent obtained by sorting the image of that function. -/
lemma prod_X_injective_eq_monomial
    {D : Type*} [CommSemiring D] {p n m : ℕ}
    (f : Fin p → Fin n) (hf : Function.Injective f)
    (a : Fin p ↪o (Fin n ⊕ₗ Fin m)) :
    (∏ i, MvPolynomial.X (toLex (f i, a i)) : StandardAuxPoly D n m) =
      MvPolynomial.monomial
        (blockPermutationExponent (injectionRangeOrderEmbedding f hf) a
          (injectionSortingPerm f hf).symm) 1 := by
  classical
  let q := injectionRangeOrderEmbedding f hf
  let u := injectionSortingPerm f hf
  calc
    (∏ i, MvPolynomial.X (toLex (f i, a i)) : StandardAuxPoly D n m) =
        ∏ i, MvPolynomial.X (toLex (q (u i), a i)) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [injectionRangeOrderEmbedding_sortingPerm]
    _ = ∏ j, MvPolynomial.X (toLex (q j, a (u.symm j))) := by
      simpa only [u.symm_apply_apply] using
        (Equiv.prod_comp u (fun j ↦
          (MvPolynomial.X (toLex (q j, a (u.symm j))) :
            StandardAuxPoly D n m)))
    _ = MvPolynomial.monomial
        (blockPermutationExponent q a u.symm) 1 := by
      rw [blockPermutationExponent]
      exact prod_X_eq_monomial_fintype
        (D := D) (fun j ↦ toLex (q j, a (u.symm j)))
    _ = _ := rfl

lemma prod_auxY_injective_eq_monomial
    {D : Type*} [CommSemiring D] {n m : ℕ}
    (d : FinsetMinorIndex n m) (f : Fin d.rows.card → Fin n)
    (hf : Function.Injective f) :
    (∏ i, auxY (D := D) (d.rows.orderEmbOfFin rfl i) (f i)) =
      MvPolynomial.monomial
        (blockPermutationExponent (injectionRangeOrderEmbedding f hf)
          d.rowInnerOrderEmbedding (injectionSortingPerm f hf).symm) 1 := by
  simpa [auxY, standardAuxYVar,
    FinsetMinorIndex.rowInnerOrderEmbedding] using
    (prod_X_injective_eq_monomial (D := D) f hf
      d.rowInnerOrderEmbedding)

lemma det_auxZ_injective_eq_sign_mul_blockGenericMatrix
    {D : Type*} [CommRing D] {n m : ℕ}
    (d : FinsetMinorIndex n m) (f : Fin d.rows.card → Fin n)
    (hf : Function.Injective f) :
    Matrix.det (fun i j : Fin d.rows.card ↦
        auxZ (D := D) (f i)
          (d.cols.orderEmbOfFin d.card_eq.symm j)) =
      (((injectionSortingPerm f hf).sign : ℤ) : StandardAuxPoly D n m) *
        Matrix.det (blockGenericMatrix (D := D)
          (injectionRangeOrderEmbedding f hf)
          d.colInnerFromRowsOrderEmbedding) := by
  simpa [auxZ, standardAuxZVar,
    FinsetMinorIndex.colInnerFromRowsOrderEmbedding] using
    (det_injectiveRows_eq_sign_mul_blockGenericMatrix
      (D := D) f hf d.colInnerFromRowsOrderEmbedding)

/-- The summand indexed by an inner-index choice in the multilinear
expansion of a minor after `X ↦ YZ`. -/
def minorExpansionTerm
    (D : Type*) [CommRing D] {n m : ℕ} (d : FinsetMinorIndex n m)
    (f : Fin d.rows.card → Fin n) : StandardAuxPoly D n m :=
  (∏ i, auxY (D := D) (d.rows.orderEmbOfFin rfl i) (f i)) *
    Matrix.det (fun i j : Fin d.rows.card ↦
      auxZ (D := D) (f i)
        (d.cols.orderEmbOfFin d.card_eq.symm j))

/-- Exact leading exponent of an injective summand.  Sorting the chosen
inner indices produces the first determinant exponent; the second determinant
uses the increasing enumeration of the same image. -/
lemma minorExpansionTerm_degree_of_injective
    {D : Type*} [CommRing D] [Nontrivial D] {n m : ℕ}
    (d : FinsetMinorIndex n m) (hd : 0 < d.rows.card)
    (f : Fin d.rows.card → Fin n) (hf : Function.Injective f) :
    (MonomialOrder.lex : MonomialOrder (StandardAuxVar n m)).degree
        (minorExpansionTerm D d f) =
      blockPermutationExponent (injectionRangeOrderEmbedding f hf)
          d.rowInnerOrderEmbedding (injectionSortingPerm f hf).symm +
        blockPermutationExponent (injectionRangeOrderEmbedding f hf)
          d.colInnerFromRowsOrderEmbedding 1 := by
  classical
  let q := injectionRangeOrderEmbedding f hf
  let u := injectionSortingPerm f hf
  let a := d.rowInnerOrderEmbedding
  let b := d.colInnerFromRowsOrderEmbedding
  have hy := prod_auxY_injective_eq_monomial (D := D) d f hf
  have hz := det_auxZ_injective_eq_sign_mul_blockGenericMatrix
    (D := D) d f hf
  have hb := blockGenericMatrix_det_degree_monic
    (D := D) hd q b
  have hscaledDegree :
      (MonomialOrder.lex : MonomialOrder (StandardAuxVar n m)).degree
          ((((u.sign : ℤ) : StandardAuxPoly D n m) *
            Matrix.det (blockGenericMatrix (D := D) q b))) =
        blockPermutationExponent q b 1 := by
    rcases Int.units_eq_one_or u.sign with hs | hs
    · simp [hs, hb.1]
    · simp [hs, hb.1]
  have hscaledLeadingCoeff :
      (MonomialOrder.lex : MonomialOrder (StandardAuxVar n m)).leadingCoeff
          ((((u.sign : ℤ) : StandardAuxPoly D n m) *
            Matrix.det (blockGenericMatrix (D := D) q b))) ≠ 0 := by
    rcases Int.units_eq_one_or u.sign with hs | hs
    · simp [hs, hb.2.leadingCoeff_eq_one]
    · simp [hs, hb.2.leadingCoeff_eq_one]
  rw [minorExpansionTerm, hy, hz]
  rw [(MonomialOrder.lex : MonomialOrder
    (StandardAuxVar n m)).degree_mul_of_mul_leadingCoeff_ne_zero]
  · rw [MonomialOrder.degree_monomial, ite_eq_right one_ne_zero,
      hscaledDegree]
  · rw [MonomialOrder.monic_monomial_one.leadingCoeff_eq_one, one_mul]
    exact hscaledLeadingCoeff

/-- Every injective summand other than the initial increasing choice has
strictly smaller degree than the initial diagonal exponent. -/
lemma minorExpansionTerm_degree_lt_initial_of_ne
    {D : Type*} [CommRing D] [Nontrivial D] {n m : ℕ}
    (d : FinsetMinorIndex n m) (hd : 0 < d.rows.card)
    (f : Fin d.rows.card → Fin n) (hf : Function.Injective f)
    (hne : f ≠ d.initialInnerOrderEmbedding) :
    (MonomialOrder.lex : MonomialOrder (StandardAuxVar n m)).degree
        (minorExpansionTerm D d f) ≺[MonomialOrder.lex]
      twoBlockDiagonalExponent d.initialInnerOrderEmbedding
        d.rowInnerOrderEmbedding d.colInnerFromRowsOrderEmbedding := by
  let q := injectionRangeOrderEmbedding f hf
  let u := injectionSortingPerm f hf
  have hdegree := minorExpansionTerm_degree_of_injective
    (D := D) d hd f hf
  rw [hdegree]
  have hperm (hu : u.symm ≠ 1) :
      blockPermutationExponent q d.rowInnerOrderEmbedding u.symm +
          blockPermutationExponent q d.colInnerFromRowsOrderEmbedding 1 ≺[MonomialOrder.lex]
        twoBlockDiagonalExponent q d.rowInnerOrderEmbedding
          d.colInnerFromRowsOrderEmbedding := by
    have h := add_lt_add_right
      (blockPermutationExponent_lt_identity q
        d.rowInnerOrderEmbedding u.symm hu)
      ((MonomialOrder.lex : MonomialOrder (StandardAuxVar n m)).toSyn
        (blockPermutationExponent q d.colInnerFromRowsOrderEmbedding 1))
    simpa [twoBlockDiagonalExponent] using h
  by_cases hq : q = d.initialInnerOrderEmbedding
  · have hu : u.symm ≠ 1 := by
      intro hu
      have huone : u = 1 := by
        apply Equiv.ext
        intro i
        have hi := DFunLike.congr_fun hu (u i)
        simpa using hi.symm
      apply hne
      funext i
      calc
        f i = q (u i) :=
          (injectionRangeOrderEmbedding_sortingPerm f hf i).symm
        _ = d.initialInnerOrderEmbedding i := by rw [hq, huone]; rfl
    simpa [q, u, hq] using hperm hu
  · have hqdiag :
        twoBlockDiagonalExponent q d.rowInnerOrderEmbedding
            d.colInnerFromRowsOrderEmbedding ≺[MonomialOrder.lex]
          twoBlockDiagonalExponent d.initialInnerOrderEmbedding
            d.rowInnerOrderEmbedding d.colInnerFromRowsOrderEmbedding := by
      exact GenericMaximalMinor.twoBlockDiagonalExponent_lt_initial
        (p := d.rows.card) (n := n) (m := m)
        (by simpa using Finset.card_le_univ d.rows) q
        d.rowInnerOrderEmbedding d.colInnerFromRowsOrderEmbedding
        (fun i ↦ d.rowInnerOrderEmbedding_lt_colInnerFromRowsOrderEmbedding i)
        (by simpa [q, FinsetMinorIndex.initialInnerOrderEmbedding] using hq)
    by_cases hu : u.symm = 1
    · simpa [q, u, twoBlockDiagonalExponent, hu] using hqdiag
    · simpa [q, u] using lt_trans (hperm hu) hqdiag

lemma minorExpansionTerm_initial_eq
    {D : Type*} [CommRing D] {n m : ℕ} (d : FinsetMinorIndex n m) :
    minorExpansionTerm D d d.initialInnerOrderEmbedding =
      MvPolynomial.monomial
          (blockPermutationExponent d.initialInnerOrderEmbedding
            d.rowInnerOrderEmbedding 1) 1 *
        Matrix.det (blockGenericMatrix (D := D)
          d.initialInnerOrderEmbedding d.colInnerFromRowsOrderEmbedding) := by
  have hy := prod_auxY_injective_eq_monomial (D := D) d
    d.initialInnerOrderEmbedding d.initialInnerOrderEmbedding.injective
  have hz := det_auxZ_injective_eq_sign_mul_blockGenericMatrix
    (D := D) d d.initialInnerOrderEmbedding
      d.initialInnerOrderEmbedding.injective
  rw [minorExpansionTerm, hy, hz]
  simp only [injectionRangeOrderEmbedding_of_orderEmbedding,
    injectionSortingPerm_of_orderEmbedding, Equiv.Perm.sign_one, Units.val_one,
    Int.cast_one, one_mul]
  have hone : (1 : Equiv.Perm (Fin d.rows.card)).symm = 1 := by
    ext i
    rfl
  rw [hone]

/-- The initial summand is monic and has exactly the initial diagonal
exponent. -/
lemma minorExpansionTerm_initial_degree_monic
    {D : Type*} [CommRing D] [Nontrivial D] {n m : ℕ}
    (d : FinsetMinorIndex n m) (hd : 0 < d.rows.card) :
    (MonomialOrder.lex : MonomialOrder (StandardAuxVar n m)).degree
        (minorExpansionTerm D d d.initialInnerOrderEmbedding) =
      twoBlockDiagonalExponent d.initialInnerOrderEmbedding
        d.rowInnerOrderEmbedding d.colInnerFromRowsOrderEmbedding ∧
    (MonomialOrder.lex : MonomialOrder (StandardAuxVar n m)).Monic
        (minorExpansionTerm D d d.initialInnerOrderEmbedding) := by
  have hdegree := minorExpansionTerm_degree_of_injective
    (D := D) d hd d.initialInnerOrderEmbedding
      d.initialInnerOrderEmbedding.injective
  have hb := blockGenericMatrix_det_degree_monic (D := D) hd
    d.initialInnerOrderEmbedding d.colInnerFromRowsOrderEmbedding
  constructor
  · have hone : (1 : Equiv.Perm (Fin d.rows.card)).symm = 1 := by
      ext i
      rfl
    simp only [injectionRangeOrderEmbedding_of_orderEmbedding,
      injectionSortingPerm_of_orderEmbedding] at hdegree
    rw [hone] at hdegree
    simpa only [twoBlockDiagonalExponent] using hdegree
  · rw [minorExpansionTerm_initial_eq]
    exact MonomialOrder.monic_monomial_one.mul hb.2

lemma auxZ_det_eq_zero_of_not_injective
    {D : Type*} [CommRing D] {n m p : ℕ}
    (f : Fin p → Fin n) (c : Fin p → Fin m)
    (hf : ¬Function.Injective f) :
    Matrix.det (fun i j ↦ auxZ (D := D) (f i) (c j)) = 0 := by
  obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hf
  apply Matrix.det_zero_of_row_eq hne
  funext k
  rw [hij]

/-- The row expansion may be restricted to injective choices of inner
indices; every noninjective choice repeats a row of the `Z` determinant. -/
lemma standardYZHom_finsetMinorIndex_poly_injective_expansion
    {D : Type*} [CommRing D] {n m : ℕ} (d : FinsetMinorIndex n m) :
    standardYZHom D n m d.poly =
      ∑ f ∈ (Finset.univ.filter fun f : Fin d.rows.card → Fin n ↦
          Function.Injective f),
        (∏ i, auxY (D := D) (d.rows.orderEmbOfFin rfl i) (f i)) *
          Matrix.det (fun i j : Fin d.rows.card ↦
            auxZ (D := D) (f i)
              (d.cols.orderEmbOfFin d.card_eq.symm j)) := by
  rw [standardYZHom_finsetMinorIndex_poly_expansion]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro f hf hnotmem
  have hinj : ¬Function.Injective f := by
    intro hinj
    exact hnotmem (Finset.mem_filter.mpr ⟨hf, hinj⟩)
  have hz : Matrix.det (fun i j : Fin d.rows.card ↦
      auxZ (D := D) (f i)
        (d.cols.orderEmbOfFin d.card_eq.symm j)) = 0 :=
    auxZ_det_eq_zero_of_not_injective f
      (d.cols.orderEmbOfFin d.card_eq.symm) hinj
  rw [hz, mul_zero]

/-- A nonempty minor has the expected initial diagonal exponent after the
`X ↦ YZ` substitution, with leading coefficient one. -/
lemma standardYZHom_finsetMinorIndex_poly_degree_monic_of_nonempty
    {D : Type*} [CommRing D] [Nontrivial D] {n m : ℕ}
    (d : FinsetMinorIndex n m) (hd : 0 < d.rows.card) :
    (MonomialOrder.lex : MonomialOrder (StandardAuxVar n m)).degree
        (standardYZHom D n m d.poly) =
      twoBlockDiagonalExponent d.initialInnerOrderEmbedding
        d.rowInnerOrderEmbedding d.colInnerFromRowsOrderEmbedding ∧
    (MonomialOrder.lex : MonomialOrder (StandardAuxVar n m)).Monic
        (standardYZHom D n m d.poly) := by
  classical
  let q₀ := d.initialInnerOrderEmbedding
  let s : Finset (Fin d.rows.card → Fin n) :=
    Finset.univ.filter Function.Injective
  let principal := minorExpansionTerm D d q₀
  let rest := ∑ f ∈ s.erase q₀, minorExpansionTerm D d f
  have hq₀mem : (q₀ : Fin d.rows.card → Fin n) ∈ s := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, q₀.injective⟩
  have hexpansion : standardYZHom D n m d.poly =
      ∑ f ∈ s, minorExpansionTerm D d f := by
    simpa [s, minorExpansionTerm] using
      (standardYZHom_finsetMinorIndex_poly_injective_expansion
        (D := D) d)
  have hdecomp : standardYZHom D n m d.poly = principal + rest := by
    rw [hexpansion]
    exact (Finset.add_sum_erase s (minorExpansionTerm D d) hq₀mem).symm
  have hprincipal := minorExpansionTerm_initial_degree_monic
    (D := D) d hd
  have hcode_ne : twoBlockDiagonalExponent q₀
      d.rowInnerOrderEmbedding d.colInnerFromRowsOrderEmbedding ≠ 0 := by
    let i : Fin d.rows.card := ⟨0, hd⟩
    intro he
    have happ := congrArg (fun e ↦
      e (toLex (q₀ i, d.rowInnerOrderEmbedding i))) he
    have hrow : blockPermutationExponent q₀ d.rowInnerOrderEmbedding 1
        (toLex (q₀ i, d.rowInnerOrderEmbedding i)) = 1 := by
      simpa using blockPermutationExponent_apply_own q₀
        d.rowInnerOrderEmbedding (1 : Equiv.Perm (Fin d.rows.card)) i
    rw [twoBlockDiagonalExponent, Finsupp.add_apply, hrow] at happ
    simp at happ
  have hcode_pos :
      (0 : (MonomialOrder.lex : MonomialOrder
        (StandardAuxVar n m)).syn) <
      (MonomialOrder.lex : MonomialOrder (StandardAuxVar n m)).toSyn
        (twoBlockDiagonalExponent q₀ d.rowInnerOrderEmbedding
          d.colInnerFromRowsOrderEmbedding) := by
    rw [MonomialOrder.toSyn_lt_iff_ne_zero]
    intro he
    exact hcode_ne ((MonomialOrder.toSyn_eq_zero_iff
      (MonomialOrder.lex : MonomialOrder (StandardAuxVar n m))
      (twoBlockDiagonalExponent q₀ d.rowInnerOrderEmbedding
        d.colInnerFromRowsOrderEmbedding)).mp he)
  have hrest :
      (MonomialOrder.lex : MonomialOrder (StandardAuxVar n m)).degree rest ≺[MonomialOrder.lex]
      twoBlockDiagonalExponent q₀ d.rowInnerOrderEmbedding
        d.colInnerFromRowsOrderEmbedding := by
    refine lt_of_le_of_lt MonomialOrder.degree_sum_le ?_
    rw [Finset.sup_lt_iff hcode_pos]
    intro f hfmem
    have hfmem' : f ∈ s := (Finset.mem_erase.mp hfmem).2
    have hf : Function.Injective f := (Finset.mem_filter.mp hfmem').2
    have hfne : f ≠ q₀ := (Finset.mem_erase.mp hfmem).1
    simpa [q₀] using
      (minorExpansionTerm_degree_lt_initial_of_ne
        (D := D) d hd f hf hfne)
  rw [hdecomp]
  constructor
  · calc
      (MonomialOrder.lex : MonomialOrder
          (StandardAuxVar n m)).degree (principal + rest) =
          (MonomialOrder.lex : MonomialOrder
            (StandardAuxVar n m)).degree principal := by
            apply (MonomialOrder.lex : MonomialOrder
              (StandardAuxVar n m)).degree_add_of_lt
            simpa [principal, q₀, hprincipal.1] using hrest
      _ = twoBlockDiagonalExponent d.initialInnerOrderEmbedding
          d.rowInnerOrderEmbedding d.colInnerFromRowsOrderEmbedding := by
        simpa [principal, q₀] using hprincipal.1
  · apply MonomialOrder.Monic.add_of_lt
      (m := (MonomialOrder.lex : MonomialOrder (StandardAuxVar n m)))
    · simpa [principal, q₀] using hprincipal.2
    · simpa [principal, q₀, hprincipal.1] using hrest

/-- Paper-facing single-minor leading-term theorem, expressed using the
profile code employed by the recovery argument. -/
lemma standardYZHom_finsetMinorIndex_poly_degree_code_monic
    {D : Type*} [CommRing D] [Nontrivial D] {n m : ℕ}
    (d : FinsetMinorIndex n m) (hd : 0 < d.rows.card) :
    (MonomialOrder.lex : MonomialOrder (StandardAuxVar n m)).degree
        (standardYZHom D n m d.poly) = standardDiagonalCode [d] ∧
    (MonomialOrder.lex : MonomialOrder (StandardAuxVar n m)).Monic
        (standardYZHom D n m d.poly) := by
  have h := standardYZHom_finsetMinorIndex_poly_degree_monic_of_nonempty
    (D := D) d hd
  constructor
  · exact h.1.trans
      (initialTwoBlockDiagonalExponent_eq_standardDiagonalCode_singleton d)
  · exact h.2

/-- Every product of nonempty minors becomes a monic polynomial with degree
equal to its full diagonal profile code after `X ↦ YZ`. -/
theorem standardYZHom_minorListPoly_degree_code_monic
    {D : Type*} [CommRing D] [Nontrivial D] {n m : ℕ}
    (l : List (FinsetMinorIndex n m)) (hne : HasNoEmptyMinors l) :
    (MonomialOrder.lex : MonomialOrder (StandardAuxVar n m)).degree
        (standardYZHom D n m (minorListPoly (D := D) l)) =
          standardDiagonalCode l ∧
    (MonomialOrder.lex : MonomialOrder (StandardAuxVar n m)).Monic
        (standardYZHom D n m (minorListPoly (D := D) l)) := by
  induction l with
  | nil =>
      simp [MonomialOrder.Monic, MonomialOrder.leadingCoeff]
  | cons d l ih =>
      have hd : 0 < d.rows.card :=
        Finset.card_pos.mpr (hne d (by simp))
      have htail : HasNoEmptyMinors l := by
        intro e he
        exact hne e (by simp [he])
      have hsingle :=
        standardYZHom_finsetMinorIndex_poly_degree_code_monic
          (D := D) d hd
      have hrest := ih htail
      rw [minorListPoly_cons, map_mul]
      constructor
      · rw [(MonomialOrder.lex : MonomialOrder
          (StandardAuxVar n m)).degree_mul_of_mul_leadingCoeff_ne_zero]
        · rw [hsingle.1, hrest.1]
          exact (standardDiagonalCode_cons d l).symm
        · rw [hsingle.2.leadingCoeff_eq_one,
            hrest.2.leadingCoeff_eq_one]
          simp
      · exact hsingle.2.mul hrest.2

/-! ## Linear independence of standard products -/

/-- A family of multivariate polynomials with pairwise distinct monic leading
monomials is linearly independent over its coefficient ring. -/
lemma monic_family_linearIndependent_of_degree_injective
    {D σ ι : Type*} [CommRing D]
    (m : MonomialOrder σ) (p : ι → MvPolynomial σ D)
    (hp : ∀ i, m.Monic (p i))
    (hdeg : Function.Injective (fun i ↦ m.degree (p i))) :
    LinearIndependent D p := by
  classical
  rw [linearIndependent_iff']
  intro s g hrel i hi
  by_contra hgi
  let t := s.filter fun j ↦ g j ≠ 0
  have hit : i ∈ t := Finset.mem_filter.mpr ⟨hi, hgi⟩
  obtain ⟨k, hkt, hmax⟩ := Finset.exists_max_image t
    (fun j ↦ m.toSyn (m.degree (p j))) ⟨i, hit⟩
  have hks : k ∈ s := (Finset.mem_filter.mp hkt).1
  have hgk : g k ≠ 0 := (Finset.mem_filter.mp hkt).2
  have hcoeff := congrArg
    (fun q : MvPolynomial σ D ↦ q.coeff (m.degree (p k))) hrel
  have hsum : ∑ j ∈ s, g j * (p j).coeff (m.degree (p k)) = g k := by
    calc
      _ = g k * (p k).coeff (m.degree (p k)) := by
        apply Finset.sum_eq_single k
        · intro j hjs hjk
          by_cases hgj : g j = 0
          · simp [hgj]
          · have hjt : j ∈ t := Finset.mem_filter.mpr ⟨hjs, hgj⟩
            have hle := hmax j hjt
            have hdegree_ne : m.degree (p j) ≠ m.degree (p k) := by
              intro heq
              exact hjk (hdeg heq)
            have hsyn_ne : m.toSyn (m.degree (p j)) ≠
                m.toSyn (m.degree (p k)) := by
              intro heq
              exact hdegree_ne (m.toSyn.injective heq)
            have hltSyn : m.toSyn (m.degree (p j)) <
                m.toSyn (m.degree (p k)) := lt_of_le_of_ne hle hsyn_ne
            have hlt : m.degree (p j) ≺[m] m.degree (p k) := hltSyn
            rw [m.coeff_eq_zero_of_lt hlt, mul_zero]
        · intro hknot
          exact (hknot hks).elim
      _ = g k := by rw [(hp k).coeff_degree, mul_one]
  rw [MvPolynomial.coeff_sum] at hcoeff
  simp only [MvPolynomial.coeff_smul, smul_eq_mul,
    AddMonoidAlgebra.coeff_zero] at hcoeff
  rw [hsum] at hcoeff
  exact hgk hcoeff

/-- The canonical index type for standard minor products: empty minor
factors are omitted because they represent the unit.  The empty list itself
is retained and indexes the constant polynomial `1`. -/
@[expose] def StandardMinorProductIndex (n m : ℕ) :=
  {l : List (FinsetMinorIndex n m) //
    IsStandardMinorList l ∧ HasNoEmptyMinors l}

/-- Delete empty-minor factors from a product.  Such factors are equal to
`1`, so this is the canonical representative used by the basis index. -/
@[expose] def eraseEmptyMinors {n m : ℕ}
    (l : List (FinsetMinorIndex n m)) : List (FinsetMinorIndex n m) :=
  l.filter fun d ↦ d.rows.Nonempty

lemma isStandardMinorList_of_pairwise {n m : ℕ}
    {l : List (FinsetMinorIndex n m)}
    (hl : l.Pairwise (· ≼ᵢ ·)) : IsStandardMinorList l := by
  induction l with
  | nil => trivial
  | cons d l ih =>
      cases l with
      | nil => trivial
      | cons e l =>
          constructor
          · exact (List.pairwise_cons.mp hl).1 e (by simp)
          · exact ih (List.Pairwise.tail hl)

lemma eraseEmptyMinors_standard {n m : ℕ}
    {l : List (FinsetMinorIndex n m)} (hl : IsStandardMinorList l) :
    IsStandardMinorList (eraseEmptyMinors l) := by
  apply isStandardMinorList_of_pairwise
  exact (isStandardMinorList_pairwise hl).filter _

lemma eraseEmptyMinors_hasNoEmptyMinors {n m : ℕ}
    (l : List (FinsetMinorIndex n m)) :
    HasNoEmptyMinors (eraseEmptyMinors l) := by
  intro d hd
  simpa using (List.mem_filter.mp hd).2

lemma FinsetMinorIndex.poly_eq_one_of_not_nonempty
    {D : Type*} [CommRing D] {n m : ℕ}
    (d : FinsetMinorIndex n m) (hd : ¬d.rows.Nonempty) :
    d.poly = (1 : GenericPoly D n m) := by
  have hrows : d.rows = ∅ := Finset.not_nonempty_iff_eq_empty.mp hd
  have hcols : d.cols = ∅ := by
    apply Finset.card_eq_zero.mp
    rw [← d.card_eq, hrows]
    simp
  unfold FinsetMinorIndex.poly
  rw [hrows, hcols]
  unfold finsetMinorPoly
  rw [dite_eq_left (by simp)]
  unfold minorPoly
  exact Matrix.det_fin_zero

lemma minorListPoly_eraseEmptyMinors
    {D : Type*} [CommRing D] {n m : ℕ}
    (l : List (FinsetMinorIndex n m)) :
    minorListPoly (D := D) (eraseEmptyMinors l) =
      minorListPoly (D := D) l := by
  induction l with
  | nil => simp [eraseEmptyMinors]
  | cons d l ih =>
      have ih' :
          minorListPoly (D := D)
              (l.filter fun e ↦ e.rows.Nonempty) =
            minorListPoly (D := D) l := by
        simpa only [eraseEmptyMinors] using ih
      by_cases hd : d.rows.Nonempty
      · simp [eraseEmptyMinors, hd, ih']
      · have hdpoly := FinsetMinorIndex.poly_eq_one_of_not_nonempty
          (D := D) d hd
        simp [eraseEmptyMinors, hd, hdpoly, ih']

/-- After the `X ↦ YZ` substitution, standard products indexed without
empty minor factors form a linearly independent family. -/
theorem standardYZHom_standardMinorProducts_linearIndependent
    {D : Type*} [CommRing D] [Nontrivial D] {n m : ℕ} :
    LinearIndependent D
      (fun s : StandardMinorProductIndex n m ↦
        standardYZHom D n m (minorListPoly (D := D) s.1)) := by
  apply monic_family_linearIndependent_of_degree_injective
    (m := (MonomialOrder.lex : MonomialOrder (StandardAuxVar n m)))
  · intro s
    exact (standardYZHom_minorListPoly_degree_code_monic
      (D := D) s.1 s.2.2).2
  · intro s t hdegree
    have hs := standardYZHom_minorListPoly_degree_code_monic
      (D := D) s.1 s.2.2
    have ht := standardYZHom_minorListPoly_degree_code_monic
      (D := D) t.1 t.2.2
    apply Subtype.ext
    apply standardDiagonalCode_injective_on_standard
      s.2.1 t.2.1 s.2.2 t.2.2
    rw [← hs.1, ← ht.1]
    exact hdegree

/-- Standard products of nonempty minors are linearly independent in the
original generic polynomial ring. -/
theorem standardMinorProducts_linearIndependent
    {D : Type*} [CommRing D] [Nontrivial D] {n m : ℕ} :
    LinearIndependent D
      (fun s : StandardMinorProductIndex n m ↦
        minorListPoly (D := D) s.1) := by
  rw [linearIndependent_iff']
  intro s g hrel i hi
  have hmapped :=
    (standardYZHom_standardMinorProducts_linearIndependent
      (D := D) (n := n) (m := m))
  apply (linearIndependent_iff'.mp hmapped) s g ?_ i hi
  apply_fun standardYZHom D n m at hrel
  simpa only [map_sum, map_smul, map_zero] using hrel

/-- The indexed standard products span the full generic polynomial ring. -/
theorem standardMinorProducts_span_eq_top
    (D : Type*) [CommRing D] (n m : ℕ) :
    Submodule.span D
      (Set.range fun s : StandardMinorProductIndex n m ↦
        minorListPoly (D := D) s.1) = ⊤ := by
  apply top_unique
  rw [← standardMinorProductSubmodule_eq_top D n m]
  rw [standardMinorProductSubmodule, Submodule.span_le]
  rintro y ⟨l, hl, rfl⟩
  let s : StandardMinorProductIndex n m :=
    ⟨eraseEmptyMinors l, eraseEmptyMinors_standard hl,
      eraseEmptyMinors_hasNoEmptyMinors l⟩
  rw [← minorListPoly_eraseEmptyMinors (D := D) l]
  exact Submodule.subset_span (Set.mem_range_self s)

/-- The standard products of nonempty minors, including the empty product
`1`, form a basis of the generic polynomial ring. -/
@[expose] noncomputable def standardMinorProductBasis
    (D : Type*) [CommRing D] [Nontrivial D] (n m : ℕ) :
    Module.Basis (StandardMinorProductIndex n m) D (GenericPoly D n m) :=
  Module.Basis.mk (standardMinorProducts_linearIndependent
      (D := D) (n := n) (m := m)) (by
    rw [standardMinorProducts_span_eq_top D n m])

@[simp] lemma standardMinorProductBasis_apply
    {D : Type*} [CommRing D] [Nontrivial D] {n m : ℕ}
    (s : StandardMinorProductIndex n m) :
    standardMinorProductBasis D n m s = minorListPoly (D := D) s.1 := by
  exact Module.Basis.mk_apply _ _ s

end GenericMaximalMinor

end

end Cslib
