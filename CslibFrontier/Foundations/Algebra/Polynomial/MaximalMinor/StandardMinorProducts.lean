/-
Copyright (c) 2026 Yuqing Kong, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuqing Kong, Christian Reitwiessner
-/

module
-- upstream: candidate (Mathlib, generic maximal minors)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Algebra.Polynomial.MaximalMinor.RectangularMinorStraightening

/-!
# Standard products of minors

This file packages minors by their row and column sets and lifts the
two-minor straightening theorem to finite products.

Ported by Christian Reitwiessner from Yuqing Kong's Apache-2.0 formalization,
`StandardMinorProducts.lean` at commit
`4e27ef9d167be69902385307d40123ec665dc532` of
https://github.com/yuqkong-1844/finite-sample-information-monotones .
The mathematical source is [Kong2027]. This general algebra is intended for
Mathlib; its destination is recorded in the upstream marker above.
-/

public section

namespace Cslib

noncomputable section

open scoped BigOperators

namespace GenericMaximalMinor

/-- A minor represented by equally large row and column subsets. -/
structure FinsetMinorIndex (n m : ℕ) where
  /-- The selected row set. -/
  rows : Finset (Fin n)
  /-- The selected column set. -/
  cols : Finset (Fin m)
  card_eq : rows.card = cols.card

instance (n m : ℕ) : DecidableEq (FinsetMinorIndex n m) := Classical.decEq _

/-- Identify finite-subset minor indices with pairs of equal-sized column embeddings. -/
def finsetMinorIndexEquiv (n m : ℕ) :
    FinsetMinorIndex n m ≃
      {p : Finset (Fin n) × Finset (Fin m) // p.1.card = p.2.card} where
  toFun d := ⟨(d.rows, d.cols), d.card_eq⟩
  invFun p := ⟨p.1.1, p.1.2, p.2⟩
  left_inv := by intro d; cases d; rfl
  right_inv := by intro p; cases p; rfl

instance (n m : ℕ) : Fintype (FinsetMinorIndex n m) :=
  Fintype.ofEquiv
    {p : Finset (Fin n) × Finset (Fin m) // p.1.card = p.2.card}
    (finsetMinorIndexEquiv n m).symm

/-- The polynomial represented by a finite-set minor index. -/
@[expose] def FinsetMinorIndex.poly {D : Type*} [CommRing D] {n m : ℕ}
    (d : FinsetMinorIndex n m) : GenericPoly D n m :=
  finsetMinorPoly (D := D) d.rows d.cols

/-- Componentwise prefix order on finite-set minor indices. -/
@[expose] def FinsetMinorIndex.LE {n m : ℕ}
    (d e : FinsetMinorIndex n m) : Prop :=
  d.rows ≼ₚ e.rows ∧ d.cols ≼ₚ e.cols

/-- Notation for `FinsetMinorIndex.LE`. -/
scoped infix:50 " ≼ᵢ " => FinsetMinorIndex.LE

/-- Strict componentwise order: both coordinates weakly decrease and at least
one decreases strictly. -/
@[expose] def FinsetMinorIndex.LT {n m : ℕ}
    (d e : FinsetMinorIndex n m) : Prop := d ≼ᵢ e ∧ d ≠ e

/-- Notation for `FinsetMinorIndex.LT`. -/
scoped infix:50 " ≺ᵢ " => FinsetMinorIndex.LT

lemma finsetMinorIndex_le_refl {n m : ℕ} (d : FinsetMinorIndex n m) : d ≼ᵢ d :=
  ⟨prefixLE_refl _, prefixLE_refl _⟩

lemma finsetMinorIndex_le_trans {n m : ℕ} {d e f : FinsetMinorIndex n m}
    (hde : d ≼ᵢ e) (hef : e ≼ᵢ f) : d ≼ᵢ f :=
  ⟨prefixLE_trans hde.1 hef.1, prefixLE_trans hde.2 hef.2⟩

lemma finsetMinorIndex_ext {n m : ℕ} {d e : FinsetMinorIndex n m}
    (hrows : d.rows = e.rows) (hcols : d.cols = e.cols) : d = e := by
  cases d
  cases e
  simp_all

/-- Defect used for the inner straightening induction. -/
@[expose] def FinsetMinorIndex.defect {n m : ℕ} (d : FinsetMinorIndex n m) : ℕ :=
  prefixDefect d.rows + prefixDefect d.cols

lemma finsetMinorIndex_defect_lt_of_left_strict {n m : ℕ}
    {d e : FinsetMinorIndex n m}
    (hrow : d.rows ≺ₚ e.rows) (hcol : d.cols ≼ₚ e.cols) :
    d.defect < e.defect := by
  unfold FinsetMinorIndex.defect
  exact Nat.add_lt_add_of_lt_of_le
    (prefixDefect_lt_of_prefixLT hrow) (prefixDefect_le_of_prefixLE hcol)

lemma finsetMinorIndex_defect_lt_of_right_strict {n m : ℕ}
    {d e : FinsetMinorIndex n m}
    (hrow : d.rows ≼ₚ e.rows) (hcol : d.cols ≺ₚ e.cols) :
    d.defect < e.defect := by
  unfold FinsetMinorIndex.defect
  exact Nat.add_lt_add_of_le_of_lt
    (prefixDefect_le_of_prefixLE hrow) (prefixDefect_lt_of_prefixLT hcol)

lemma finsetMinorIndex_defect_lt_of_strict_coordinates {n m : ℕ}
    {d e : FinsetMinorIndex n m}
    (hrow : d.rows ≼ₚ e.rows) (hcol : d.cols ≼ₚ e.cols)
    (hstrict : d.rows ≺ₚ e.rows ∨ d.cols ≺ₚ e.cols) :
    d.defect < e.defect := by
  rcases hstrict with h | h
  · exact finsetMinorIndex_defect_lt_of_left_strict h hcol
  · exact finsetMinorIndex_defect_lt_of_right_strict hrow h

lemma finsetMinorIndex_defect_lt_of_LT {n m : ℕ}
    {d e : FinsetMinorIndex n m} (h : d ≺ᵢ e) :
    d.defect < e.defect := by
  apply finsetMinorIndex_defect_lt_of_strict_coordinates h.1.1 h.1.2
  by_cases hrows : d.rows = e.rows
  · right
    exact ⟨h.1.2, by
      intro hcols
      exact h.2 (finsetMinorIndex_ext hrows hcols)⟩
  · exact Or.inl ⟨h.1.1, hrows⟩

/-- A list is standard when consecutive minors are weakly increasing. -/
@[expose] def IsStandardMinorList {n m : ℕ} : List (FinsetMinorIndex n m) → Prop
  | [] => True
  | [_] => True
  | d :: e :: l => d ≼ᵢ e ∧ IsStandardMinorList (e :: l)

/-- Polynomial product represented by a list of minors. -/
@[expose] def minorListPoly {D : Type*} [CommRing D] {n m : ℕ} :
    List (FinsetMinorIndex n m) → GenericPoly D n m
  | [] => 1
  | d :: l => d.poly * minorListPoly l

@[simp] lemma minorListPoly_nil {D : Type*} [CommRing D] {n m : ℕ} :
    minorListPoly (D := D) ([] : List (FinsetMinorIndex n m)) = 1 := rfl

@[simp] lemma minorListPoly_cons {D : Type*} [CommRing D] {n m : ℕ}
    (d : FinsetMinorIndex n m) (l : List (FinsetMinorIndex n m)) :
    minorListPoly (D := D) (d :: l) = d.poly * minorListPoly l := rfl

/-- Integral span of standard products. -/
def standardMinorProductSpan {D : Type*} [CommRing D] (n m : ℕ) :
    AddSubgroup (GenericPoly D n m) :=
  AddSubgroup.closure
    {x | ∃ l : List (FinsetMinorIndex n m),
      IsStandardMinorList l ∧ x = minorListPoly (D := D) l}

/-- Standard products with a fixed number of minor factors. -/
@[expose] def standardMinorProductSpanOfLength {D : Type*} [CommRing D]
    (n m k : ℕ) : AddSubgroup (GenericPoly D n m) :=
  AddSubgroup.closure
    {x | ∃ l : List (FinsetMinorIndex n m),
      IsStandardMinorList l ∧ l.length = k ∧
        x = minorListPoly (D := D) l}

lemma standard_minorListPoly_mem_span {D : Type*} [CommRing D] {n m : ℕ}
    (l : List (FinsetMinorIndex n m)) (hl : IsStandardMinorList l) :
    minorListPoly (D := D) l ∈ standardMinorProductSpan (D := D) n m := by
  apply AddSubgroup.subset_closure
  exact ⟨l, hl, rfl⟩

lemma standard_minorListPoly_mem_spanOfLength
    {D : Type*} [CommRing D] {n m : ℕ}
    (l : List (FinsetMinorIndex n m)) (hl : IsStandardMinorList l) :
    minorListPoly (D := D) l ∈
      standardMinorProductSpanOfLength (D := D) n m l.length := by
  apply AddSubgroup.subset_closure
  exact ⟨l, hl, rfl, rfl⟩

lemma mul_left_mem_of_mem_closure {R : Type*} [CommRing R]
    (K : AddSubgroup R) (s : Set R) (c x : R)
    (hgen : ∀ y ∈ s, c * y ∈ K) (hx : x ∈ AddSubgroup.closure s) :
    c * x ∈ K := by
  induction hx using AddSubgroup.closure_induction with
  | mem y hy => exact hgen y hy
  | zero => simp
  | add x y _ _ hx hy => simpa [mul_add] using K.add_mem hx hy
  | neg x _ hx => simpa using K.neg_mem hx

lemma mul_right_mem_of_mem_closure {R : Type*} [CommRing R]
    (K : AddSubgroup R) (s : Set R) (c x : R)
    (hgen : ∀ y ∈ s, y * c ∈ K) (hx : x ∈ AddSubgroup.closure s) :
    x * c ∈ K := by
  induction hx using AddSubgroup.closure_induction with
  | mem y hy => exact hgen y hy
  | zero => simp
  | add x y _ _ hx hy => simpa [add_mul] using K.add_mem hx hy
  | neg x _ hx => simpa using K.neg_mem hx

/-- Allowed replacements of a nonstandard pair. -/
def pairReductionGenerators {D : Type*} [CommRing D] {n m : ℕ}
    (d : FinsetMinorIndex n m) : Set (GenericPoly D n m) :=
  {x | ∃ a b : FinsetMinorIndex n m,
    a ≺ᵢ d ∧ a ≼ᵢ b ∧ x = a.poly * b.poly}

/-- The additive span of smaller standard products in a two-minor reduction. -/
def pairReductionSpan {D : Type*} [CommRing D] {n m : ℕ}
    (d : FinsetMinorIndex n m) : AddSubgroup (GenericPoly D n m) :=
  AddSubgroup.closure (pairReductionGenerators (D := D) d)

lemma two_minor_mem_pairReductionSpan {D : Type*} [CommRing D] {n m : ℕ}
    (d e : FinsetMinorIndex n m) (hnot : ¬d ≼ᵢ e) :
    d.poly * e.poly ∈ pairReductionSpan (D := D) d := by
  have h := two_minor_straightening (D := D)
    d.rows e.rows d.cols e.cols d.card_eq e.card_eq hnot
  apply (AddSubgroup.closure_le _).mpr ?_ h
  intro x hx
  rcases hx with ⟨A, C, B, E, hAB, hCE, hAd, hBd,
    hAC, hBE, hstrict, -, rfl⟩
  let a : FinsetMinorIndex n m := ⟨A, B, hAB⟩
  let b : FinsetMinorIndex n m := ⟨C, E, hCE⟩
  apply AddSubgroup.subset_closure
  refine ⟨a, b, ?_, ⟨hAC, hBE⟩, rfl⟩
  refine ⟨⟨hAd, hBd⟩, ?_⟩
  intro hab
  have hrows : A = d.rows := congrArg FinsetMinorIndex.rows hab
  have hcols : B = d.cols := congrArg FinsetMinorIndex.cols hab
  rcases hstrict with hs | hs
  · exact hs.2 hrows
  · exact hs.2 hcols

/-- Every finite product of minors straightens into standard products with the
same number of factors. -/
theorem minorListPoly_mem_standardSpanOfLength
    {D : Type*} [CommRing D] {n m : ℕ}
    (l : List (FinsetMinorIndex n m)) :
    minorListPoly (D := D) l ∈
      standardMinorProductSpanOfLength (D := D) n m l.length := by
  classical
  generalize hk : l.length = k
  induction k using Nat.strong_induction_on generalizing l with
  | ind k outer =>
      cases l with
      | nil =>
          have hk0 : k = 0 := by simpa using hk.symm
          subst k
          exact standard_minorListPoly_mem_spanOfLength
            (D := D) (n := n) (m := m) [] trivial
      | cons d t =>
          have htlen : t.length < k := by
            simp only [List.length_cons] at hk
            omega
          have prepend : ∀ (a : FinsetMinorIndex n m)
              (s : List (FinsetMinorIndex n m)),
              IsStandardMinorList s → s.length < k →
              minorListPoly (D := D) (a :: s) ∈
                standardMinorProductSpanOfLength (D := D) n m (s.length + 1) := by
            intro a s hs hslen
            generalize hdef : a.defect = q
            induction q using Nat.strong_induction_on generalizing a s with
            | ind q inner =>
                cases s with
                | nil =>
                    exact standard_minorListPoly_mem_spanOfLength
                      (D := D) (n := n) (m := m) [a] trivial
                | cons b r =>
                    by_cases hab : a ≼ᵢ b
                    · apply AddSubgroup.subset_closure
                      exact ⟨a :: b :: r, ⟨hab, hs⟩, rfl, rfl⟩
                    · have hpair := two_minor_mem_pairReductionSpan
                        (D := D) a b hab
                      have hpairTail :
                          (a.poly * b.poly) * minorListPoly (D := D) r ∈
                            standardMinorProductSpanOfLength
                              (D := D) n m ((b :: r).length + 1) := by
                        apply mul_right_mem_of_mem_closure
                          (standardMinorProductSpanOfLength
                            (D := D) n m ((b :: r).length + 1))
                          (pairReductionGenerators (D := D) a)
                          (minorListPoly (D := D) r) (a.poly * b.poly)
                        · intro y hy
                          rcases hy with ⟨a', b', ha'a, ha'b', rfl⟩
                          have htail : minorListPoly (D := D) (b' :: r) ∈
                              standardMinorProductSpanOfLength
                                (D := D) n m (b' :: r).length := by
                            exact outer (b' :: r).length (by simpa using hslen)
                              (b' :: r) rfl
                          rw [mul_assoc]
                          change a'.poly * minorListPoly (D := D) (b' :: r) ∈
                            standardMinorProductSpanOfLength
                              (D := D) n m ((b :: r).length + 1)
                          apply mul_left_mem_of_mem_closure
                            (standardMinorProductSpanOfLength
                              (D := D) n m ((b :: r).length + 1))
                            {x | ∃ u : List (FinsetMinorIndex n m),
                              IsStandardMinorList u ∧
                              u.length = (b' :: r).length ∧
                              x = minorListPoly (D := D) u}
                            a'.poly (minorListPoly (D := D) (b' :: r))
                          · intro z hz
                            rcases hz with ⟨u, huStd, huLen, rfl⟩
                            have hdeflt : a'.defect < q :=
                              (finsetMinorIndex_defect_lt_of_LT ha'a).trans_eq hdef
                            have hpre := inner a'.defect hdeflt a' u huStd (by
                              simpa [huLen] using hslen)
                            simpa [huLen] using hpre
                          · exact htail
                        · exact hpair
                      simpa [minorListPoly, mul_assoc] using hpairTail
          have htail := outer t.length htlen t rfl
          have hcons : minorListPoly (D := D) (d :: t) ∈
              standardMinorProductSpanOfLength (D := D) n m (t.length + 1) := by
            apply mul_left_mem_of_mem_closure
              (standardMinorProductSpanOfLength (D := D) n m (t.length + 1))
              {x | ∃ s : List (FinsetMinorIndex n m),
                IsStandardMinorList s ∧ s.length = t.length ∧
                  x = minorListPoly (D := D) s}
              d.poly (minorListPoly (D := D) t)
            · intro x hx
              rcases hx with ⟨s, hs, hslen, rfl⟩
              have hp := prepend d s hs (by simpa [hslen] using htlen)
              simpa [hslen] using hp
            · exact htail
          have hk' : t.length + 1 = k := by simpa using hk
          rw [hk'] at hcons
          exact hcons

/-! ## Spanning the polynomial ring -/

/-- The coefficient-linear span of standard products. -/
@[expose] def standardMinorProductSubmodule (D : Type*) [CommRing D] (n m : ℕ) :
    Submodule D (GenericPoly D n m) :=
  Submodule.span D
    {x | ∃ l : List (FinsetMinorIndex n m),
      IsStandardMinorList l ∧ x = minorListPoly (D := D) l}

lemma minorListPoly_append {D : Type*} [CommRing D] {n m : ℕ}
    (l₁ l₂ : List (FinsetMinorIndex n m)) :
    minorListPoly (D := D) (l₁ ++ l₂) =
      minorListPoly (D := D) l₁ * minorListPoly (D := D) l₂ := by
  induction l₁ with
  | nil => simp
  | cons d l ih => simp [ih, mul_assoc]

lemma minorListPoly_mem_standardSubmodule
    {D : Type*} [CommRing D] {n m : ℕ}
    (l : List (FinsetMinorIndex n m)) :
    minorListPoly (D := D) l ∈ standardMinorProductSubmodule D n m := by
  have hlen := minorListPoly_mem_standardSpanOfLength (D := D) l
  apply (AddSubgroup.closure_le
    (standardMinorProductSubmodule D n m).toAddSubgroup).mpr ?_ hlen
  intro x hx
  rcases hx with ⟨u, huStd, -, rfl⟩
  apply Submodule.subset_span
  exact ⟨u, huStd, rfl⟩

lemma standardSubmodule_mul_minor
    {D : Type*} [CommRing D] {n m : ℕ}
    (d : FinsetMinorIndex n m) {x : GenericPoly D n m}
    (hx : x ∈ standardMinorProductSubmodule D n m) :
    x * d.poly ∈ standardMinorProductSubmodule D n m := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
      rcases hy with ⟨l, hl, rfl⟩
      have hlist := minorListPoly_mem_standardSubmodule
        (D := D) (l ++ [d])
      rw [minorListPoly_append] at hlist
      simpa using hlist
  | zero => simp
  | add x y _ _ hx hy => simpa [add_mul] using
      (standardMinorProductSubmodule D n m).add_mem hx hy
  | smul a x _ hx =>
      rw [smul_mul_assoc]
      exact (standardMinorProductSubmodule D n m).smul_mem a hx

/-- The `1 × 1` minor at `(i,j)`. -/
@[expose] def singletonMinorIndex {n m : ℕ} (i : Fin n) (j : Fin m) :
    FinsetMinorIndex n m where
  rows := {i}
  cols := {j}
  card_eq := by simp

@[simp] lemma singletonMinorIndex_poly {D : Type*} [CommRing D]
    {n m : ℕ} (i : Fin n) (j : Fin m) :
    (singletonMinorIndex i j).poly =
      (MvPolynomial.X (i, j) : GenericPoly D n m) := by
  unfold FinsetMinorIndex.poly singletonMinorIndex finsetMinorPoly
  rw [dite_eq_left ((Finset.card_singleton i).trans (Finset.card_singleton j).symm)]
  unfold minorPoly minorMatrix
  let M : Matrix (Fin ({i} : Finset (Fin n)).card)
      (Fin ({i} : Finset (Fin n)).card) (GenericPoly D n m) :=
    fun a b ↦ MvPolynomial.X
      ((({i} : Finset (Fin n)).orderEmbOfFin rfl) a,
        (({j} : Finset (Fin m)).orderEmbOfFin (by simp)) b)
  let e : Fin ({i} : Finset (Fin n)).card ≃ Fin 1 :=
    (Fin.castOrderIso (Finset.card_singleton i)).toEquiv
  change Matrix.det M = MvPolynomial.X (i, j)
  calc
    Matrix.det M = Matrix.det (M.reindex e e) :=
      (Matrix.det_reindex_self e M).symm
    _ = (M.reindex e e) 0 0 := Matrix.det_fin_one _
    _ = MvPolynomial.X (i, j) := by
      change MvPolynomial.X
        ((({i} : Finset (Fin n)).orderEmbOfFin rfl) (e.symm 0),
          (({j} : Finset (Fin m)).orderEmbOfFin (by simp)) (e.symm 0)) = _
      have hi : (({i} : Finset (Fin n)).orderEmbOfFin rfl) (e.symm 0) = i :=
        Finset.mem_singleton.mp
          (Finset.orderEmbOfFin_mem ({i} : Finset (Fin n)) rfl (e.symm 0))
      have hj : (({j} : Finset (Fin m)).orderEmbOfFin (by simp)) (e.symm 0) = j :=
        Finset.mem_singleton.mp
          (Finset.orderEmbOfFin_mem ({j} : Finset (Fin m)) (by simp) (e.symm 0))
      rw [hi, hj]

/-- Standard products span the entire generic polynomial ring over its
coefficient ring. -/
theorem mem_standardMinorProductSubmodule
    {D : Type*} [CommRing D] {n m : ℕ} (p : GenericPoly D n m) :
    p ∈ standardMinorProductSubmodule D n m := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      have hone : (1 : GenericPoly D n m) ∈
          standardMinorProductSubmodule D n m :=
        minorListPoly_mem_standardSubmodule (D := D) []
      have ha := (standardMinorProductSubmodule D n m).smul_mem a hone
      rw [MvPolynomial.smul_eq_C_mul, mul_one] at ha
      exact ha
  | add p q hp hq =>
      exact (standardMinorProductSubmodule D n m).add_mem hp hq
  | mul_X p ij hp =>
      simpa using standardSubmodule_mul_minor
        (D := D) (singletonMinorIndex ij.1 ij.2) hp

theorem standardMinorProductSubmodule_eq_top
    (D : Type*) [CommRing D] (n m : ℕ) :
    standardMinorProductSubmodule D n m = ⊤ := by
  apply top_unique
  intro p _
  exact mem_standardMinorProductSubmodule p

end GenericMaximalMinor

end

end Cslib
