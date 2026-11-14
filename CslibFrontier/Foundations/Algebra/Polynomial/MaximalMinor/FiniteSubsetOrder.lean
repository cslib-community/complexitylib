/-
Copyright (c) 2026 Yuqing Kong, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuqing Kong, Christian Reitwiessner
-/

module
-- upstream: candidate (Mathlib, generic maximal minors)

public import CslibFrontier.Init
public import Mathlib

/-!
# The prefix order on finite subsets

This file contains the finite combinatorics used by the straightening law for
minors.  For subsets `A B` of `Fin N`, the relation `A ≼ B` means that every
initial segment contains at least as many elements of `A` as of `B`.

The definition uses initial segments of lengths `r : Fin (N + 1)`.  In
particular, the last value records the cardinality of the entire subset; this
also makes the definition uniform when `N = 0`.

Ported by Christian Reitwiessner from Yuqing Kong's Apache-2.0 formalization,
`FiniteSubsetOrder.lean` at commit
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

/-- The number of elements of `A` in the first `r` positions of `Fin N`. -/
@[expose] def prefixCard {N : ℕ} (A : Finset (Fin N)) (r : Fin (N + 1)) : ℕ :=
  (A.filter fun i ↦ i.val < r.val).card

/-- The standard order on finite subsets used for standard bitableaux. -/
@[expose] def PrefixLE {N : ℕ} (A B : Finset (Fin N)) : Prop :=
  ∀ r : Fin (N + 1), prefixCard B r ≤ prefixCard A r

/-- Notation for `PrefixLE`. -/
scoped infix:50 " ≼ₚ " => PrefixLE

lemma prefixLE_refl {N : ℕ} (A : Finset (Fin N)) : A ≼ₚ A := by
  intro r
  exact le_rfl

lemma prefixLE_trans {N : ℕ} {A B C : Finset (Fin N)}
    (hAB : A ≼ₚ B) (hBC : B ≼ₚ C) : A ≼ₚ C := by
  intro r
  exact (hBC r).trans (hAB r)

lemma prefixCard_last {N : ℕ} (A : Finset (Fin N)) :
    prefixCard A (Fin.last N) = A.card := by
  simp [prefixCard, Fin.last]

lemma card_ge_of_prefixLE {N : ℕ} {A B : Finset (Fin N)}
    (h : A ≼ₚ B) : B.card ≤ A.card := by
  simpa [prefixCard_last] using h (Fin.last N)

lemma prefixLE_of_superset {N : ℕ} {A B : Finset (Fin N)}
    (hBA : B ⊆ A) : A ≼ₚ B := by
  intro r
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter] at hi ⊢
  exact ⟨hBA hi.1, hi.2⟩

/-- The prefix ending immediately before `i`. -/
def prefixBefore {N : ℕ} (i : Fin N) : Fin (N + 1) :=
  ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩

/-- The prefix ending at `i`. -/
def prefixThrough {N : ℕ} (i : Fin N) : Fin (N + 1) :=
  ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩

lemma prefixCard_through {N : ℕ} (A : Finset (Fin N)) (i : Fin N) :
    prefixCard A (prefixThrough i) =
      prefixCard A (prefixBefore i) + if i ∈ A then 1 else 0 := by
  have hfilter :
      A.filter (fun j ↦ j.val < (prefixThrough i).val) =
        if i ∈ A then
          insert i (A.filter fun j ↦ j.val < (prefixBefore i).val)
        else A.filter fun j ↦ j.val < (prefixBefore i).val := by
    ext j
    by_cases hji : j = i
    · subst j
      by_cases hiA : i ∈ A <;> simp [hiA, prefixThrough, prefixBefore]
    · have hval : j.val ≠ i.val := fun h ↦ hji (Fin.ext h)
      by_cases hiA : i ∈ A <;>
        simp [hiA, hji, prefixThrough, prefixBefore] <;> omega
  rw [prefixCard, prefixCard, hfilter]
  by_cases hiA : i ∈ A
  · simp [hiA, prefixBefore]
  · simp [hiA]

/-- The prefix immediately before the `q`-th element of a finite subset has
exactly `q` elements. -/
lemma prefixCard_before_orderEmbOfFin {N : ℕ} (A : Finset (Fin N))
    (q : Fin A.card) :
    prefixCard A (prefixBefore (A.orderEmbOfFin rfl q)) = q.val := by
  let e : Fin A.card ↪ Fin N := (A.orderEmbOfFin rfl).toEmbedding
  have hfilter :
      A.filter (fun j ↦ j.val < (A.orderEmbOfFin rfl q).val) =
        (Finset.Iio q).map e := by
    ext j
    constructor
    · intro hj
      have hjA : j ∈ A := (Finset.mem_filter.mp hj).1
      have hjAset : j ∈ (A : Set (Fin N)) := hjA
      rw [← A.range_orderEmbOfFin rfl] at hjAset
      obtain ⟨k, rfl⟩ := hjAset
      apply Finset.mem_map.mpr
      refine ⟨k, ?_, rfl⟩
      exact Finset.mem_Iio.mpr
        ((A.orderEmbOfFin rfl).lt_iff_lt.mp (Finset.mem_filter.mp hj).2)
    · intro hj
      obtain ⟨k, hk, rfl⟩ := Finset.mem_map.mp hj
      apply Finset.mem_filter.mpr
      exact ⟨A.orderEmbOfFin_mem rfl k,
        (A.orderEmbOfFin rfl).lt_iff_lt.mpr (Finset.mem_Iio.mp hk)⟩
  rw [prefixCard, prefixBefore, hfilter, Finset.card_map, Fin.card_Iio]

/-- If `b` lies strictly before the `q`-th element of `A`, then at most `q`
elements of `A` occur at or before `b`. -/
lemma prefixCard_through_le_index_of_lt_orderEmbOfFin {N : ℕ}
    (A : Finset (Fin N)) (q : Fin A.card) (b : Fin N)
    (hb : b < A.orderEmbOfFin rfl q) :
    prefixCard A (prefixThrough b) ≤ q.val := by
  calc
    prefixCard A (prefixThrough b) ≤
        prefixCard A (prefixBefore (A.orderEmbOfFin rfl q)) := by
      apply Finset.card_le_card
      intro j hj
      simp only [Finset.mem_filter] at hj ⊢
      exact ⟨hj.1, by
        simp only [prefixThrough, prefixBefore] at hj ⊢
        omega⟩
    _ = q.val := prefixCard_before_orderEmbOfFin A q

/-- Prefix dominance implies the usual componentwise comparison of the
increasing enumerations.  This is the direction needed to recover a standard
bitableau from its diagonal monomial. -/
lemma orderEmbOfFin_le_of_prefixLE {N : ℕ} {A B : Finset (Fin N)}
    (hAB : A ≼ₚ B) (q : Fin B.card) :
    A.orderEmbOfFin rfl (Fin.castLE (card_ge_of_prefixLE hAB) q) ≤
      B.orderEmbOfFin rfl q := by
  let qA : Fin A.card := Fin.castLE (card_ge_of_prefixLE hAB) q
  let a := A.orderEmbOfFin rfl qA
  let b := B.orderEmbOfFin rfl q
  by_contra hnot
  have hba : b < a := lt_of_not_ge hnot
  have hB : prefixCard B (prefixThrough b) = q.val + 1 := by
    rw [prefixCard_through]
    simp only [b, B.orderEmbOfFin_mem, ite_true]
    rw [prefixCard_before_orderEmbOfFin]
  have hA : prefixCard A (prefixThrough b) ≤ q.val := by
    have := prefixCard_through_le_index_of_lt_orderEmbOfFin A qA b hba
    simpa [qA] using this
  have hdom := hAB (prefixThrough b)
  rw [hB] at hdom
  omega

lemma eq_of_prefixCard_eq {N : ℕ} {A B : Finset (Fin N)}
    (h : ∀ r : Fin (N + 1), prefixCard A r = prefixCard B r) : A = B := by
  ext i
  have hbefore := h (prefixBefore i)
  have hthrough := h (prefixThrough i)
  rw [prefixCard_through A i, prefixCard_through B i, hbefore] at hthrough
  by_cases hiA : i ∈ A <;> by_cases hiB : i ∈ B <;>
    simp_all

lemma prefixLE_antisymm {N : ℕ} {A B : Finset (Fin N)}
    (hAB : A ≼ₚ B) (hBA : B ≼ₚ A) : A = B := by
  apply eq_of_prefixCard_eq
  intro r
  exact Nat.le_antisymm (hBA r) (hAB r)

/-- The rank used to turn strict descent in the prefix order into descent in
the natural numbers. -/
def prefixRank {N : ℕ} (A : Finset (Fin N)) : ℕ :=
  ∑ r : Fin (N + 1), prefixCard A r

lemma prefixRank_mono {N : ℕ} {A B : Finset (Fin N)}
    (h : A ≼ₚ B) : prefixRank B ≤ prefixRank A := by
  unfold prefixRank
  exact Finset.sum_le_sum fun r _ ↦ h r

lemma prefixRank_lt_of_prefixLE_of_exists_lt {N : ℕ}
    {A B : Finset (Fin N)} (h : A ≼ₚ B)
    (hstrict : ∃ r : Fin (N + 1), prefixCard B r < prefixCard A r) :
    prefixRank B < prefixRank A := by
  rcases hstrict with ⟨r, hr⟩
  unfold prefixRank
  exact Finset.sum_lt_sum (fun i _ ↦ h i) ⟨r, Finset.mem_univ r, hr⟩

lemma exists_prefixCard_lt_of_prefixLE_of_ne {N : ℕ}
    {A B : Finset (Fin N)} (h : A ≼ₚ B) (hne : A ≠ B) :
    ∃ r : Fin (N + 1), prefixCard B r < prefixCard A r := by
  by_contra hnot
  push Not at hnot
  apply hne
  apply eq_of_prefixCard_eq
  intro r
  exact Nat.le_antisymm (hnot r) (h r)

lemma prefixRank_lt_of_prefixLE_of_ne {N : ℕ}
    {A B : Finset (Fin N)} (h : A ≼ₚ B) (hne : A ≠ B) :
    prefixRank B < prefixRank A :=
  prefixRank_lt_of_prefixLE_of_exists_lt h
    (exists_prefixCard_lt_of_prefixLE_of_ne h hne)

/-- Strict prefix order. -/
@[expose] def PrefixLT {N : ℕ} (A B : Finset (Fin N)) : Prop := A ≼ₚ B ∧ A ≠ B

/-- Notation for `PrefixLT`. -/
scoped infix:50 " ≺ₚ " => PrefixLT

/-- Defect from the largest possible prefix rank.  Moving strictly downward
in the prefix order strictly decreases this natural number. -/
@[expose] def prefixDefect {N : ℕ} (A : Finset (Fin N)) : ℕ :=
  prefixRank (Finset.univ : Finset (Fin N)) - prefixRank A

lemma prefixRank_le_univ {N : ℕ} (A : Finset (Fin N)) :
    prefixRank A ≤ prefixRank (Finset.univ : Finset (Fin N)) := by
  exact prefixRank_mono (prefixLE_of_superset (Finset.subset_univ A))

lemma prefixDefect_lt_of_prefixLT {N : ℕ} {A B : Finset (Fin N)}
    (h : A ≺ₚ B) : prefixDefect A < prefixDefect B := by
  have hrank : prefixRank B < prefixRank A :=
    prefixRank_lt_of_prefixLE_of_ne h.1 h.2
  have hbound := prefixRank_le_univ A
  unfold prefixDefect
  omega

lemma prefixDefect_le_of_prefixLE {N : ℕ} {A B : Finset (Fin N)}
    (h : A ≼ₚ B) : prefixDefect A ≤ prefixDefect B := by
  have hrank := prefixRank_mono h
  have hbound := prefixRank_le_univ A
  unfold prefixDefect
  omega

/-- The additive defect used for induction on a pair of row/column subsets. -/
@[expose] def laplaceDefect {N : ℕ} (A B : Finset (Fin N)) : ℕ :=
  prefixDefect A + prefixDefect B

lemma laplaceDefect_comm {N : ℕ} (A B : Finset (Fin N)) :
    laplaceDefect A B = laplaceDefect B A := by
  simp [laplaceDefect, add_comm]

lemma laplaceDefect_lt_of_left_strict {N : ℕ}
    {A B A' B' : Finset (Fin N)}
    (hA : A' ≺ₚ A) (hB : B' ≼ₚ B) :
    laplaceDefect A' B' < laplaceDefect A B := by
  unfold laplaceDefect
  exact Nat.add_lt_add_of_lt_of_le
    (prefixDefect_lt_of_prefixLT hA) (prefixDefect_le_of_prefixLE hB)

lemma laplaceDefect_lt_of_right_strict {N : ℕ}
    {A B A' B' : Finset (Fin N)}
    (hA : A' ≼ₚ A) (hB : B' ≺ₚ B) :
    laplaceDefect A' B' < laplaceDefect A B := by
  unfold laplaceDefect
  exact Nat.add_lt_add_of_le_of_lt
    (prefixDefect_le_of_prefixLE hA) (prefixDefect_lt_of_prefixLT hB)

end GenericMaximalMinor

end

end Cslib
