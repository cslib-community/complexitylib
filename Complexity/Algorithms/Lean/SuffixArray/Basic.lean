/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.Data.List.CommonPrefix
public import Mathlib.Data.List.Lex
import Mathlib.Data.List.Nodup

/-!
# Suffix arrays and LCP arrays

The suffix array of a word `w` over a linearly ordered alphabet lists the starting positions
`0, …, |w| - 1` of its nonempty suffixes `w.drop i` in increasing lexicographic order
(`[ManberMyers1993]`). Its LCP array records the length of the longest common prefix of every
two suffixes adjacent in that order, measured by `List.lcpLen`
(`Complexity.Foundations.Data.List.CommonPrefix`). This module gives the specifications, the
uniqueness of suffix arrays, a reference construction by sorting, and the combinatorial lemma
behind Kasai et al.'s linear-time LCP construction (`[KasaiLeeArimuraArikawaPark2001]`).

## Source Conventions

* **Indexing:** positions and ranks are `0`-based. The suffix of rank `r` starts at `sa[r]`, and
  `lcp[r]` compares the suffixes of ranks `r - 1` and `r`; `lcp[0] = 0` by convention.
* **Alphabet:** any `[LinearOrder α]`, with Mathlib's lexicographic order on `List α`, in which a
  proper prefix is smaller than the word it extends. No end-of-word sentinel is assumed, and the
  empty suffix (position `|w|`) is not listed.

## Main definitions

* `Cslib.Algorithms.Lean.SuffixArray.IsSuffixArray`: `sa` is a permutation of
  `List.range w.length` whose suffixes are strictly increasing.
* `Cslib.Algorithms.Lean.SuffixArray.suffixArray`: the positions sorted by their suffixes.
* `Cslib.Algorithms.Lean.SuffixArray.lcpArray`: the LCP array of a list of positions.

## Main results

* `Cslib.Algorithms.Lean.SuffixArray.IsSuffixArray.unique`: suffix arrays are unique.
* `Cslib.Algorithms.Lean.SuffixArray.isSuffixArray_suffixArray`: the sorting construction is the
  suffix array.
* `Cslib.Algorithms.Lean.SuffixArray.IsSuffixArray.lt_iff_drop_lt`: rank order is suffix order.
* `Cslib.Algorithms.Lean.SuffixArray.IsSuffixArray.getElem_lcpArray_sub_one_le`: the height lemma
  `lcp[rank[i + 1]] ≥ lcp[rank[i]] - 1` of `[KasaiLeeArimuraArikawaPark2001]`, stated for ranks
  `r`, `r'` with `sa[r] + 1 = sa[r']`.

## References

* [U. Manber and G. Myers, *Suffix Arrays: A New Method for On-Line String
  Searches*][ManberMyers1993]
* [T. Kasai, G. Lee, H. Arimura, S. Arikawa, and K. Park, *Linear-Time Longest-Common-Prefix
  Computation in Suffix Arrays and Its Applications*][KasaiLeeArimuraArikawaPark2001]
-/

public section

namespace Cslib.Algorithms.Lean.SuffixArray

variable {α : Type*}

/-! ## Suffix arrays -/

/-- `sa` is the suffix array of `w`: a permutation of the positions `0, …, |w| - 1` listing the
suffixes `w.drop i` in strictly increasing lexicographic order. -/
structure IsSuffixArray [LinearOrder α] (w : List α) (sa : List ℕ) : Prop where
  /-- `sa` lists every position of `w` exactly once. -/
  perm : sa.Perm (List.range w.length)
  /-- The suffixes at the listed positions strictly increase. -/
  sorted : sa.Pairwise fun i j => w.drop i < w.drop j

section SuffixArray

variable [LinearOrder α] {w : List α} {sa : List ℕ}

theorem isSuffixArray_iff :
    IsSuffixArray w sa ↔
      sa.Perm (List.range w.length) ∧ sa.Pairwise fun i j => w.drop i < w.drop j :=
  ⟨fun h => ⟨h.perm, h.sorted⟩, fun h => ⟨h.1, h.2⟩⟩

instance instDecidableIsSuffixArray : Decidable (IsSuffixArray w sa) :=
  decidable_of_iff _ isSuffixArray_iff.symm

namespace IsSuffixArray

theorem length_eq (h : IsSuffixArray w sa) : sa.length = w.length := by
  rw [h.perm.length_eq, List.length_range]

theorem nodup (h : IsSuffixArray w sa) : sa.Nodup :=
  h.perm.nodup_iff.mpr List.nodup_range

theorem mem_iff (h : IsSuffixArray w sa) {i : ℕ} : i ∈ sa ↔ i < w.length := by
  rw [h.perm.mem_iff, List.mem_range]

theorem getElem_lt (h : IsSuffixArray w sa) {r : ℕ} (hr : r < sa.length) :
    sa[r] < w.length :=
  h.mem_iff.mp (List.getElem_mem hr)

theorem getElem_eq_getElem_iff (h : IsSuffixArray w sa) {r r' : ℕ} (hr : r < sa.length)
    (hr' : r' < sa.length) : sa[r] = sa[r'] ↔ r = r' :=
  h.nodup.getElem_inj_iff

/-- Ranks order the suffixes strictly. -/
theorem drop_lt_drop (h : IsSuffixArray w sa) {r r' : ℕ} (hr : r < r') (hr' : r' < sa.length) :
    w.drop sa[r] < w.drop sa[r'] :=
  List.pairwise_iff_getElem.mp h.sorted r r' (by omega) hr' hr

/-- Rank order is suffix order. -/
theorem lt_iff_drop_lt (h : IsSuffixArray w sa) {r r' : ℕ} (hr : r < sa.length)
    (hr' : r' < sa.length) : r < r' ↔ w.drop sa[r] < w.drop sa[r'] := by
  refine ⟨fun hlt => h.drop_lt_drop hlt hr', fun hlt => ?_⟩
  by_contra hge
  rcases Nat.lt_or_eq_of_le (Nat.le_of_not_lt hge) with hgt | heq
  · exact lt_asymm hlt (h.drop_lt_drop hgt hr)
  · subst heq
    exact lt_irrefl _ hlt

/-- Suffix arrays are unique. -/
theorem unique {sa' : List ℕ} (h : IsSuffixArray w sa) (h' : IsSuffixArray w sa') : sa = sa' :=
  List.Perm.eq_of_pairwise (le := fun i j => w.drop i < w.drop j)
    (fun _ _ _ _ hab hba => absurd (lt_trans hab hba) (lt_irrefl _))
    h.sorted h'.sorted (h.perm.trans h'.perm.symm)

/-- Every position has a rank. -/
theorem exists_getElem_eq (h : IsSuffixArray w sa) {i : ℕ} (hi : i < w.length) :
    ∃ (r : ℕ) (hr : r < sa.length), sa[r] = i :=
  List.getElem_of_mem (h.mem_iff.mpr hi)

end IsSuffixArray

/-! ## The reference construction -/

/-- The suffix array computed by sorting the positions `0, …, |w| - 1` by their suffixes. -/
def suffixArray (w : List α) : List ℕ :=
  (List.range w.length).mergeSort fun i j => decide (w.drop i ≤ w.drop j)

omit [LinearOrder α] in
private theorem drop_ne_drop {i j : ℕ} (hi : i < w.length) (hj : j < w.length) (hij : i ≠ j) :
    w.drop i ≠ w.drop j := by
  intro heq
  have := congrArg List.length heq
  simp only [List.length_drop] at this
  omega

/-- Sorting the positions by their suffixes yields the suffix array. -/
theorem isSuffixArray_suffixArray (w : List α) : IsSuffixArray w (suffixArray w) := by
  have hperm : (suffixArray w).Perm (List.range w.length) := List.mergeSort_perm _ _
  refine ⟨hperm, ?_⟩
  have hle : (suffixArray w).Pairwise fun i j => decide (w.drop i ≤ w.drop j) :=
    List.pairwise_mergeSort
      (fun a b c hab hbc => by
        simp only [decide_eq_true_eq] at hab hbc ⊢
        exact le_trans hab hbc)
      (fun a b => by
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        exact le_total _ _)
      _
  have hnd : (suffixArray w).Nodup := hperm.nodup_iff.mpr List.nodup_range
  refine (hle.and hnd).imp_of_mem fun {i j} hi hj ⟨hij, hne⟩ => ?_
  simp only [decide_eq_true_eq] at hij
  rw [hperm.mem_iff, List.mem_range] at hi hj
  exact lt_of_le_of_ne hij (drop_ne_drop hi hj hne)

/-- A list is a suffix array of `w` iff it is `suffixArray w`. -/
theorem isSuffixArray_iff_eq_suffixArray : IsSuffixArray w sa ↔ sa = suffixArray w :=
  ⟨fun h => h.unique (isSuffixArray_suffixArray w), fun h => h ▸ isSuffixArray_suffixArray w⟩

end SuffixArray

/-! ## LCP arrays -/

section LCPArray

variable [DecidableEq α]

/-- The LCP array of `w` with respect to the positions `sa`: entry `0` is `0` and entry `r > 0`
is the length of the longest common prefix of the suffixes at `sa[r - 1]` and `sa[r]`. -/
def lcpArray (w : List α) : List ℕ → List ℕ
  | [] => []
  | i :: sa => 0 :: List.zipWith (fun j k => List.lcpLen (w.drop j) (w.drop k)) (i :: sa) sa

@[simp] theorem length_lcpArray (w : List α) (sa : List ℕ) :
    (lcpArray w sa).length = sa.length := by
  cases sa with
  | nil => rfl
  | cons i sa =>
    simp only [lcpArray, List.length_cons, List.length_zipWith]
    omega

theorem getElem_lcpArray_zero (w : List α) (sa : List ℕ) (h : 0 < (lcpArray w sa).length) :
    (lcpArray w sa)[0] = 0 := by
  cases sa with
  | nil => simp only [length_lcpArray, List.length_nil, lt_self_iff_false] at h
  | cons i sa => rfl

theorem getElem_lcpArray_of_pos (w : List α) (sa : List ℕ) {r : ℕ}
    (hr : r < (lcpArray w sa).length) (hr0 : 0 < r) :
    (lcpArray w sa)[r] =
      List.lcpLen (w.drop (sa[r - 1]'(by simp only [length_lcpArray] at hr; omega)))
        (w.drop (sa[r]'(by simpa only [length_lcpArray] using hr))) := by
  cases sa with
  | nil => simp only [length_lcpArray, List.length_nil] at hr; omega
  | cons i sa =>
    obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    simp only [lcpArray, List.getElem_cons_succ, List.getElem_zipWith, Nat.add_sub_cancel]

end LCPArray

section Height

variable [LinearOrder α] {w : List α} {sa : List ℕ}

/-- **Height lemma** (`[KasaiLeeArimuraArikawaPark2001]`): if the suffix of rank `r'` starts one
position after the suffix of rank `r`, then `lcp[r'] ≥ lcp[r] - 1`. In terms of the rank array,
`lcp[rank[i + 1]] ≥ lcp[rank[i]] - 1`. -/
theorem IsSuffixArray.getElem_lcpArray_sub_one_le (h : IsSuffixArray w sa) {r r' : ℕ}
    (hr : r < sa.length) (hr' : r' < sa.length) (hsucc : sa[r] + 1 = sa[r']) :
    (lcpArray w sa)[r]'(by simpa only [length_lcpArray] using hr) - 1 ≤
      (lcpArray w sa)[r']'(by simpa only [length_lcpArray] using hr') := by
  rcases Nat.eq_zero_or_pos r with rfl | hr0
  · rw [getElem_lcpArray_zero]; omega
  rw [getElem_lcpArray_of_pos w sa _ hr0]
  set i := sa[r]
  set j := sa[r - 1]'(by omega)
  set L := List.lcpLen (w.drop j) (w.drop i) with hL
  have hshift : L - 1 ≤ List.lcpLen (w.drop (j + 1)) (w.drop (i + 1)) := by
    have := List.lcpLen_sub_one_le_lcpLen_tail (w.drop j) (w.drop i)
    simpa only [List.tail_drop] using this
  rcases Nat.lt_or_ge L 2 with hL2 | hL2
  · omega
  -- Both suffixes have length at least `L ≥ 2`, so `j + 1 < |w|`.
  have hjn : j + 1 < w.length := by
    have := List.lcpLen_le_length_left (w.drop j) (w.drop i)
    simp only [List.length_drop] at this
    omega
  obtain ⟨q, hq, hqj⟩ := h.exists_getElem_eq hjn
  -- The heads agree, so the order of the tails is that of the suffixes.
  have hji : w.drop (j + 1) < w.drop (i + 1) := by
    have hlt : w.drop j < w.drop i := h.drop_lt_drop (by omega) hr
    have hjw : j < w.length := by omega
    have hiw : i < w.length := h.getElem_lt hr
    rw [List.drop_eq_getElem_cons hjw, List.drop_eq_getElem_cons hiw] at hlt hL
    have heq : w[j] = w[i] := by
      by_contra hne
      simp only [List.lcpLen_cons_cons, hne, ↓reduceIte] at hL
      omega
    rw [heq] at hlt
    exact List.lex_cons_iff.mp hlt
  have hqr' : q < r' := by
    rw [h.lt_iff_drop_lt hq hr', hqj, ← hsucc]
    exact hji
  rw [getElem_lcpArray_of_pos w sa _ (by omega)]
  have hle1 : w.drop sa[r' - 1] ≥ w.drop sa[q] := by
    rcases Nat.lt_or_eq_of_le (Nat.le_sub_one_of_lt hqr') with hlt | heq
    · exact le_of_lt (h.drop_lt_drop hlt (by omega))
    · simp only [heq, le_refl]
  have hle2 : w.drop sa[r' - 1] ≤ w.drop sa[r'] :=
    le_of_lt (h.drop_lt_drop (by omega) hr')
  have := List.lcpLen_le_lcpLen_of_le_of_le_right hle1 hle2
  rw [hqj] at this
  rw [hsucc] at hshift
  omega

end Height

end Cslib.Algorithms.Lean.SuffixArray
