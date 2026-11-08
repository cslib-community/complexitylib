/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.List.Lex
public import Mathlib.Data.List.Perm.Basic
import Complexity.Foundations.Data.List.Lex
import Mathlib.Data.List.Sort

/-!
# Suffix arrays and LCP arrays

The suffix array of a word `w` over a linearly ordered alphabet lists the starting positions
`0, …, |w| - 1` of its nonempty suffixes `w.drop i` in increasing lexicographic order
(`[ManberMyers1993]`). Its LCP array records the length of the longest common prefix of every
two suffixes adjacent in that order. This module gives the specifications, the uniqueness of
suffix arrays, a reference construction by sorting, and the combinatorial lemma behind Kasai
et al.'s linear-time LCP construction (`[KasaiLeeArimuraArikawaPark2001]`).

## Source Conventions

* **Indexing:** positions and ranks are `0`-based. The suffix of rank `r` starts at `sa[r]`, and
  `lcp[r]` compares the suffixes of ranks `r - 1` and `r`; `lcp[0] = 0` by convention.
* **Alphabet:** any `[LinearOrder α]`, with Mathlib's lexicographic order on `List α`, in which a
  proper prefix is smaller than the word it extends. No end-of-word sentinel is assumed, and the
  empty suffix (position `|w|`) is not listed.

## Main definitions

* `Cslib.Algorithms.Lean.SuffixArray.lcpLen`: length of the longest common prefix of two lists.
* `Cslib.Algorithms.Lean.SuffixArray.IsSuffixArray`: `sa` is a permutation of
  `List.range w.length` whose suffixes are strictly increasing.
* `Cslib.Algorithms.Lean.SuffixArray.suffixArray`: the positions sorted by their suffixes.
* `Cslib.Algorithms.Lean.SuffixArray.lcpArray`: the LCP array of a list of positions.

## Main results

* `Cslib.Algorithms.Lean.SuffixArray.IsSuffixArray.eq`: suffix arrays are unique.
* `Cslib.Algorithms.Lean.SuffixArray.isSuffixArray_suffixArray`: the sorting construction is the
  suffix array.
* `Cslib.Algorithms.Lean.SuffixArray.IsSuffixArray.lt_iff_drop_lt`: rank order is suffix order.
* `Cslib.Algorithms.Lean.SuffixArray.lcpLen_le_lcpLen_of_le_of_le_left` and `_right`: a list
  lexicographically between two others shares their longest common prefix.
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

/-! ## Longest common prefix -/

/-- Length of the longest common prefix of `u` and `v`. -/
@[expose] def lcpLen [DecidableEq α] : List α → List α → ℕ
  | a :: u, b :: v => if a = b then lcpLen u v + 1 else 0
  | _, _ => 0

section lcp

variable [DecidableEq α]

@[simp] theorem lcpLen_nil_left (v : List α) : lcpLen [] v = 0 := by
  cases v <;> rfl

@[simp] theorem lcpLen_nil_right (u : List α) : lcpLen u [] = 0 := by
  cases u <;> rfl

theorem lcpLen_cons_cons (a b : α) (u v : List α) :
    lcpLen (a :: u) (b :: v) = if a = b then lcpLen u v + 1 else 0 := rfl

@[simp] theorem lcpLen_cons_cons_self (a : α) (u v : List α) :
    lcpLen (a :: u) (a :: v) = lcpLen u v + 1 := by
  simp only [lcpLen_cons_cons, ↓reduceIte]

theorem lcpLen_comm (u v : List α) : lcpLen u v = lcpLen v u := by
  induction u generalizing v with
  | nil => simp only [lcpLen_nil_left, lcpLen_nil_right]
  | cons a u ih =>
    cases v with
    | nil => simp only [lcpLen_nil_left, lcpLen_nil_right]
    | cons b v =>
      simp only [lcpLen_cons_cons, ih v]
      by_cases h : a = b
      · simp only [h, ↓reduceIte]
      · simp only [h, ↓reduceIte, Ne.symm h]

theorem lcpLen_le_length_left (u v : List α) : lcpLen u v ≤ u.length := by
  induction u generalizing v with
  | nil => simp only [lcpLen_nil_left, List.length_nil, Nat.le_refl]
  | cons a u ih =>
    cases v with
    | nil => simp only [lcpLen_nil_right, Nat.zero_le]
    | cons b v =>
      rw [lcpLen_cons_cons]
      split_ifs
      · have := ih v
        simp only [List.length_cons]
        omega
      · exact Nat.zero_le _

theorem lcpLen_le_length_right (u v : List α) : lcpLen u v ≤ v.length := by
  rw [lcpLen_comm]
  exact lcpLen_le_length_left v u

/-- `k ≤ lcpLen u v` iff both lists have length at least `k` and agree on their first `k`
entries. -/
theorem le_lcpLen_iff {u v : List α} {k : ℕ} :
    k ≤ lcpLen u v ↔ k ≤ u.length ∧ k ≤ v.length ∧ u.take k = v.take k := by
  induction k generalizing u v with
  | zero => simp only [Nat.zero_le, List.take_zero, and_self]
  | succ k ih =>
    cases u with
    | nil => simp only [lcpLen_nil_left, List.length_nil]; omega
    | cons a u =>
      cases v with
      | nil => simp only [lcpLen_nil_right, List.length_nil]; omega
      | cons b v =>
        rw [lcpLen_cons_cons, List.take_succ_cons, List.take_succ_cons, List.cons_eq_cons,
          List.length_cons, List.length_cons]
        by_cases hab : a = b
        · simp only [hab, ↓reduceIte, true_and, Nat.add_le_add_iff_right, ih]
        · simp only [hab, ↓reduceIte, false_and, and_false, iff_false]
          omega

/-- A common prefix of length `h` splits off the longest common prefix. -/
theorem lcpLen_eq_add_lcpLen_drop {u v : List α} {h : ℕ} (hh : h ≤ lcpLen u v) :
    lcpLen u v = h + lcpLen (u.drop h) (v.drop h) := by
  induction h generalizing u v with
  | zero => simp only [List.drop_zero, Nat.zero_add]
  | succ h ih =>
    cases u with
    | nil => simp only [lcpLen_nil_left] at hh; omega
    | cons a u =>
      cases v with
      | nil => simp only [lcpLen_nil_right] at hh; omega
      | cons b v =>
        rw [lcpLen_cons_cons] at hh ⊢
        by_cases hab : a = b
        · simp only [hab, ↓reduceIte] at hh ⊢
          rw [ih (by omega), List.drop_succ_cons, List.drop_succ_cons]
          omega
        · simp only [hab, ↓reduceIte] at hh
          omega

/-- Dropping one leading entry from both lists shortens their longest common prefix by at most
one. -/
theorem lcpLen_sub_one_le_lcpLen_tail (u v : List α) :
    lcpLen u v - 1 ≤ lcpLen u.tail v.tail := by
  cases u with
  | nil => simp only [lcpLen_nil_left, Nat.zero_sub, Nat.zero_le]
  | cons a u =>
    cases v with
    | nil => simp only [lcpLen_nil_right, Nat.zero_sub, Nat.zero_le]
    | cons b v =>
      rw [lcpLen_cons_cons, List.tail_cons, List.tail_cons]
      split_ifs <;> omega

end lcp

section order

variable [LinearOrder α]

/-- A list lexicographically between `u` and `x` shares at least `lcpLen u x` leading entries
with `u`. -/
theorem lcpLen_le_lcpLen_of_le_of_le_left {u v x : List α} (huv : u ≤ v) (hvx : v ≤ x) :
    lcpLen u x ≤ lcpLen u v := by
  set k := lcpLen u x
  obtain ⟨hku, hkx, htake⟩ := le_lcpLen_iff.mp (le_refl k)
  have hpu : u.take k <+: u := List.take_prefix k u
  have hpx : u.take k <+: x := htake ▸ List.take_prefix k x
  have hpv : u.take k <+: v := List.IsPrefix.of_prefix_of_le_of_le hpu hpx huv hvx
  have hlen : (u.take k).length = k := by simp only [List.length_take]; omega
  refine le_lcpLen_iff.mpr ⟨hku, ?_, ?_⟩
  · have := hpv.length_le; omega
  · have := List.prefix_iff_eq_take.mp hpv
    rw [hlen] at this
    exact this

/-- A list lexicographically between `u` and `x` shares at least `lcpLen u x` leading entries
with `x`. -/
theorem lcpLen_le_lcpLen_of_le_of_le_right {u v x : List α} (huv : u ≤ v) (hvx : v ≤ x) :
    lcpLen u x ≤ lcpLen v x := by
  set k := lcpLen u x
  obtain ⟨hku, hkx, htake⟩ := le_lcpLen_iff.mp (le_refl k)
  have hpu : u.take k <+: u := List.take_prefix k u
  have hpx : u.take k <+: x := htake ▸ List.take_prefix k x
  have hpv : u.take k <+: v := List.IsPrefix.of_prefix_of_le_of_le hpu hpx huv hvx
  have hlen : (u.take k).length = k := by simp only [List.length_take]; omega
  refine le_lcpLen_iff.mpr ⟨?_, hkx, ?_⟩
  · have := hpv.length_le; omega
  · have := List.prefix_iff_eq_take.mp hpv
    rw [hlen] at this
    rw [← this, htake]

end order

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

instance : Decidable (IsSuffixArray w sa) :=
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
theorem eq {sa' : List ℕ} (h : IsSuffixArray w sa) (h' : IsSuffixArray w sa') : sa = sa' :=
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
@[expose] def suffixArray (w : List α) : List ℕ :=
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
  ⟨fun h => h.eq (isSuffixArray_suffixArray w), fun h => h ▸ isSuffixArray_suffixArray w⟩

end SuffixArray

/-! ## LCP arrays -/

section LCPArray

variable [DecidableEq α]

/-- The LCP array of `w` with respect to the positions `sa`: entry `0` is `0` and entry `r > 0`
is the length of the longest common prefix of the suffixes at `sa[r - 1]` and `sa[r]`. -/
@[expose] def lcpArray (w : List α) : List ℕ → List ℕ
  | [] => []
  | i :: sa => 0 :: List.zipWith (fun j k => lcpLen (w.drop j) (w.drop k)) (i :: sa) sa

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
      lcpLen (w.drop (sa[r - 1]'(by simp only [length_lcpArray] at hr; omega)))
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
  set L := lcpLen (w.drop j) (w.drop i) with hL
  have hshift : L - 1 ≤ lcpLen (w.drop (j + 1)) (w.drop (i + 1)) := by
    have := lcpLen_sub_one_le_lcpLen_tail (w.drop j) (w.drop i)
    simpa only [List.tail_drop] using this
  rcases Nat.lt_or_ge L 2 with hL2 | hL2
  · omega
  -- Both suffixes have length at least `L ≥ 2`, so `j + 1 < |w|`.
  have hjn : j + 1 < w.length := by
    have := lcpLen_le_length_left (w.drop j) (w.drop i)
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
      simp only [lcpLen_cons_cons, hne, ↓reduceIte] at hL
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
  have := lcpLen_le_lcpLen_of_le_of_le_right hle1 hle2
  rw [hqj] at this
  rw [hsucc] at hshift
  omega

end Height

end Cslib.Algorithms.Lean.SuffixArray
