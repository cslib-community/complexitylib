/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init

/-!
# Word Borders, Periods, and the KMP Prefix Function

This module develops the combinatorics of word borders, periods, and the Knuth–Morris–Pratt
prefix (failure) function over lists with decidable equality (`[KnuthMorrisPratt1977]`;
`[CLRS2009]`, Section 32.4).

A length `k < w.length` is a *proper border length* of a word `w` (`IsProperBorderLen w k`) when
the prefix `w.take k` is also a suffix of `w`. Equivalently, `d = w.length - k` is a positive
*period* of `w` (`IsPeriod w d`), meaning `w[i] = w[i + d]` whenever `i + d < w.length`.

To treat failure-table construction and text scanning uniformly, we define
`maxPrefixSuffixUpTo p t B` as the largest length `k ≤ B` with `k ≤ p.length` such that `p.take k`
is a suffix of `t`. Specializing `t = w` and `B = w.length - 1` yields the maximum proper border
length `maxBorderLen w` and the KMP prefix function `borderLen p q = maxBorderLen (p.take q)`
(corresponding to $\pi[q]$ in `[CLRS2009]`, Section 32.4 for $1 \le q \le |p|$).

## Main definitions

* `Cslib.Algorithms.Lean.KMP.IsProperBorderLen`: `k < w.length` and `w.take k <:+ w`.
* `Cslib.Algorithms.Lean.KMP.IsPeriod`: period `d` of `w` (`w[i] = w[i + d]` for `i + d < |w|`).
* `Cslib.Algorithms.Lean.KMP.maxPrefixSuffixUpTo`: largest `k ≤ B` with `k ≤ |p|` and
  `p.take k <:+ t`.
* `Cslib.Algorithms.Lean.KMP.maxBorderLen`: maximum proper border length of `w` (`0` on `[]`).
* `Cslib.Algorithms.Lean.KMP.minPeriod`: minimum positive period `w.length - maxBorderLen w`.
* `Cslib.Algorithms.Lean.KMP.borderLen`: KMP prefix value `maxBorderLen (p.take q)`.
* `Cslib.Algorithms.Lean.KMP.borderChain`: strictly decreasing list of all proper border lengths
  of `p.take q` obtained by iterating `k ↦ borderLen p k`.
* `Cslib.Algorithms.Lean.KMP.nextLen`: pure KMP automaton transition updating a matched prefix
  length `k < p.length` upon reading character `c`.

## Main results

* `Cslib.Algorithms.Lean.KMP.isProperBorderLen_iff_isPeriod`: `IsProperBorderLen w k` holds iff
  `k < w.length` and `IsPeriod w (w.length - k)`.
* `Cslib.Algorithms.Lean.KMP.IsProperBorderLen.trans` and `IsProperBorderLen.to_take`: proper
  borders of `w` strictly shorter than a proper border `k` are exactly the proper borders of
  `w.take k`.
* `Cslib.Algorithms.Lean.KMP.mem_borderChain_iff` and `pairwise_gt_borderChain`: iterating
  `k ↦ borderLen p k` enumerates all proper border lengths of `p.take q` in strictly decreasing
  order (`[CLRS2009]`, Lemma 32.5).
* `Cslib.Algorithms.Lean.KMP.maxPrefixSuffixUpTo_append_singleton`: extending `t` by one character
  `c` updates `maxPrefixSuffixUpTo p t B` (`B < p.length`) via `nextLen p · c`, specializing both
  to `borderLen_succ` (`[CLRS2009]`, Lemma 32.6 and Corollary 32.7) and to the KMP text-scanning
  step.

## References

* [D. E. Knuth, J. H. Morris, Jr., and V. R. Pratt, *Fast Pattern Matching in
  Strings*][KnuthMorrisPratt1977]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest, and C. Stein, *Introduction to Algorithms*,
  3rd ed., Section 32.4][CLRS2009]
-/

public section

namespace Cslib.Algorithms.Lean.KMP

/-! ## One-character suffix extension -/

/-- Appending a single element preserves suffixes iff the base lists are suffixes and the
appended elements agree. -/
private theorem append_singleton_isSuffix_iff {α : Type*} {u t : List α} {a c : α} :
    u ++ [a] <:+ t ++ [c] ↔ u <:+ t ∧ a = c := by
  constructor
  · rintro ⟨s, hs⟩
    rw [← List.append_assoc] at hs
    have hlen : (s ++ u).length = t.length := by
      have h := congrArg List.length hs
      simp only [List.length_append, List.length_singleton] at h ⊢
      omega
    obtain ⟨hsu, hac⟩ := List.append_inj hs hlen
    exact ⟨⟨s, hsu⟩, List.singleton_inj.mp hac⟩
  · rintro ⟨⟨s, rfl⟩, rfl⟩
    exact ⟨s, (List.append_assoc s u [a]).symm⟩

/-- Extending a prefix `p.take j` (`j < p.length`) to `p.take (j + 1)` matches a suffix of
`t ++ [c]` iff `p.take j <:+ t` and `p[j] = c`. -/
private theorem take_succ_isSuffix_append_iff {α : Type*} {p t : List α} {c : α} {j : ℕ}
    (hj : j < p.length) :
    p.take (j + 1) <:+ t ++ [c] ↔ p.take j <:+ t ∧ p[j] = c := by
  rw [List.take_add_one, getElem?_pos p j hj, Option.toList_some, append_singleton_isSuffix_iff]

/-! ## Proper borders and periods -/

/-- `k` is a proper border length of `w` if `k < w.length` and the length-`k` prefix `w.take k`
is also a suffix of `w`. -/
@[expose] def IsProperBorderLen {α : Type*} (w : List α) (k : ℕ) : Prop :=
  k < w.length ∧ w.take k <:+ w

/-- `d` is a period of `w` if characters at distance `d` agree throughout `w`. -/
@[expose] def IsPeriod {α : Type*} (w : List α) (d : ℕ) : Prop :=
  ∀ (i : ℕ) (h : i + d < w.length), w[i]'(by omega) = w[i + d]'h

theorem isProperBorderLen_zero {α : Type*} {w : List α} (hw : 0 < w.length) :
    IsProperBorderLen w 0 :=
  ⟨hw, List.nil_suffix⟩

theorem not_isProperBorderLen_nil {α : Type*} (k : ℕ) : ¬ IsProperBorderLen ([] : List α) k := by
  rintro ⟨hk, _⟩
  exact Nat.not_lt_zero k hk

theorem isProperBorderLen_iff_take_eq_drop {α : Type*} {w : List α} {k : ℕ} :
    IsProperBorderLen w k ↔ k < w.length ∧ w.take k = w.drop (w.length - k) := by
  constructor
  · rintro ⟨hk, s, hs⟩
    refine ⟨hk, ?_⟩
    have hslen : s.length = w.length - k := by
      have hlen := congrArg List.length hs
      simp only [List.length_append, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at hlen
      omega
    have hdrop : (s ++ w.take k).drop s.length = w.take k := List.drop_left
    rw [hs, hslen] at hdrop
    exact hdrop.symm
  · rintro ⟨hk, heq⟩
    exact ⟨hk, heq ▸ List.drop_suffix (w.length - k) w⟩

theorem isProperBorderLen_iff_exists_border {α : Type*} {w : List α} {k : ℕ} :
    IsProperBorderLen w k ↔
      ∃ b : List α, b.length = k ∧ b.length < w.length ∧ b <+: w ∧ b <:+ w := by
  constructor
  · rintro ⟨hk, hsuf⟩
    refine ⟨w.take k, ?_, ?_, List.take_prefix k w, hsuf⟩ <;>
      simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt hk), hk]
  · rintro ⟨b, rfl, hk, hpref, hsuf⟩
    have htake : b = w.take b.length := List.prefix_iff_eq_take.mp hpref
    exact ⟨hk, htake ▸ hsuf⟩

/-- Border-period duality: `k < w.length` is a proper border length of `w` iff `w.length - k` is
a period of `w`. -/
theorem isProperBorderLen_iff_isPeriod {α : Type*} {w : List α} {k : ℕ} :
    IsProperBorderLen w k ↔ k < w.length ∧ IsPeriod w (w.length - k) := by
  rw [isProperBorderLen_iff_take_eq_drop]
  constructor
  · rintro ⟨hk, heq⟩
    refine ⟨hk, fun i hi => ?_⟩
    have hik : i < k := by omega
    have h1 : (w.take k)[i]'(by simp only [List.length_take]; omega) = w[i]'(by omega) :=
      List.getElem_take
    have h2 : (w.drop (w.length - k))[i]'(by simp only [List.length_drop]; omega) =
        w[w.length - k + i]'(by omega) :=
      List.getElem_drop
    have heq_i : (w.take k)[i]'(by simp only [List.length_take]; omega) =
        (w.drop (w.length - k))[i]'(by simp only [List.length_drop]; omega) := by
      simp only [heq]
    have hidx : w.length - k + i = i + (w.length - k) := Nat.add_comm _ _
    rw [← h1, heq_i, h2]
    simp only [hidx]
  · rintro ⟨hk, hper⟩
    refine ⟨hk, List.ext_getElem ?_ fun i h1 h2 => ?_⟩
    · simp only [List.length_take, List.length_drop]
      omega
    · simp only [List.length_take] at h1
      have hik : i < k := by omega
      rw [List.getElem_take, List.getElem_drop]
      have hidx : w.length - k + i = i + (w.length - k) := Nat.add_comm _ _
      simpa only [hidx] using hper i (by omega)

/-- A proper border of a proper border of `w` is itself a proper border of `w`. -/
theorem IsProperBorderLen.trans {α : Type*} {w : List α} {j k : ℕ}
    (hjk : IsProperBorderLen (w.take k) j) (hkw : IsProperBorderLen w k) :
    IsProperBorderLen w j := by
  rcases hkw with ⟨hk, hsufk⟩
  rcases hjk with ⟨hj, hsufj⟩
  simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at hj
  rw [List.take_take, Nat.min_eq_left (Nat.le_of_lt hj)] at hsufj
  exact ⟨Nat.lt_trans hj hk, hsufj.trans hsufk⟩

/-- Any proper border of `w` strictly shorter than a proper border `k` of `w` is a proper border
of `w.take k`. -/
theorem IsProperBorderLen.to_take {α : Type*} {w : List α} {j k : ℕ}
    (hjw : IsProperBorderLen w j) (hkw : IsProperBorderLen w k) (hlt : j < k) :
    IsProperBorderLen (w.take k) j := by
  rcases hjw with ⟨hj, hsufj⟩
  rcases hkw with ⟨hk, hsufk⟩
  refine ⟨by simp only [List.length_take]; omega, ?_⟩
  rw [List.take_take, Nat.min_eq_left (Nat.le_of_lt hlt)]
  exact List.suffix_of_suffix_length_le hsufj hsufk (by simp only [List.length_take]; omega)

/-! ## Maximum prefix-suffix lengths, maximum borders, and minimum periods -/

/-- Largest length `k ≤ B` with `k ≤ p.length` such that `p.take k <:+ t`. -/
@[expose] def maxPrefixSuffixUpTo {α : Type*} [DecidableEq α] (p t : List α) : ℕ → ℕ
  | 0 => 0
  | B + 1 =>
    if B + 1 ≤ p.length ∧ p.take (B + 1) <:+ t then B + 1
    else maxPrefixSuffixUpTo p t B

theorem maxPrefixSuffixUpTo_le_bound {α : Type*} [DecidableEq α] (p t : List α) (B : ℕ) :
    maxPrefixSuffixUpTo p t B ≤ B := by
  induction B with
  | zero => exact Nat.le_refl 0
  | succ B ih =>
    simp only [maxPrefixSuffixUpTo]
    split_ifs
    · exact Nat.le_refl (B + 1)
    · exact Nat.le_succ_of_le ih

theorem maxPrefixSuffixUpTo_le_length {α : Type*} [DecidableEq α] (p t : List α) (B : ℕ) :
    maxPrefixSuffixUpTo p t B ≤ p.length := by
  induction B with
  | zero => exact Nat.zero_le _
  | succ B ih =>
    simp only [maxPrefixSuffixUpTo]
    split_ifs with h
    · exact h.1
    · exact ih

theorem take_maxPrefixSuffixUpTo_isSuffix {α : Type*} [DecidableEq α] (p t : List α) (B : ℕ) :
    p.take (maxPrefixSuffixUpTo p t B) <:+ t := by
  induction B with
  | zero => exact List.nil_suffix
  | succ B ih =>
    simp only [maxPrefixSuffixUpTo]
    split_ifs with h
    · exact h.2
    · exact ih

theorem le_maxPrefixSuffixUpTo {α : Type*} [DecidableEq α] {p t : List α} {B k : ℕ}
    (hkB : k ≤ B) (hkp : k ≤ p.length) (hsuf : p.take k <:+ t) :
    k ≤ maxPrefixSuffixUpTo p t B := by
  induction B with
  | zero => omega
  | succ B ih =>
    simp only [maxPrefixSuffixUpTo]
    split_ifs with h
    · exact hkB
    · have hklt : k ≤ B := by
        rcases Nat.eq_or_lt_of_le hkB with rfl | hlt
        · exact False.elim (h ⟨hkp, hsuf⟩)
        · omega
      exact ih hklt

theorem eq_maxPrefixSuffixUpTo_iff {α : Type*} [DecidableEq α] {p t : List α} {B m : ℕ} :
    m = maxPrefixSuffixUpTo p t B ↔
      m ≤ B ∧ m ≤ p.length ∧ p.take m <:+ t ∧
        ∀ k, m < k → k ≤ B → k ≤ p.length → ¬ (p.take k <:+ t) := by
  constructor
  · rintro rfl
    refine ⟨maxPrefixSuffixUpTo_le_bound p t B, maxPrefixSuffixUpTo_le_length p t B,
      take_maxPrefixSuffixUpTo_isSuffix p t B, fun k hlt hkB hkp hsuf => ?_⟩
    have hle := le_maxPrefixSuffixUpTo hkB hkp hsuf
    omega
  · rintro ⟨hmB, hmp, hmsuf, hmax⟩
    have hle := le_maxPrefixSuffixUpTo hmB hmp hmsuf
    have hge : maxPrefixSuffixUpTo p t B ≤ m := by
      by_contra hlt
      exact hmax (maxPrefixSuffixUpTo p t B) (by omega)
        (maxPrefixSuffixUpTo_le_bound p t B)
        (maxPrefixSuffixUpTo_le_length p t B)
        (take_maxPrefixSuffixUpTo_isSuffix p t B)
    omega

/-- Maximum proper border length of `w` (`0` when `w = []`). -/
@[expose] def maxBorderLen {α : Type*} [DecidableEq α] (w : List α) : ℕ :=
  maxPrefixSuffixUpTo w w (w.length - 1)

/-- Minimum positive period of a nonempty word `w` (`0` when `w = []`). -/
@[expose] def minPeriod {α : Type*} [DecidableEq α] (w : List α) : ℕ :=
  w.length - maxBorderLen w

/-- The KMP prefix function $\pi[q]$: maximum proper border length of the prefix `p.take q`. -/
@[expose] def borderLen {α : Type*} [DecidableEq α] (p : List α) (q : ℕ) : ℕ :=
  maxBorderLen (p.take q)

@[simp]
theorem maxBorderLen_nil {α : Type*} [DecidableEq α] : maxBorderLen ([] : List α) = 0 := rfl

@[simp]
theorem maxBorderLen_singleton {α : Type*} [DecidableEq α] (a : α) : maxBorderLen [a] = 0 := rfl

theorem maxBorderLen_le_pred {α : Type*} [DecidableEq α] (w : List α) :
    maxBorderLen w ≤ w.length - 1 :=
  maxPrefixSuffixUpTo_le_bound w w (w.length - 1)

theorem maxBorderLen_lt_length {α : Type*} [DecidableEq α] {w : List α} (hw : 0 < w.length) :
    maxBorderLen w < w.length := by
  have h := maxBorderLen_le_pred w
  omega

theorem isProperBorderLen_maxBorderLen {α : Type*} [DecidableEq α] {w : List α}
    (hw : 0 < w.length) : IsProperBorderLen w (maxBorderLen w) :=
  ⟨maxBorderLen_lt_length hw, take_maxPrefixSuffixUpTo_isSuffix w w (w.length - 1)⟩

theorem le_maxBorderLen_of_isProperBorderLen {α : Type*} [DecidableEq α] {w : List α} {k : ℕ}
    (h : IsProperBorderLen w k) : k ≤ maxBorderLen w :=
  le_maxPrefixSuffixUpTo (by have := h.1; omega) (Nat.le_of_lt h.1) h.2

theorem minPeriod_add_maxBorderLen {α : Type*} [DecidableEq α] (w : List α) :
    minPeriod w + maxBorderLen w = w.length := by
  have h := maxBorderLen_le_pred w
  unfold minPeriod
  omega

theorem minPeriod_pos {α : Type*} [DecidableEq α] {w : List α} (hw : 0 < w.length) :
    0 < minPeriod w := by
  have h := maxBorderLen_lt_length hw
  unfold minPeriod
  omega

theorem isPeriod_minPeriod {α : Type*} [DecidableEq α] {w : List α} (hw : 0 < w.length) :
    IsPeriod w (minPeriod w) :=
  (isProperBorderLen_iff_isPeriod.mp (isProperBorderLen_maxBorderLen hw)).2

theorem minPeriod_le_of_isPeriod {α : Type*} [DecidableEq α] {w : List α} {d : ℕ}
    (hd0 : 0 < d) (hper : IsPeriod w d) :
    minPeriod w ≤ d := by
  by_cases hdlen : d ≤ w.length
  · have hborder : IsProperBorderLen w (w.length - d) := by
      rw [isProperBorderLen_iff_isPeriod]
      refine ⟨by omega, ?_⟩
      have heq : w.length - (w.length - d) = d := by omega
      simpa only [heq] using hper
    have hle := le_maxBorderLen_of_isProperBorderLen hborder
    unfold minPeriod
    omega
  · have h := maxBorderLen_le_pred w
    unfold minPeriod
    omega

@[simp]
theorem borderLen_zero {α : Type*} [DecidableEq α] (p : List α) : borderLen p 0 = 0 := rfl

@[simp]
theorem borderLen_one {α : Type*} [DecidableEq α] (p : List α) : borderLen p 1 = 0 := by
  cases p <;> rfl

theorem borderLen_lt {α : Type*} [DecidableEq α] {p : List α} {q : ℕ}
    (hq : 0 < q) (hp : p ≠ []) : borderLen p q < q := by
  have hlen : 0 < (p.take q).length := by
    cases p with
    | nil => exact False.elim (hp rfl)
    | cons _ _ => simp only [List.length_take, List.length_cons]; omega
  have hlt := maxBorderLen_lt_length hlen
  have htake_le : (p.take q).length ≤ q := List.length_take_le q p
  exact Nat.lt_of_lt_of_le hlt htake_le

theorem borderLen_eq_maxPrefixSuffixUpTo {α : Type*} [DecidableEq α] {p : List α} {q : ℕ}
    (hqp : q ≤ p.length) :
    borderLen p q = maxPrefixSuffixUpTo p (p.take q) (q - 1) := by
  apply eq_maxPrefixSuffixUpTo_iff.mpr
  have hlen : (p.take q).length = q := List.length_take_of_le hqp
  rcases Nat.eq_zero_or_pos q with rfl | hqpos
  · simp only [borderLen_zero, Nat.zero_le, List.take_zero, List.nil_suffix, true_and]
    intro k hk0 hkB
    omega
  · have hb : IsProperBorderLen (p.take q) (borderLen p q) :=
      isProperBorderLen_maxBorderLen (by rw [hlen]; exact hqpos)
    have hble : borderLen p q ≤ q - 1 := by
      have := hb.1
      rw [hlen] at this
      omega
    have htake_eq : p.take (borderLen p q) = (p.take q).take (borderLen p q) := by
      rw [List.take_take, Nat.min_eq_left (by omega)]
    refine ⟨hble, by omega, htake_eq ▸ hb.2, fun k hlt hkB _ hsuf => ?_⟩
    have hk_proper : IsProperBorderLen (p.take q) k := by
      refine ⟨by rw [hlen]; omega, ?_⟩
      rw [List.take_take, Nat.min_eq_left (by omega)]
      exact hsuf
    have hle := le_maxBorderLen_of_isProperBorderLen hk_proper
    change k ≤ borderLen p q at hle
    omega

/-! ## Prefix-function iteration (`[CLRS2009]`, Lemma 32.5) -/

/-- Strictly decreasing list of all proper border lengths of `p.take q` (empty when `q = 0` or
`p = []`), computed by iterating `k ↦ borderLen p k` (`[CLRS2009]`, Lemma 32.5). -/
def borderChain {α : Type*} [DecidableEq α] (p : List α) (q : ℕ) : List ℕ :=
  if _h : q = 0 ∨ p = [] then []
  else
    let k := borderLen p q
    if k = 0 then [0]
    else k :: borderChain p k
termination_by q
decreasing_by
  have hq : 0 < q := by omega
  have hp : p ≠ [] := fun hp0 => _h (Or.inr hp0)
  exact borderLen_lt hq hp

/-- Prefix-function iteration theorem (`[CLRS2009]`, Lemma 32.5): for `1 ≤ q ≤ p.length`,
`borderChain p q` contains exactly the proper border lengths of `p.take q`. -/
theorem mem_borderChain_iff {α : Type*} [DecidableEq α] {p : List α} {q j : ℕ}
    (hq1 : 1 ≤ q) (hqp : q ≤ p.length) :
    j ∈ borderChain p q ↔ IsProperBorderLen (p.take q) j := by
  induction q using Nat.strongRecOn with
  | ind q ih =>
    have hp : p ≠ [] := by
      rintro rfl
      simp only [List.length_nil] at hqp
      omega
    have hcond : ¬ (q = 0 ∨ p = []) := by
      rintro (rfl | hp0)
      · omega
      · exact hp hp0
    have hlen : (p.take q).length = q := List.length_take_of_le hqp
    have hb_proper : IsProperBorderLen (p.take q) (borderLen p q) :=
      isProperBorderLen_maxBorderLen (by rw [hlen]; omega)
    rw [borderChain]
    simp only [hcond, ↓reduceDIte]
    split_ifs with hk0
    · simp only [List.mem_singleton]
      constructor
      · rintro rfl
        exact isProperBorderLen_zero (by rw [hlen]; omega)
      · intro hj
        have hle := le_maxBorderLen_of_isProperBorderLen hj
        change j ≤ borderLen p q at hle
        omega
    · have hklt : borderLen p q < q := borderLen_lt (by omega) hp
      have hk1 : 1 ≤ borderLen p q := by omega
      have hkp : borderLen p q ≤ p.length := by omega
      have htake_k : (p.take q).take (borderLen p q) = p.take (borderLen p q) := by
        rw [List.take_take, Nat.min_eq_left (Nat.le_of_lt hklt)]
      simp only [List.mem_cons, ih (borderLen p q) hklt hk1 hkp]
      constructor
      · rintro (rfl | hj)
        · exact hb_proper
        · exact (htake_k.symm ▸ hj).trans hb_proper
      · intro hj
        have hle : j ≤ borderLen p q := le_maxBorderLen_of_isProperBorderLen hj
        rcases Nat.eq_or_lt_of_le hle with rfl | hjlt
        · exact Or.inl rfl
        · exact Or.inr (htake_k ▸ hj.to_take hb_proper hjlt)

/-- `borderChain p q` lists proper border lengths in strictly decreasing order. -/
theorem pairwise_gt_borderChain {α : Type*} [DecidableEq α] {p : List α} {q : ℕ}
    (hqp : q ≤ p.length) :
    (borderChain p q).Pairwise (· > ·) := by
  induction q using Nat.strongRecOn with
  | ind q ih =>
    rw [borderChain]
    split_ifs with hcond
    · exact List.Pairwise.nil
    · dsimp only
      split_ifs with hk0
      · exact List.pairwise_singleton _ _
      · have hq0 : q ≠ 0 := fun hq0 => hcond (Or.inl hq0)
        have hp : p ≠ [] := fun hp0 => hcond (Or.inr hp0)
        have hq1 : 1 ≤ q := by omega
        have hklt : borderLen p q < q := borderLen_lt (by omega) hp
        have hk1 : 1 ≤ borderLen p q := by omega
        have hkp : borderLen p q ≤ p.length := by omega
        refine List.Pairwise.cons (fun j hj => ?_) (ih (borderLen p q) hklt hkp)
        have hj_proper := (mem_borderChain_iff hk1 hkp).mp hj
        have hjlen : j < (p.take (borderLen p q)).length := hj_proper.1
        rw [List.length_take_of_le hkp] at hjlen
        exact hjlen

/-! ## Pure KMP automaton transition and master step theorem -/

/-- Pure KMP transition: given a matched prefix length `k < p.length` (or `0` when `p = []`) and
input character `c`, falls back along `borderLen p` until matching `p[k] = c` or exhausting
borders. -/
@[expose] def nextLen {α : Type*} [DecidableEq α] (p : List α) (k : ℕ) (c : α) : ℕ :=
  if hk : k < p.length then
    if p[k]'hk = c then k + 1
    else if k = 0 then 0
    else nextLen p (borderLen p k) c
  else 0
termination_by k
decreasing_by
  have hp : p ≠ [] := by
    rintro rfl
    simp only [List.length_nil] at hk
    omega
  exact borderLen_lt (by omega) hp

theorem nextLen_le_succ {α : Type*} [DecidableEq α] (p : List α) (k : ℕ) (c : α) :
    nextLen p k c ≤ k + 1 := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    rw [nextLen]
    split_ifs with hk hmatch hk0
    · exact Nat.le_refl (k + 1)
    · exact Nat.zero_le _
    · have hp : p ≠ [] := by rintro rfl; simp only [List.length_nil] at hk; omega
      have hlt : borderLen p k < k := borderLen_lt (by omega) hp
      have hsub := ih (borderLen p k) hlt
      omega
    · exact Nat.zero_le _

theorem nextLen_le_length {α : Type*} [DecidableEq α] (p : List α) (k : ℕ) (c : α) :
    nextLen p k c ≤ p.length := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    rw [nextLen]
    split_ifs with hk hmatch hk0
    · omega
    · exact Nat.zero_le _
    · have hp : p ≠ [] := by rintro rfl; simp only [List.length_nil] at hk; omega
      exact ih (borderLen p k) (borderLen_lt (by omega) hp)
    · exact Nat.zero_le _

/-- Master KMP step theorem: for any bound `B < p.length` and word `t`, extending `t` by one
character `c` updates `maxPrefixSuffixUpTo p t B` via `nextLen p · c`. -/
theorem maxPrefixSuffixUpTo_append_singleton {α : Type*} [DecidableEq α]
    (p t : List α) (c : α) {B : ℕ} (hB : B < p.length) :
    maxPrefixSuffixUpTo p (t ++ [c]) (B + 1) =
      nextLen p (maxPrefixSuffixUpTo p t B) c := by
  set k := maxPrefixSuffixUpTo p t B
  have hkB : k ≤ B := maxPrefixSuffixUpTo_le_bound p t B
  have hkp : k < p.length := Nat.lt_of_le_of_lt hkB hB
  have hksuf : p.take k <:+ t := take_maxPrefixSuffixUpTo_isSuffix p t B
  have h_valid_iff : ∀ j, j ≤ B ∧ p.take j <:+ t ↔ j = k ∨ IsProperBorderLen (p.take k) j := by
    intro j
    constructor
    · rintro ⟨hjB, hjsuf⟩
      have hjk : j ≤ k := le_maxPrefixSuffixUpTo (B := B) hjB (by omega) hjsuf
      rcases Nat.eq_or_lt_of_le hjk with rfl | hjlt
      · exact Or.inl rfl
      · right
        refine ⟨by rw [List.length_take_of_le (Nat.le_of_lt hkp)]; exact hjlt, ?_⟩
        rw [List.take_take, Nat.min_eq_left (Nat.le_of_lt hjlt)]
        exact List.suffix_of_suffix_length_le hjsuf hksuf (by simp only [List.length_take]; omega)
    · rintro (rfl | hjprop)
      · exact ⟨hkB, hksuf⟩
      · have hjlt : j < k := by
          have := hjprop.1
          rwa [List.length_take_of_le (Nat.le_of_lt hkp)] at this
        have hjsuf_k : p.take j <:+ p.take k := by
          have := hjprop.2
          rwa [List.take_take, Nat.min_eq_left (Nat.le_of_lt hjlt)] at this
        exact ⟨by omega, hjsuf_k.trans hksuf⟩
  suffices hrec : ∀ m, m < p.length →
      nextLen p m c = maxPrefixSuffixUpTo p (p.take m ++ [c]) (m + 1) by
    rw [hrec k hkp]
    symm
    apply eq_maxPrefixSuffixUpTo_iff.mpr
    have hiff_pos : ∀ j, j ≤ B →
        (p.take (j + 1) <:+ t ++ [c] ↔ j ≤ k ∧ p.take (j + 1) <:+ p.take k ++ [c]) := by
      intro j hjB
      rw [take_succ_isSuffix_append_iff (by omega), take_succ_isSuffix_append_iff (by omega)]
      constructor
      · rintro ⟨hjt, hjc⟩
        rcases (h_valid_iff j).mp ⟨hjB, hjt⟩ with rfl | hjprop
        · exact ⟨Nat.le_refl k, List.suffix_rfl, hjc⟩
        · have hjlt : j < k := by
            have := hjprop.1
            rwa [List.length_take_of_le (Nat.le_of_lt hkp)] at this
          have hjsuf_k : p.take j <:+ p.take k := by
            have := hjprop.2
            rwa [List.take_take, Nat.min_eq_left (Nat.le_of_lt hjlt)] at this
          exact ⟨Nat.le_of_lt hjlt, hjsuf_k, hjc⟩
      · rintro ⟨hjk, hjsuf_k, hjc⟩
        exact ⟨hjsuf_k.trans hksuf, hjc⟩
    set u := maxPrefixSuffixUpTo p (p.take k ++ [c]) (k + 1)
    have hu_le : u ≤ k + 1 := maxPrefixSuffixUpTo_le_bound p (p.take k ++ [c]) (k + 1)
    have hu_p : u ≤ p.length := maxPrefixSuffixUpTo_le_length p (p.take k ++ [c]) (k + 1)
    have hu_suf : p.take u <:+ p.take k ++ [c] :=
      take_maxPrefixSuffixUpTo_isSuffix p (p.take k ++ [c]) (k + 1)
    refine ⟨by omega, hu_p, ?_, fun s hslt hs_le hsp hssuf => ?_⟩
    · rcases Nat.eq_zero_or_pos u with hu0 | hupos
      · rw [hu0]; exact List.nil_suffix
      · obtain ⟨j, hj⟩ : ∃ j, u = j + 1 := ⟨u - 1, by omega⟩
        rw [hj] at hu_suf ⊢
        exact (hiff_pos j (by omega)).mpr ⟨by omega, hu_suf⟩
    · rcases Nat.eq_zero_or_pos s with rfl | hspos
      · omega
      · obtain ⟨j, rfl⟩ : ∃ j, s = j + 1 := ⟨s - 1, by omega⟩
        have hjk_suf := (hiff_pos j (by omega)).mp hssuf
        have hle := le_maxPrefixSuffixUpTo (B := k + 1) (by omega) hsp hjk_suf.2
        change j + 1 ≤ u at hle
        omega
  intro m hm
  induction m using Nat.strongRecOn with
  | ind m ih =>
    rw [nextLen]
    simp only [hm, ↓reduceDIte]
    split_ifs with hmatch hm0
    · apply eq_maxPrefixSuffixUpTo_iff.mpr
      refine ⟨Nat.le_refl _, by omega, ?_, fun s hslt hs_le _ _ => by omega⟩
      rw [take_succ_isSuffix_append_iff hm]
      exact ⟨List.suffix_rfl, hmatch⟩
    · subst hm0
      apply eq_maxPrefixSuffixUpTo_iff.mpr
      refine ⟨Nat.zero_le _, Nat.zero_le _, List.nil_suffix, fun s hslt hs_le hsp hssuf => ?_⟩
      have hs1 : s = 1 := by omega
      subst hs1
      rw [take_succ_isSuffix_append_iff hm] at hssuf
      exact hmatch hssuf.2
    · have hp : p ≠ [] := by rintro rfl; simp only [List.length_nil] at hm; omega
      have hblt : borderLen p m < m := borderLen_lt (by omega) hp
      rw [ih (borderLen p m) hblt (by omega)]
      set b := borderLen p m
      have hb_eq : b = maxPrefixSuffixUpTo p (p.take m) (m - 1) :=
        borderLen_eq_maxPrefixSuffixUpTo (Nat.le_of_lt hm)
      have hbsuf : p.take b <:+ p.take m :=
        hb_eq ▸ take_maxPrefixSuffixUpTo_isSuffix p (p.take m) (m - 1)
      apply eq_maxPrefixSuffixUpTo_iff.mpr
      set u := maxPrefixSuffixUpTo p (p.take b ++ [c]) (b + 1)
      have hu_le : u ≤ b + 1 := maxPrefixSuffixUpTo_le_bound p (p.take b ++ [c]) (b + 1)
      have hu_p : u ≤ p.length := maxPrefixSuffixUpTo_le_length p (p.take b ++ [c]) (b + 1)
      have hu_suf : p.take u <:+ p.take b ++ [c] :=
        take_maxPrefixSuffixUpTo_isSuffix p (p.take b ++ [c]) (b + 1)
      refine ⟨by omega, hu_p, ?_, fun s hslt hs_le hsp hssuf => ?_⟩
      · rcases Nat.eq_zero_or_pos u with hu0 | hupos
        · rw [hu0]; exact List.nil_suffix
        · obtain ⟨j, hj⟩ : ∃ j, u = j + 1 := ⟨u - 1, by omega⟩
          rw [hj] at hu_suf ⊢
          rw [take_succ_isSuffix_append_iff (by omega)] at hu_suf ⊢
          exact ⟨hu_suf.1.trans hbsuf, hu_suf.2⟩
      · rcases Nat.eq_zero_or_pos s with rfl | hspos
        · omega
        · obtain ⟨j, rfl⟩ : ∃ j, s = j + 1 := ⟨s - 1, by omega⟩
          rw [take_succ_isSuffix_append_iff (by omega)] at hssuf
          have hjm : j ≠ m := fun hjeq => hmatch (hjeq ▸ hssuf.2)
          have hj_le_m1 : j ≤ m - 1 := by omega
          have hjb : j ≤ b :=
            hb_eq ▸ le_maxPrefixSuffixUpTo (B := m - 1) hj_le_m1 (by omega) hssuf.1
          have hjsuf_b : p.take j <:+ p.take b :=
            List.suffix_of_suffix_length_le hssuf.1 hbsuf (by simp only [List.length_take]; omega)
          have hj1_suf_b : p.take (j + 1) <:+ p.take b ++ [c] :=
            (take_succ_isSuffix_append_iff (by omega)).mpr ⟨hjsuf_b, hssuf.2⟩
          have hle := le_maxPrefixSuffixUpTo (B := b + 1) (by omega) hsp hj1_suf_b
          change j + 1 ≤ u at hle
          omega

/-- Recurrence for the KMP prefix function (`[CLRS2009]`, Lemma 32.6 and Corollary 32.7): for
`1 ≤ q < p.length`, `borderLen p (q + 1) = nextLen p (borderLen p q) p[q]`. -/
theorem borderLen_succ {α : Type*} [DecidableEq α] {p : List α} {q : ℕ}
    (hq1 : 1 ≤ q) (hqp : q < p.length) :
    borderLen p (q + 1) = nextLen p (borderLen p q) (p[q]'hqp) := by
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  have h1 : borderLen p (r + 1 + 1) = maxPrefixSuffixUpTo p (p.take (r + 1 + 1)) (r + 1) :=
    borderLen_eq_maxPrefixSuffixUpTo (Nat.succ_le_of_lt hqp)
  have h2 : borderLen p (r + 1) = maxPrefixSuffixUpTo p (p.take (r + 1)) r :=
    borderLen_eq_maxPrefixSuffixUpTo (Nat.le_of_lt hqp)
  have htake : p.take (r + 1 + 1) = p.take (r + 1) ++ [p[r + 1]'hqp] := by
    rw [List.take_add_one, getElem?_pos p (r + 1) hqp, Option.toList_some]
  rw [h1, htake, maxPrefixSuffixUpTo_append_singleton p (p.take (r + 1)) (p[r + 1]'hqp) (by omega),
    ← h2]

/-- Resetting a full pattern match `m = p.length` (`0 < p.length`) to `borderLen p p.length`
recovers the longest proper prefix of `p` that is a suffix of `t`. -/
theorem maxPrefixSuffixUpTo_pred_of_eq_length {α : Type*} [DecidableEq α]
    {p t : List α} (_hp : 0 < p.length)
    (hfull : maxPrefixSuffixUpTo p t p.length = p.length) :
    maxPrefixSuffixUpTo p t (p.length - 1) = borderLen p p.length := by
  have hpsuf : p <:+ t := by
    have h := take_maxPrefixSuffixUpTo_isSuffix p t p.length
    rwa [hfull, List.take_length] at h
  have hb : borderLen p p.length = maxPrefixSuffixUpTo p p (p.length - 1) := by
    simp only [borderLen, maxBorderLen, List.take_length]
  rw [hb]
  symm
  apply eq_maxPrefixSuffixUpTo_iff.mpr
  set b := maxPrefixSuffixUpTo p p (p.length - 1)
  refine ⟨maxPrefixSuffixUpTo_le_bound p p (p.length - 1),
    maxPrefixSuffixUpTo_le_length p p (p.length - 1),
    (take_maxPrefixSuffixUpTo_isSuffix p p (p.length - 1)).trans hpsuf,
    fun k hlt hkB hkp hsuf => ?_⟩
  have hksuf_p : p.take k <:+ p :=
    List.suffix_of_suffix_length_le hsuf hpsuf (by simp only [List.length_take]; omega)
  have hle := le_maxPrefixSuffixUpTo (B := p.length - 1) hkB hkp hksuf_p
  change k ≤ b at hle
  omega

/-- When `maxPrefixSuffixUpTo p t p.length < p.length`, restricting the bound to `p.length - 1`
leaves the value unchanged. -/
theorem maxPrefixSuffixUpTo_pred_of_lt_length {α : Type*} [DecidableEq α]
    {p t : List α} (hlt : maxPrefixSuffixUpTo p t p.length < p.length) :
    maxPrefixSuffixUpTo p t (p.length - 1) = maxPrefixSuffixUpTo p t p.length := by
  set m := maxPrefixSuffixUpTo p t p.length
  symm
  apply eq_maxPrefixSuffixUpTo_iff.mpr
  refine ⟨by omega, maxPrefixSuffixUpTo_le_length p t p.length,
    take_maxPrefixSuffixUpTo_isSuffix p t p.length, fun k hklt hkB hkp hsuf => ?_⟩
  have hle := le_maxPrefixSuffixUpTo (B := p.length) (by omega) hkp hsuf
  change k ≤ m at hle
  omega

end Cslib.Algorithms.Lean.KMP
