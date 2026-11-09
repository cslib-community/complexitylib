/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.BinarySearch
public import CslibFrontier.Algorithms.Lean.SuffixArray.Basic
public import Cslib.Algorithms.Lean.TimeM
import CslibFrontier.Foundations.Data.List.Lex

/-!
# Pattern search in a suffix array

The suffixes of `w` that start with a pattern `p` occupy a contiguous range of ranks in the suffix
array, because the words with prefix `p` form an interval of the lexicographic order. Two binary
searches over `sa` find the endpoints of that range (the plain search of `[ManberMyers1993]`,
without LCP information), comparing `p` with at most `|p|` characters of a suffix per probe.

## Source Conventions

* **Result:** `search w sa p = (lo, hi)` is the half-open rank interval `[lo, hi)`; the
  occurrences of `p` are the positions `sa[lo], …, sa[hi - 1]`, listed in suffix order rather than
  text order.
* **Empty pattern:** `p = []` returns `(0, |w|)`, every position `i < |w|`. Unlike
  `Cslib.Algorithms.Lean.KMP.kmpMatchesList`, the position `|w|` of the empty suffix is not
  reported, since the suffix array does not list it.
* **Resource bounds:** `TimeM ℕ` counts exact character comparisons. The search makes at most
  `2 * |p| * (⌊log₂ |sa|⌋ + 1)` of them, the source's `O(|p| log |w|)` bound for the plain
  search. The source's `O(|p| + log |w|)` search, which reuses LCP information between probes, is
  not formalized.

## Cost Model

* **Charged (`1` `TimeM` tick):** every three-way character comparison `compare a w[i]` in
  `cmpSuffixM`.
* **Uncharged (`0` `TimeM` ticks):** index arithmetic and loop control in the binary search,
  array reads (`sa[r]!`, `w[i]`), the bounds check `i < w.size`, and the conversions in the list
  wrappers `search` and `occurrences`.

## Main definitions

* `Cslib.Algorithms.Lean.SuffixArray.cmpSuffixM`: compare `p` with a suffix of `w`, up to `|p|`
  characters.
* `Cslib.Algorithms.Lean.SuffixArray.searchM`, `search`: the rank interval of the suffixes
  starting with `p`.
* `Cslib.Algorithms.Lean.SuffixArray.occurrences`: the positions of the occurrences of `p`.

## Main results

* `Cslib.Algorithms.Lean.SuffixArray.ret_cmpSuffixM`: `cmpSuffixM w p i` compares `p` with
  `(w.drop i).take |p|`.
* `Cslib.Algorithms.Lean.SuffixArray.searchM_spec` and `search_spec`: on a suffix array, the
  suffix of rank `r` starts with `p` iff `lo ≤ r < hi`.
* `Cslib.Algorithms.Lean.SuffixArray.mem_occurrences`: `i ∈ occurrences w sa p` iff `i < |w|` and
  `p` occurs in `w` at position `i`.
* `Cslib.Algorithms.Lean.SuffixArray.searchM_time_le`: at most `2 * |p| * (⌊log₂ |sa|⌋ + 1)`
  character comparisons.

## References

* [U. Manber and G. Myers, *Suffix Arrays: A New Method for On-Line String
  Searches*][ManberMyers1993]
-/

public section

namespace Cslib.Algorithms.Lean.SuffixArray

open Cslib.Algorithms.Lean

variable {α : Type*}

/-! ## Comparing a pattern with a suffix -/

section Compare

variable [LinearOrder α]

/-- Compare the pattern `p` with the first `|p|` characters of the suffix of `w` at position
`i`, charging one tick per character comparison. -/
def cmpSuffixM (w : Array α) : List α → ℕ → TimeM ℕ Ordering
  | [], _ => return .eq
  | a :: p, i =>
    if hi : i < w.size then do
      ✓ match compare a w[i] with
        | .lt => return .lt
        | .gt => return .gt
        | .eq => cmpSuffixM w p (i + 1)
    else
      return .gt

/-- `cmpSuffixM w p i` makes at most `|p|` character comparisons. -/
theorem cmpSuffixM_time_le (w : Array α) (p : List α) (i : ℕ) :
    (cmpSuffixM w p i).time ≤ p.length := by
  induction p generalizing i with
  | nil => simp only [cmpSuffixM, TimeM.time_pure, List.length_nil, le_refl]
  | cons a p ih =>
    rw [cmpSuffixM]
    split_ifs with hi
    · simp only [TimeM.time_bind, TimeM.time_tick, List.length_cons]
      split
      · simp only [TimeM.time_pure]; omega
      · simp only [TimeM.time_pure]; omega
      · have := ih (i + 1); omega
    · simp only [TimeM.time_pure, Nat.zero_le]

/-- `cmpSuffixM w p i` compares `p` with the window `(w.drop i).take |p|` of the same length as
`p` (shorter if the suffix is shorter). -/
theorem ret_cmpSuffixM (w : Array α) (p : List α) (i : ℕ) :
    (cmpSuffixM w p i).ret =
      if p < (w.toList.drop i).take p.length then .lt
      else if p = (w.toList.drop i).take p.length then .eq else .gt := by
  induction p generalizing i with
  | nil =>
    simp only [cmpSuffixM, TimeM.ret_pure, List.length_nil, List.take_zero, lt_self_iff_false,
      ↓reduceIte]
  | cons a p ih =>
    rw [cmpSuffixM]
    by_cases hi : i < w.size
    · simp only [hi, ↓reduceDIte]
      rw [List.drop_eq_getElem_cons (i := i) (l := w.toList) (by simpa using hi),
        List.length_cons, List.take_succ_cons, Array.getElem_toList]
      simp only [TimeM.ret_bind]
      rcases lt_trichotomy a w[i] with h | h | h
      · rw [compare_lt_iff_lt.mpr h]
        simp only [show a :: p < w[i] :: (w.toList.drop (i + 1)).take p.length from
          List.Lex.rel h, ↓reduceIte]
        rfl
      · rw [compare_eq_iff_eq.mpr h]
        have e1 : a :: p < w[i] :: (w.toList.drop (i + 1)).take p.length ↔
            p < (w.toList.drop (i + 1)).take p.length := by
          rw [← h]; exact List.lex_cons_iff
        have e2 : a :: p = w[i] :: (w.toList.drop (i + 1)).take p.length ↔
            p = (w.toList.drop (i + 1)).take p.length := by
          rw [← h]; exact List.cons_inj_right a
        simp only [e1, e2]
        exact ih (i + 1)
      · rw [compare_gt_iff_gt.mpr h]
        have e1 : ¬ a :: p < w[i] :: (w.toList.drop (i + 1)).take p.length :=
          not_lt_of_gt (List.Lex.rel h)
        have e2 : a :: p ≠ w[i] :: (w.toList.drop (i + 1)).take p.length :=
          fun e => ne_of_gt h (List.cons.inj e).1
        simp only [e1, e2, ↓reduceIte]
        rfl
    · simp only [hi, ↓reduceDIte]
      rw [List.drop_eq_nil_of_le (by simpa using hi), List.take_nil]
      have e1 : ¬ a :: p < [] := not_lt_of_gt List.Lex.nil
      simp only [TimeM.ret_pure, e1, reduceCtorEq, ↓reduceIte]

/-- `cmpSuffixM` reports `.gt` iff the window of the suffix is below `p`. -/
theorem ret_cmpSuffixM_eq_gt_iff (w : Array α) (p : List α) (i : ℕ) :
    (cmpSuffixM w p i).ret = .gt ↔ (w.toList.drop i).take p.length < p := by
  rw [ret_cmpSuffixM]
  split_ifs with h1 h2
  · simp only [false_iff, not_lt]
    exact le_of_lt h1
  · simp only [false_iff, not_lt]
    exact le_of_eq h2
  · simp only [true_iff]
    exact lt_of_le_of_ne (not_lt.mp h1) (Ne.symm h2)

/-- `cmpSuffixM` reports `.eq` or `.gt` iff the window of the suffix is at most `p`. -/
theorem ret_cmpSuffixM_ne_lt_iff (w : Array α) (p : List α) (i : ℕ) :
    (cmpSuffixM w p i).ret ≠ .lt ↔ (w.toList.drop i).take p.length ≤ p := by
  rw [ret_cmpSuffixM]
  split_ifs with h1 h2
  · simp only [ne_eq, not_true_eq_false, false_iff, not_le]
    exact h1
  · simp only [ne_eq, reduceCtorEq, not_false_eq_true, true_iff]
    exact le_of_eq h2.symm
  · simp only [ne_eq, reduceCtorEq, not_false_eq_true, true_iff]
    exact not_lt.mp h1

/-- `cmpSuffixM` reports `.eq` iff `p` is a prefix of the suffix. -/
theorem ret_cmpSuffixM_eq_eq_iff (w : Array α) (p : List α) (i : ℕ) :
    (cmpSuffixM w p i).ret = .eq ↔ p <+: w.toList.drop i := by
  rw [ret_cmpSuffixM, List.prefix_iff_eq_take]
  split_ifs with h1 h2
  · simp only [false_iff]
    exact ne_of_lt h1
  · simp only [true_iff]
    exact h2
  · simp only [false_iff]
    exact h2

end Compare

/-! ## Searching a suffix array -/

section Search

variable [LinearOrder α]

/-- Binary-search probe at rank `r`: is the `|p|`-window of the suffix of rank `r` below `p`? -/
def probeBelowM (w : Array α) (sa : Array ℕ) (p : List α) (r : ℕ) : TimeM ℕ Bool := do
  let c ← cmpSuffixM w p sa[r]!
  return decide (c = .gt)

/-- Binary-search probe at rank `r`: is the `|p|`-window of the suffix of rank `r` at most
`p`? -/
def probeAtMostM (w : Array α) (sa : Array ℕ) (p : List α) (r : ℕ) : TimeM ℕ Bool := do
  let c ← cmpSuffixM w p sa[r]!
  return decide (c ≠ .lt)

/-- Find the range of ranks whose suffixes start with `p`, by two binary searches over `sa`:
`lo` is the first rank whose suffix's `|p|`-window is not below `p`, and `hi` is the first rank
whose window is above `p`. -/
def searchM (w : Array α) (sa : Array ℕ) (p : List α) : TimeM ℕ (ℕ × ℕ) := do
  let lo ← lowerBoundM (probeBelowM w sa p) 0 sa.size
  let hi ← lowerBoundM (probeAtMostM w sa p) 0 sa.size
  return (lo, hi)

/-- The rank interval of suffixes of `w` starting with `p`. -/
def search (w : List α) (sa : List ℕ) (p : List α) : ℕ × ℕ :=
  (searchM w.toArray sa.toArray p).ret

/-- The starting positions of the occurrences of `p` in `w`, listed in suffix-array order. -/
def occurrences (w : List α) (sa : List ℕ) (p : List α) : List ℕ :=
  let r := search w sa p
  (sa.take r.2).drop r.1

/-- Binary search over the suffix array performs at most `2 * |p| * (⌊log₂ |sa|⌋ + 1)`
character comparisons. -/
theorem searchM_time_le (w : Array α) (sa : Array ℕ) (p : List α) :
    (searchM w sa p).time ≤ 2 * (p.length * (Nat.log 2 sa.size + 1)) := by
  have h1 := lowerBoundM_time_le (probeBelowM w sa p) (c := p.length) (fun r => by
    simp only [probeBelowM, TimeM.time_bind, TimeM.time_pure, Nat.add_zero]
    exact cmpSuffixM_time_le w p _) 0 sa.size
  have h2 := lowerBoundM_time_le (probeAtMostM w sa p) (c := p.length) (fun r => by
    simp only [probeAtMostM, TimeM.time_bind, TimeM.time_pure, Nat.add_zero]
    exact cmpSuffixM_time_le w p _) 0 sa.size
  simp only [searchM, TimeM.time_bind, TimeM.time_pure, Nat.add_zero, Nat.sub_zero] at h1 h2 ⊢
  omega

/-- Specification of the probe used to find the lower end of the rank interval. -/
theorem ret_probeBelowM (w : Array α) (sa : Array ℕ) (p : List α) {r : ℕ} (hr : r < sa.size) :
    (probeBelowM w sa p r).ret = true ↔ (w.toList.drop sa[r]).take p.length < p := by
  simp only [probeBelowM, TimeM.ret_bind, TimeM.ret_pure, decide_eq_true_eq]
  rw [getElem!_pos sa r hr]
  exact ret_cmpSuffixM_eq_gt_iff w p _

/-- Specification of the probe used to find the upper end of the rank interval. -/
theorem ret_probeAtMostM (w : Array α) (sa : Array ℕ) (p : List α) {r : ℕ} (hr : r < sa.size) :
    (probeAtMostM w sa p r).ret = true ↔ (w.toList.drop sa[r]).take p.length ≤ p := by
  simp only [probeAtMostM, TimeM.ret_bind, TimeM.ret_pure, decide_eq_true_eq]
  rw [getElem!_pos sa r hr]
  exact ret_cmpSuffixM_ne_lt_iff w p _

/-- On a suffix array, the `|p|`-windows of the suffixes are sorted by rank. -/
private theorem take_drop_le_take_drop {w : Array α} {sa : Array ℕ}
    (hsa : IsSuffixArray w.toList sa.toList) {r r' : ℕ} (hrr' : r ≤ r') (hr' : r' < sa.size)
    (n : ℕ) :
    (w.toList.drop (sa[r]'(by omega))).take n ≤ (w.toList.drop sa[r']).take n := by
  rcases Nat.lt_or_eq_of_le hrr' with hlt | rfl
  · have := hsa.drop_lt_drop (r := r) (r' := r') hlt (by simpa using hr')
    simp only [Array.getElem_toList] at this
    exact List.take_le_take_of_le (le_of_lt this) n
  · exact le_refl _

/-- **Correctness of suffix-array search**: on a suffix array, `searchM` returns ranks
`lo ≤ hi ≤ |sa|` such that the suffix of rank `r` starts with `p` exactly when `lo ≤ r < hi`. -/
theorem searchM_spec {w : Array α} {sa : Array ℕ} (hsa : IsSuffixArray w.toList sa.toList)
    (p : List α) :
    (searchM w sa p).ret.1 ≤ (searchM w sa p).ret.2 ∧ (searchM w sa p).ret.2 ≤ sa.size ∧
      ∀ (r : ℕ) (hr : r < sa.size),
        p <+: w.toList.drop sa[r] ↔ (searchM w sa p).ret.1 ≤ r ∧ r < (searchM w sa p).ret.2 := by
  simp only [searchM, TimeM.ret_bind, TimeM.ret_pure]
  obtain ⟨-, hlo2, hlo3, hlo4⟩ := lowerBoundM_spec (probeBelowM w sa p) (lo := 0) (hi := sa.size)
    (fun m m' _ hmm' hm' h => by
      rw [ret_probeBelowM w sa p (by omega)] at h ⊢
      exact lt_of_le_of_lt (take_drop_le_take_drop hsa hmm' hm' _) h)
  obtain ⟨-, hhi2, hhi3, hhi4⟩ := lowerBoundM_spec (probeAtMostM w sa p) (lo := 0)
    (hi := sa.size)
    (fun m m' _ hmm' hm' h => by
      rw [ret_probeAtMostM w sa p (by omega)] at h ⊢
      exact le_trans (take_drop_le_take_drop hsa hmm' hm' _) h)
  set lo := (lowerBoundM (probeBelowM w sa p) 0 sa.size).ret
  set hi := (lowerBoundM (probeAtMostM w sa p) 0 sa.size).ret
  have hbelow : ∀ (r : ℕ) (hr : r < sa.size),
      (w.toList.drop sa[r]).take p.length < p ↔ r < lo := by
    intro r hr
    refine ⟨fun h => ?_, fun h => (ret_probeBelowM w sa p hr).mp (hlo3 r (Nat.zero_le _) h)⟩
    by_contra hc
    have := hlo4 r (by omega) hr
    rw [← Bool.not_eq_true, ret_probeBelowM w sa p hr] at this
    exact this h
  have hatmost : ∀ (r : ℕ) (hr : r < sa.size),
      (w.toList.drop sa[r]).take p.length ≤ p ↔ r < hi := by
    intro r hr
    refine ⟨fun h => ?_, fun h => (ret_probeAtMostM w sa p hr).mp (hhi3 r (Nat.zero_le _) h)⟩
    by_contra hc
    have := hhi4 r (by omega) hr
    rw [← Bool.not_eq_true, ret_probeAtMostM w sa p hr] at this
    exact this h
  have hlohi : lo ≤ hi := by grind
  refine ⟨hlohi, by omega, fun r hr => ?_⟩
  rw [List.prefix_iff_eq_take]
  constructor
  · intro h
    refine ⟨?_, (hatmost r hr).mp (le_of_eq h.symm)⟩
    by_contra hc
    have := (hbelow r hr).mpr (by omega)
    rw [← h] at this
    exact lt_irrefl _ this
  · rintro ⟨h1, h2⟩
    have hle := (hatmost r hr).mpr h2
    have hnlt : ¬ (w.toList.drop sa[r]).take p.length < p := fun h => by
      have := (hbelow r hr).mp h
      omega
    exact (le_antisymm hle (not_lt.mp hnlt)).symm

/-- **Correctness of suffix-array search** on lists. -/
theorem search_spec {w : List α} {sa : List ℕ} (hsa : IsSuffixArray w sa) (p : List α) :
    (search w sa p).1 ≤ (search w sa p).2 ∧ (search w sa p).2 ≤ sa.length ∧
      ∀ (r : ℕ) (hr : r < sa.length),
        p <+: w.drop sa[r] ↔ (search w sa p).1 ≤ r ∧ r < (search w sa p).2 := by
  have := searchM_spec (w := w.toArray) (sa := sa.toArray) hsa p
  simpa only [search, List.size_toArray, List.getElem_toArray] using this

/-- `occurrences w sa p` lists exactly the positions where `p` occurs in `w` (as a prefix of a
nonempty suffix). -/
theorem mem_occurrences {w : List α} {sa : List ℕ} (hsa : IsSuffixArray w sa) (p : List α)
    {i : ℕ} : i ∈ occurrences w sa p ↔ i < w.length ∧ p <+: w.drop i := by
  rw [show occurrences w sa p = (sa.take (search w sa p).2).drop (search w sa p).1 from rfl]
  obtain ⟨hlohi, hhi, hspec⟩ := search_spec hsa p
  set lo := (search w sa p).1
  set hi := (search w sa p).2
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨k, hk, rfl⟩
    simp only [List.length_drop, List.length_take] at hk
    simp only [List.getElem_drop, List.getElem_take]
    have hr : lo + k < sa.length := by omega
    exact ⟨hsa.getElem_lt hr, (hspec (lo + k) hr).mpr ⟨by omega, by omega⟩⟩
  · rintro ⟨hi', hp⟩
    obtain ⟨r, hr, rfl⟩ := hsa.exists_getElem_eq hi'
    obtain ⟨h1, h2⟩ := (hspec r hr).mp hp
    refine ⟨r - lo, by simp only [List.length_drop, List.length_take]; omega, ?_⟩
    simp only [List.getElem_drop, List.getElem_take]
    congr 1
    omega

end Search

end Cslib.Algorithms.Lean.SuffixArray
