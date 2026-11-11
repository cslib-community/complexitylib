/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Algorithms.Lean.SuffixArray.Kasai
public import Complexity.Foundations.Data.List.CommonPrefix
public import Cslib.Algorithms.Lean.TimeM

/-!
# The Z-algorithm

The Z-function of a word `s` records, at each position `i`, the length of the longest common
prefix of `s` and its suffix `s.drop i`. The Z-algorithm (`[Gusfield1997]`, Section 1.4) computes
all of these values from left to right. It keeps the box `[l, r)`, the rightmost interval found
so far that repeats a prefix of `s`. At a position `i` inside the box, the value `z[i - l]`
either gives `z[i]` outright or shows that `z[i] ≥ r - i`, so explicit comparisons start at
`r`. Every comparison that matches moves `r` to the right, and each position ends with at most
one mismatch, so the total number of comparisons is linear.

## Source Conventions

* **Indexing:** positions are `0`-based, and `z[0] = |s|` (the whole word is a prefix of
  itself). Gusfield indexes from `1` and leaves `Z_1` undefined.
* **Box:** `[l, r)` is half-open. Gusfield's box `[l, r]` is closed and `1`-indexed. Initially
  `l = r = 0`, the empty box.
* **Resource bounds:** `TimeM ℕ` counts exact character comparisons. The bound `2 * |s| - 3`
  (natural subtraction, so `0` for `|s| ≤ 1`) holds for every input and makes explicit the linear
  bound of `[Gusfield1997]`, Section 1.4.
  It is attained by `a ^ (n - 1) b` for `n ≥ 2`; this is checked for small `n` in the tests.

## Cost Model

* **Charged (`1` `TimeM` tick):** every character equality comparison, all made by the
  suffix-array primitive `Cslib.Algorithms.Lean.SuffixArray.extendM` (shared with Kasai et al.'s
  algorithm).
* **Uncharged (`0` `TimeM` ticks):** array reads and pushes, the comparison of `z[i - l]` with
  `r - i`, integer arithmetic, loop control and the conversions in the list wrapper.

A call to `extendM` starting from a common prefix `h = max (r - i) 0` makes at most
`ret - h + 1` comparisons, and `ret - h` when it reaches the end of the word
(`extendM_time_add_le_of_size_le`). The potential `max r i` plus one more while `max r i < |s|`
then telescopes to `2 * |s| - 3` (`zAlgorithmM_time_le`).

## Main definitions

* `Cslib.Algorithms.Lean.ZFunction.zFunction`: the specification
  `z[i] = List.lcpLen s (s.drop i)`.
* `Cslib.Algorithms.Lean.ZFunction.zAlgorithmM`, `zAlgorithm`: the Z-algorithm on arrays in
  `TimeM ℕ`, and its list wrapper.

## Main results

* `Cslib.Algorithms.Lean.ZFunction.ret_zAlgorithmM` and `zAlgorithm_eq_zFunction`: the algorithm
  computes the Z-function, for every input.
* `Cslib.Algorithms.Lean.ZFunction.zAlgorithmM_time_le`: at most `2 * |s| - 3` character
  comparisons.

## References

* [D. Gusfield, *Algorithms on Strings, Trees, and Sequences*][Gusfield1997]
-/

public section

namespace Cslib.Algorithms.Lean.ZFunction

open Cslib.Algorithms.Lean SuffixArray

variable {α : Type*} [DecidableEq α]

/-! ## Specification -/

/-- The Z-function of `s`: at each position `i < |s|`, the length of the longest common prefix
of `s` and `s.drop i`. -/
def zFunction (s : List α) : List ℕ :=
  (List.range s.length).map fun i => List.lcpLen s (s.drop i)

@[simp] theorem length_zFunction (s : List α) : (zFunction s).length = s.length := by
  rw [zFunction, List.length_map, List.length_range]

theorem getElem_zFunction (s : List α) (i : ℕ) (hi : i < (zFunction s).length) :
    (zFunction s)[i]'hi = List.lcpLen s (s.drop i) := by
  simp only [zFunction, List.getElem_map, List.getElem_range]

/-- The Z-function at `0` is the length of the word. -/
theorem getElem_zFunction_zero (s : List α) (hs : 0 < (zFunction s).length) :
    (zFunction s)[0]'hs = s.length := by
  rw [getElem_zFunction, List.drop_zero, List.lcpLen_self]

/-! ## The algorithm -/

/-- The main loop of the Z-algorithm at position `i`, with box `[l, r)` and the values `z` at
the positions before `i`. If `z[i - l] < r - i` then `z[i] = z[i - l]`; otherwise extend the
common prefix of `s` and `s.drop i` from `max (r - i) 0`. When `i ≥ r` the test fails because
`r - i = 0`, whatever the read returns (`Array.getD` returns `0` outside `z`). -/
private def zLoopM (s : Array α) (i l r : ℕ) (z : Array ℕ) : TimeM ℕ (Array ℕ) :=
  if i < s.size then
    if z.getD (i - l) 0 < r - i then
      zLoopM s (i + 1) l r (z.push (z.getD (i - l) 0))
    else do
      let k ← extendM s 0 i (r - i)
      zLoopM s (i + 1) i (i + k) (z.push k)
  else
    return z
termination_by s.size - i

/-- The Z-algorithm in `TimeM ℕ`, charging one tick per character comparison. The value at `0`
is the length of the word; the loop computes the others from left to right. -/
def zAlgorithmM (s : Array α) : TimeM ℕ (Array ℕ) :=
  if s.size = 0 then return #[] else zLoopM s 1 0 0 #[s.size]

/-- The Z-algorithm on lists. -/
def zAlgorithm (s : List α) : List ℕ :=
  (zAlgorithmM s.toArray).ret.toList

/-! ## Character comparisons -/

/-- Amortized cost of the main loop, with potential `max r i`, plus one while
`max r i < |s|`. -/
private theorem zLoopM_time_add_le (s : Array α) (i l r : ℕ) (z : Array ℕ) (hi : i ≤ s.size)
    (hr : r ≤ s.size) :
    (zLoopM s i l r z).time + max r i + (if max r i < s.size then 1 else 0) ≤
      (s.size - i) + s.size := by
  generalize hk : s.size - i = k
  induction k generalizing i l r z with
  | zero =>
    rw [zLoopM]
    simp only [show ¬(i < s.size) by omega, ↓reduceIte, TimeM.time_pure]
    split_ifs <;> omega
  | succ k ih =>
    have his : i < s.size := by omega
    rw [zLoopM]
    simp only [his, ↓reduceIte]
    by_cases hcopy : z.getD (i - l) 0 < r - i
    · simp only [hcopy, ↓reduceIte]
      have := ih (i + 1) l r (z.push (z.getD (i - l) 0)) (by omega) hr (by omega)
      split_ifs at this ⊢ <;> omega
    · simp only [hcopy, ↓reduceIte, TimeM.time_bind]
      have h1 := extendM_time_add_le s 0 i (r - i)
      have h2 := ret_extendM_le s 0 i (r - i)
      have h3 := extendM_time_add_le_of_size_le s 0 i (r - i)
      have := ih (i + 1) i (i + (extendM s 0 i (r - i)).ret)
        (z.push (extendM s 0 i (r - i)).ret) (by omega) (by omega) (by omega)
      by_cases hend : s.size ≤ i + (extendM s 0 i (r - i)).ret
      · have h3 := h3 hend
        split_ifs at this ⊢ <;> omega
      · split_ifs at this ⊢ <;> omega

/-- **Linear bound for the Z-algorithm.** `zAlgorithmM s` performs at most `2 * |s| - 3`
character comparisons, for every input. -/
theorem zAlgorithmM_time_le (s : Array α) : (zAlgorithmM s).time ≤ 2 * s.size - 3 := by
  rw [zAlgorithmM]
  split_ifs with h0
  · simp only [TimeM.time_pure]
    omega
  · have := zLoopM_time_add_le s 1 0 0 #[s.size] (by omega) (Nat.zero_le _)
    split_ifs at this <;> omega

/-! ## Correctness -/

/-- Loop invariant: the values before `i` are correct, `l < i`, the box `[l, r)` repeats a
prefix of `s` (`r ≤ l + z[l]`), and the box is empty when `l = 0`. -/
private theorem zLoopM_spec (s : Array α) (i l r : ℕ) (z : Array ℕ) (hi1 : 1 ≤ i)
    (hi : i ≤ s.size) (hz : z.size = i)
    (hzs : ∀ (j : ℕ) (hj : j < i), z[j]'(by omega) = List.lcpLen s.toList (s.toList.drop j))
    (hl : l < i) (hl0 : r = 0 ∨ 0 < l)
    (hrl : r ≤ l + List.lcpLen s.toList (s.toList.drop l)) (hr : r ≤ s.size) :
    (zLoopM s i l r z).ret.toList = zFunction s.toList := by
  generalize hk : s.size - i = k
  induction k generalizing i l r z with
  | zero =>
    rw [zLoopM]
    simp only [show ¬(i < s.size) by omega, ↓reduceIte, TimeM.ret_pure]
    apply List.ext_getElem (by simp only [Array.length_toList, length_zFunction]; omega)
    intro j h1 h2
    simp only [Array.length_toList] at h1
    rw [Array.getElem_toList, getElem_zFunction, hzs j (by omega)]
  | succ k ih =>
    have his : i < s.size := by omega
    rw [zLoopM]
    simp only [his, ↓reduceIte]
    -- Inside the box, `s.drop i` and `s.drop (i - l)` agree on their first `r - i` entries.
    have hbox : i < r → min (List.lcpLen s.toList (s.toList.drop (i - l))) (r - i) =
        min (List.lcpLen s.toList (s.toList.drop i)) (r - i) := by
      intro hir
      obtain ⟨_, hA2, hA3⟩ :=
        List.le_lcpLen_iff.mp (show r - l ≤ List.lcpLen s.toList (s.toList.drop l) by omega)
      simp only [List.length_drop, Array.length_toList] at hA2
      apply List.min_lcpLen_eq_of_take_eq
      · simp only [List.length_drop, Array.length_toList]; omega
      · simp only [List.length_drop, Array.length_toList]; omega
      · have e1 : s.toList.drop i = (s.toList.drop l).drop (i - l) := by
          rw [List.drop_drop]; congr 1; omega
        rw [e1, List.take_drop, List.take_drop, show i - l + (r - i) = r - l by omega, hA3]
    have hzil : i < r → z.getD (i - l) 0 = List.lcpLen s.toList (s.toList.drop (i - l)) := by
      intro hir
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega), Option.getD_some]
      exact hzs (i - l) (by omega)
    by_cases hcopy : z.getD (i - l) 0 < r - i
    · simp only [hcopy, ↓reduceIte]
      have hir : i < r := by omega
      have hmin := hbox hir
      have hval : z.getD (i - l) 0 = List.lcpLen s.toList (s.toList.drop i) := by grind
      refine ih (i + 1) l r (z.push (z.getD (i - l) 0)) (by omega) (by omega)
        (by rw [Array.size_push, hz]) (fun j hj => ?_) (by omega) hl0 hrl hr (by omega)
      rw [Array.getElem_push]
      split_ifs with hji
      · exact hzs j (by omega)
      · rw [show j = i by omega]
        exact hval
    · simp only [hcopy, ↓reduceIte, TimeM.ret_bind]
      have hh : r - i ≤ List.lcpLen s.toList (s.toList.drop i) := by grind
      have hext : (extendM s 0 i (r - i)).ret = List.lcpLen s.toList (s.toList.drop i) := by
        rw [ret_extendM, List.lcpLen_eq_add_lcpLen_drop hh, List.drop_drop, Nat.zero_add]
      rw [hext]
      have hlen := List.lcpLen_le_length_right s.toList (s.toList.drop i)
      simp only [List.length_drop, Array.length_toList] at hlen
      refine ih (i + 1) i (i + List.lcpLen s.toList (s.toList.drop i))
        (z.push (List.lcpLen s.toList (s.toList.drop i))) (by omega) (by omega)
        (by rw [Array.size_push, hz]) (fun j hj => ?_) (by omega) (Or.inr (by omega))
        (le_refl _) (by omega) (by omega)
      rw [Array.getElem_push]
      split_ifs with hji
      · exact hzs j (by omega)
      · rw [show j = i by omega]

/-- **Correctness of the Z-algorithm**: `zAlgorithmM s` returns the Z-function of `s`, for every
input. -/
theorem ret_zAlgorithmM (s : Array α) : (zAlgorithmM s).ret.toList = zFunction s.toList := by
  rw [zAlgorithmM]
  split_ifs with h0
  · simp only [TimeM.ret_pure, List.toList_toArray]
    rw [zFunction, Array.length_toList, h0, List.range_zero, List.map_nil]
  · refine zLoopM_spec s 1 0 0 #[s.size] (le_refl _) (by omega) rfl (fun j hj => ?_)
      Nat.zero_lt_one (Or.inl rfl) (Nat.zero_le _) (Nat.zero_le _)
    obtain rfl : j = 0 := by omega
    rw [List.drop_zero, List.lcpLen_self, Array.length_toList]
    rfl

/-- **Correctness of the Z-algorithm** on lists. -/
theorem zAlgorithm_eq_zFunction (s : List α) : zAlgorithm s = zFunction s :=
  ret_zAlgorithmM s.toArray

end Cslib.Algorithms.Lean.ZFunction
