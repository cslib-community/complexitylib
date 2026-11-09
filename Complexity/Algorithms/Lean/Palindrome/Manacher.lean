/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Algorithms.Lean.Palindrome.Basic
public import Cslib.Algorithms.Lean.TimeM

/-!
# Manacher's Algorithm: All Maximal Palindromes in Linear Time

This module implements Manacher's algorithm (`[Manacher1975]`; all-centers formulation as in
`[ApostolicoBreslauerGalil1995]`, Section 1) in `Cslib.Algorithms.Lean.TimeM`: `manacherM w`
computes `radius w.toList c` for each of the `2 * w.size + 1` centers `c` of an array `w` over any
alphabet `[DecidableEq α]`, using at most `3 * w.size` character comparisons.

The algorithm scans the centers left to right, maintaining the center `C` whose maximal palindrome
reaches furthest right, ending at `R`. At a new center `c`, the mirror lemma `min_radius_mirror`
says that the radius about `c` agrees with the already computed radius `m` about `2 * C - c` up to
`b = R - (c + 1) / 2`. If `m < b`, the radius about `c` is `m`, with no comparisons. Otherwise it is
at least `b`, and `extendM` extends the palindrome of radius `b` about `c` letter by letter; every
successful comparison moves `R` one position right, so there are at most `w.size` of them, plus at
most one failed comparison per center.

## Source Conventions

* **Centers:** the centers and radii are those of `Complexity.Algorithms.Lean.Palindrome.Basic`
  (`[ApostolicoBreslauerGalil1995]`, Section 1, translated to `0`-indexed centers
  `c = 0, …, 2 * n`), with letters only: no sentinel symbols are interleaved, and the extension
  phase stops at the ends of `w` without a comparison.
* **Off-line formulation:** `manacherM` reads the whole array and returns all radii. Manacher's
  original algorithm is *on-line*, reporting the palindromic prefixes of the input read so far;
  that formulation is not modeled here. The palindromic prefixes are read off the radii by
  `palindrome_take_iff`.
* **Resource bounds:** `TimeM ℕ` counts exact character comparisons, not RAM steps.

## Cost Model

* **Charged (`1` `TimeM` tick):** every character equality comparison `w[l] = w[r]` in the
  extension phase `extendM`.
* **Uncharged (`0` `TimeM` ticks):** array reads, `Array.push`, natural-number arithmetic and
  comparisons of radii (the mirror test `m < b`), recursion control, and the argmax over the radii
  in `longestPalindromeM`.

Each extension phase makes at most one comparison more than the number of positions by which it
moves `R` right (`extendM_time_le`, `add_extendM_le`), and `R ≤ w.size` throughout, so the
`2 * w.size` centers `c ≥ 1` cost at most `w.size + 2 * w.size` comparisons (`manacherM_time_le`).
The bound is close to the algorithm's worst case: on `a b^(n - 2) c` it makes `3 * n - 6`
comparisons (checked for `n = 10` and `n = 20` in the test module `ComplexityTests.Manacher`; the
count for general `n` is not proved here).

## Main definitions

* `Cslib.Algorithms.Lean.Palindrome.extendM`: one extension phase, comparing `w[l - 1]` with `w[r]`
  and growing `[l, r)` while they agree.
* `Cslib.Algorithms.Lean.Palindrome.manacherM`, `manacher`: Manacher's algorithm and its output
  array of radii.
* `Cslib.Algorithms.Lean.Palindrome.longestPalindromeM`: the interval `[l, r)` of a longest
  palindromic factor, read off the radii.

## Main results

* `Cslib.Algorithms.Lean.Palindrome.manacher_eq`: `manacher w` is exactly the array
  `radius w.toList c` for `c < 2 * w.size + 1`.
* `Cslib.Algorithms.Lean.Palindrome.manacherM_time_le`: at most `3 * w.size` character comparisons.
* `Cslib.Algorithms.Lean.Palindrome.extract_longestPalindromeM`,
  `longestPalindromeM_time_le`: a longest palindromic factor in at most `3 * w.size` comparisons.

## References

* [G. Manacher, *A New Linear-Time "On-Line" Algorithm for Finding the Smallest Initial
  Palindrome of a String*][Manacher1975]
* [A. Apostolico, D. Breslauer, and Z. Galil, *Parallel detection of all palindromes in a
  string*][ApostolicoBreslauerGalil1995]
-/

public section

namespace Cslib.Algorithms.Lean.Palindrome

open Cslib.Algorithms.Lean.TimeM

variable {α : Type*} [DecidableEq α]

/-! ## The extension phase -/

/-- One extension phase: starting from the factor `[l, r)`, compare `w[l - 1]` with `w[r]` and grow
the factor while they agree, stopping at the ends of `w`. Returns the number of successful
extensions, charging one tick per character comparison. -/
def extendM (w : Array α) : ℕ → ℕ → TimeM ℕ ℕ
  | 0, _ => return 0
  | l + 1, r =>
    if h : r < w.size ∧ l < w.size then do
      ✓ if w[l]'h.2 = w[r]'h.1 then do
          let e ← extendM w l (r + 1)
          return e + 1
        else
          return 0
    else
      return 0

/-- An extension phase makes at most one comparison more than its number of extensions. -/
theorem extendM_time_le (w : Array α) (l r : ℕ) :
    (extendM w l r).time ≤ (extendM w l r).ret + 1 := by
  induction l generalizing r with
  | zero => simp only [extendM, TimeM.time_pure, TimeM.ret_pure]; omega
  | succ l ih =>
    simp only [extendM]
    split_ifs with h hEq
    · simp only [TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, TimeM.ret_bind,
        TimeM.ret_pure]
      have := ih (r + 1)
      omega
    · simp only [TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, TimeM.ret_bind,
        TimeM.ret_pure]
      omega
    · simp only [TimeM.time_pure, TimeM.ret_pure]; omega

/-- An extension phase never moves the right end past the end of `w`. -/
theorem add_extendM_le (w : Array α) (l : ℕ) {r : ℕ} (hr : r ≤ w.size) :
    r + (extendM w l r).ret ≤ w.size := by
  induction l generalizing r with
  | zero => simp only [extendM, TimeM.ret_pure]; omega
  | succ l ih =>
    simp only [extendM]
    split_ifs with h hEq
    · simp only [TimeM.ret_bind, TimeM.ret_pure]
      have := ih (r := r + 1) (by omega)
      omega
    · simp only [TimeM.ret_bind, TimeM.ret_pure]; omega
    · simp only [TimeM.ret_pure]; omega

/-- From any palindromic radius `k ≤ radius w c`, the extension phase reaches exactly the maximal
radius about `c`. -/
theorem add_ret_extendM {w : Array α} {c k : ℕ} (hk : k ≤ radius w.toList c) :
    k + (extendM w (c / 2 - k) ((c + 1) / 2 + k)).ret = radius w.toList c := by
  have hhalf := radius_le_half w.toList c
  generalize hl : c / 2 - k = l
  induction l generalizing k with
  | zero =>
    simp only [extendM, TimeM.ret_pure]
    omega
  | succ l ih =>
    simp only [extendM]
    split_ifs with h hEq
    · simp only [TimeM.ret_bind, TimeM.ret_pure]
      have hc : c ≤ 2 * w.toList.length := by simp only [Array.length_toList]; omega
      have hpr : IsPalRadius w.toList c (k + 1) := by
        rw [isPalRadius_succ_iff ((isPalRadius_iff_le_radius hc).mpr hk) (by omega)
          (by simp only [Array.length_toList]; omega)]
        rw [show c / 2 - k - 1 = l by omega, Array.getElem?_toList, Array.getElem?_toList,
          Array.getElem?_eq_getElem h.2, Array.getElem?_eq_getElem h.1, hEq]
      have hk1 := (isPalRadius_iff_le_radius hc).mp hpr
      have := ih hk1 (by omega)
      rw [show (c + 1) / 2 + (k + 1) = (c + 1) / 2 + k + 1 by omega] at this
      omega
    · simp only [TimeM.ret_bind, TimeM.ret_pure]
      by_contra hne
      have hpr := isPalRadius_succ_of_lt_radius (w := w.toList) (c := c) (k := k) (by omega)
      have hc : c ≤ 2 * w.toList.length := by
        have := hpr.2.1; omega
      rw [isPalRadius_succ_iff ((isPalRadius_iff_le_radius hc).mpr hk) (by omega)
          (by have := hpr.2.1; omega),
        show c / 2 - k - 1 = l by omega, Array.getElem?_toList, Array.getElem?_toList,
        Array.getElem?_eq_getElem h.2, Array.getElem?_eq_getElem h.1] at hpr
      exact hEq (Option.some_inj.mp hpr)
    · simp only [TimeM.ret_pure]
      by_contra hne
      have hpr := isPalRadius_succ_of_lt_radius (w := w.toList) (c := c) (k := k) (by omega)
      have h1 := hpr.2.1
      simp only [Array.length_toList] at h1
      omega

/-! ## The main loop -/

/-- The main loop of Manacher's algorithm. `rad` holds the radii of the centers `< c`, and `R` is
the right end of the maximal palindrome about `C`, the one reaching furthest right so far. -/
private def loopM (w : Array α) : ℕ → ℕ → ℕ → ℕ → Array ℕ → TimeM ℕ (Array ℕ)
  | 0, _, _, _, rad => return rad
  | fuel + 1, c, C, R, rad =>
    let m := rad.getD (2 * C - c) 0
    let b := R - (c + 1) / 2
    if m < b then
      loopM w fuel (c + 1) C R (rad.push m)
    else do
      let e ← extendM w (c / 2 - b) ((c + 1) / 2 + b)
      loopM w fuel (c + 1) c ((c + 1) / 2 + b + e) (rad.push (b + e))

/-- **Manacher's algorithm**: the maximal palindromic radius about each of the `2 * w.size + 1`
centers of `w`, charging one tick per character comparison. -/
def manacherM (w : Array α) : TimeM ℕ (Array ℕ) :=
  loopM w (2 * w.size) 1 0 0 #[0]

/-- The radii computed by Manacher's algorithm. -/
@[expose] def manacher (w : Array α) : Array ℕ :=
  (manacherM w).ret

theorem ret_manacherM (w : Array α) : (manacherM w).ret = manacher w := rfl

private theorem loopM_time_le (w : Array α) (fuel c C R : ℕ) (rad : Array ℕ) (hR : R ≤ w.size)
    (hc : c + fuel ≤ 2 * w.size + 1) :
    (loopM w fuel c C R rad).time ≤ w.size - R + fuel := by
  induction fuel generalizing c C R rad with
  | zero => simp only [loopM, TimeM.time_pure]; omega
  | succ fuel ih =>
    simp only [loopM]
    split_ifs with hm
    · have := ih (c + 1) C R (rad.push (rad.getD (2 * C - c) 0)) hR (by omega)
      omega
    · simp only [TimeM.time_bind]
      have hr0 : (c + 1) / 2 + (R - (c + 1) / 2) ≤ w.size := by omega
      have h1 := extendM_time_le w (c / 2 - (R - (c + 1) / 2)) ((c + 1) / 2 + (R - (c + 1) / 2))
      have h2 := add_extendM_le w (c / 2 - (R - (c + 1) / 2)) hr0
      have := ih (c + 1) c _ (rad.push ((R - (c + 1) / 2) +
        (extendM w (c / 2 - (R - (c + 1) / 2)) ((c + 1) / 2 + (R - (c + 1) / 2))).ret)) h2
        (by omega)
      omega

/-- **Linear bound**: Manacher's algorithm makes at most `3 * w.size` character comparisons. -/
theorem manacherM_time_le (w : Array α) : (manacherM w).time ≤ 3 * w.size := by
  have := loopM_time_le w (2 * w.size) 1 0 0 #[0] (Nat.zero_le _) (by omega)
  rw [manacherM]
  omega

private theorem loopM_spec (w : Array α) (fuel c C R : ℕ) (rad : Array ℕ)
    (hc : c + fuel = 2 * w.size + 1) (hsize : rad.size = c)
    (hrad : ∀ i (hi : i < rad.size), rad[i] = radius w.toList i) (hCc : C < c)
    (hR : R = (C + 1) / 2 + radius w.toList C) :
    (loopM w fuel c C R rad).ret = Array.ofFn (n := 2 * w.size + 1) (radius w.toList ·) := by
  induction fuel generalizing c C R rad with
  | zero =>
    simp only [loopM, TimeM.ret_pure]
    apply Array.ext (by simp only [Array.size_ofFn]; omega)
    intro i h1 h2
    rw [hrad i h1, Array.getElem_ofFn]
  | succ fuel ih =>
    have hRn : R ≤ w.toList.length := by
      rw [hR]; exact add_radius_le_length _ (by simp only [Array.length_toList]; omega)
    have hmirror := min_radius_mirror (w := w.toList) (c := c) (by omega) hR hRn
    have hm : rad.getD (2 * C - c) 0 = radius w.toList (2 * C - c) := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega), Option.getD_some,
        hrad]
    simp only [loopM]
    split_ifs with hlt
    · rw [hm] at hlt ⊢
      have heq : radius w.toList c = radius w.toList (2 * C - c) := by omega
      refine ih (c + 1) C R _ (by omega) (by simp only [Array.size_push]; omega) ?_ (by omega) hR
      intro i hi
      rw [Array.getElem_push]
      split_ifs with hi'
      · exact hrad i hi'
      · simp only [Array.size_push] at hi
        rw [show i = c by omega, heq]
    · rw [hm] at hlt
      simp only [TimeM.ret_bind]
      have hb : R - (c + 1) / 2 ≤ radius w.toList c := by omega
      have hext := add_ret_extendM (w := w) (c := c) hb
      refine ih (c + 1) c _ _ (by omega) (by simp only [Array.size_push]; omega) ?_ (by omega)
        (by omega)
      intro i hi
      rw [Array.getElem_push]
      split_ifs with hi'
      · exact hrad i hi'
      · simp only [Array.size_push] at hi
        rw [show i = c by omega, hext]

/-- **Correctness of Manacher's algorithm**: it returns exactly the maximal palindromic radii
about all `2 * w.size + 1` centers of `w`. -/
theorem manacher_eq (w : Array α) :
    manacher w = Array.ofFn (n := 2 * w.size + 1) (radius w.toList ·) := by
  refine loopM_spec w _ 1 0 0 #[0] (by omega) rfl ?_ Nat.zero_lt_one ?_
  · intro i hi
    have hi0 : i = 0 := by simp only [List.size_toArray, List.length_singleton] at hi; omega
    subst hi0
    have := radius_le_half w.toList 0
    simp only [List.getElem_toArray, List.getElem_singleton]
    omega
  · have := radius_le_half w.toList 0
    omega

theorem size_manacher (w : Array α) : (manacher w).size = 2 * w.size + 1 := by
  rw [manacher_eq, Array.size_ofFn]

theorem getElem_manacher (w : Array α) {c : ℕ} (hc : c < (manacher w).size) :
    (manacher w)[c] = radius w.toList c := by
  simp only [manacher_eq, Array.getElem_ofFn]

theorem getD_manacher (w : Array α) (c : ℕ) : (manacher w).getD c 0 = radius w.toList c := by
  rw [Array.getD_eq_getD_getElem?]
  by_cases hc : c < (manacher w).size
  · rw [Array.getElem?_eq_getElem hc, Option.getD_some, getElem_manacher]
  · rw [Array.getElem?_eq_none (by omega), Option.getD_none,
      radius_eq_zero_of_length_lt
        (by rw [size_manacher] at hc; simp only [Array.length_toList]; omega)]

/-! ## Longest palindromic factor -/

/-- A longest palindromic factor of `w` via Manacher's algorithm, returned as an interval `[l, r)`
of positions. The argmax over the radii makes no character comparisons and is free. -/
def longestPalindromeM (w : Array α) : TimeM ℕ (ℕ × ℕ) := do
  let rad ← manacherM w
  let c := ((List.range rad.size).argmax fun c => 2 * rad.getD c 0 + c % 2).getD 0
  let k := rad.getD c 0
  return (c / 2 - k, (c + 1) / 2 + k)

/-- `longestPalindromeM w` returns the interval of `longestPalindrome w.toList`, a longest
palindromic factor of `w` (`length_le_longestPalindrome`). -/
theorem extract_longestPalindromeM (w : Array α) :
    w.toList.extract (longestPalindromeM w).ret.1 (longestPalindromeM w).ret.2 =
      longestPalindrome w.toList := by
  simp only [longestPalindromeM, TimeM.ret_bind, TimeM.ret_pure, ret_manacherM, getD_manacher,
    size_manacher, longestPalindrome, maxPalindrome, bestCenter, Array.length_toList]

theorem longestPalindromeM_time_le (w : Array α) : (longestPalindromeM w).time ≤ 3 * w.size := by
  simp only [longestPalindromeM, TimeM.time_bind, TimeM.time_pure, Nat.add_zero]
  exact manacherM_time_le w

end Cslib.Algorithms.Lean.Palindrome
