/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.Data.List.Palindrome
public import Mathlib.Data.List.MinMax
public import Mathlib.Data.Nat.Find

/-!
# Maximal palindromes at all centers

A word `w` of length `n` has `2 * n + 1` *centers* `c = 0, …, 2 * n`: an odd center `c` is the
letter at position `c / 2`, and an even center `c` is the gap before position `c / 2` (with
`c = 2 * n` the gap after the last letter). A factor `w.extract a b` has center `a + b`, so
`w.extract (c / 2 - k) ((c + 1) / 2 + k)` is the factor with *radius* `k` about `c`: its length is
`2 * k + c % 2`. Palindromes are Mathlib's `List.Palindrome`.

`radius w c` is the maximal radius of a palindromic factor about `c`. This is the all-centers
formulation of [Apostolico, Breslauer and Galil][ApostolicoBreslauerGalil1995], Section 1: their
even palindrome of radius `R` centered at position `k` (1-indexed, letters `S[k - R .. k + R - 1]`)
has center `c = 2 * (k - 1)` here, and their odd palindrome of radius `R` centered on position `k`
(letters `S[k - R .. k + R]`) has center `c = 2 * k - 1`; the maximal radii agree. The extra center
`c = 2 * n` always has radius `0`.

Every palindromic factor is determined by the radius at its center
(`palindrome_extract_iff_le_radius`), so the longest palindromic factor (`longestPalindrome`) and
the palindromic prefixes (`palindrome_take_iff`) are read off the radii. Computing all radii in
linear time is Manacher's algorithm (`Complexity.Algorithms.Lean.Palindrome.Manacher`); its key
step is the mirror lemma `min_radius_mirror`.

## Main definitions

* `Cslib.Algorithms.Lean.Palindrome.IsPalRadius`: `w.extract (c / 2 - k) ((c + 1) / 2 + k)` is a
  palindromic factor of `w`.
* `Cslib.Algorithms.Lean.Palindrome.radius`: the maximal palindromic radius about center `c`.
* `Cslib.Algorithms.Lean.Palindrome.maxPalindrome`: the maximal palindromic factor about `c`.
* `Cslib.Algorithms.Lean.Palindrome.bestCenter`, `longestPalindrome`: a center maximizing
  `2 * radius w c + c % 2` and its maximal palindrome, a longest palindromic factor of `w`.

## Main results

* `Cslib.Algorithms.Lean.Palindrome.isPalRadius_iff_le_radius`: the palindromic radii about `c`
  are exactly `0, …, radius w c` (for centers `c ≤ 2 * w.length`).
* `Cslib.Algorithms.Lean.Palindrome.palindrome_extract_iff_le_radius`: for `a ≤ b ≤ w.length`,
  `w.extract a b` is a palindrome iff `b - a ≤ 2 * radius w (a + b) + (a + b) % 2`.
* `Cslib.Algorithms.Lean.Palindrome.isPalRadius_succ_iff`: a palindromic radius `k` with room on
  both sides extends to `k + 1` iff the two letters just outside it agree.
* `Cslib.Algorithms.Lean.Palindrome.min_radius_mirror`: the mirror lemma. If the maximal palindrome
  about `C` ends at `R`, then for `c ≥ C` the radii about `c` and about `2 * C - c` agree once
  truncated at `R - (c + 1) / 2`.
* `Cslib.Algorithms.Lean.Palindrome.length_le_longestPalindrome`,
  `palindrome_longestPalindrome`, `longestPalindrome_isInfix`: `longestPalindrome w` is a longest
  palindromic factor of `w`.
* `Cslib.Algorithms.Lean.Palindrome.palindrome_take_iff`: `w.take k` is a palindrome iff
  `radius w k = k / 2`.

## References

* [A. Apostolico, D. Breslauer, and Z. Galil, *Parallel detection of all palindromes in a
  string*][ApostolicoBreslauerGalil1995]
-/

public section

namespace Cslib.Algorithms.Lean.Palindrome

variable {α : Type*}

/-! ## Palindromic radii -/

/-- `k` is a palindromic radius about center `c` of `w`: the factor
`w.extract (c / 2 - k) ((c + 1) / 2 + k)` lies inside `w` and is a palindrome. -/
@[expose] def IsPalRadius (w : List α) (c k : ℕ) : Prop :=
  k ≤ c / 2 ∧ (c + 1) / 2 + k ≤ w.length ∧
    (w.extract (c / 2 - k) ((c + 1) / 2 + k)).Palindrome

instance [DecidableEq α] (w : List α) (c k : ℕ) : Decidable (IsPalRadius w c k) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The maximal palindromic radius about center `c` of `w` (`0` when `c > 2 * w.length`). -/
@[expose] def radius [DecidableEq α] (w : List α) (c : ℕ) : ℕ :=
  Nat.findGreatest (IsPalRadius w c) w.length

theorem IsPalRadius.mono {w : List α} {c k k' : ℕ} (h : IsPalRadius w c k) (hk : k' ≤ k) :
    IsPalRadius w c k' := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨by omega, by omega, h3.extract_of_le h2 (by omega) (by omega) (by omega)⟩

theorem isPalRadius_zero {w : List α} {c : ℕ} (hc : c ≤ 2 * w.length) : IsPalRadius w c 0 := by
  refine ⟨Nat.zero_le _, by omega, ?_⟩
  rw [List.palindrome_extract_iff (by omega)]
  intro i hi hi'
  congr 1
  omega

/-- The extension step: a palindromic radius `k` about `c` with room on both sides extends to
`k + 1` iff the two letters just outside its factor agree. -/
theorem isPalRadius_succ_iff {w : List α} {c k : ℕ} (hk : IsPalRadius w c k) (hl : k < c / 2)
    (hr : (c + 1) / 2 + k < w.length) :
    IsPalRadius w c (k + 1) ↔ w[c / 2 - k - 1]? = w[(c + 1) / 2 + k]? := by
  obtain ⟨_, _, hpal⟩ := hk
  have hiff := List.palindrome_extract_sub_one_add_one_iff (l := w) (a := c / 2 - k)
    (b := (c + 1) / 2 + k) (by omega) (by omega) hr
  rw [show c / 2 - k - 1 = c / 2 - (k + 1) by omega,
    show (c + 1) / 2 + k + 1 = (c + 1) / 2 + (k + 1) by omega] at hiff
  rw [show c / 2 - k - 1 = c / 2 - (k + 1) by omega]
  constructor
  · intro h
    exact (hiff.mp h.2.2).2
  · intro h
    exact ⟨by omega, by omega, hiff.mpr ⟨hpal, h⟩⟩

variable [DecidableEq α]

/-- The palindromic radii about a center `c ≤ 2 * w.length` are exactly `0, …, radius w c`. -/
theorem isPalRadius_iff_le_radius {w : List α} {c k : ℕ} (hc : c ≤ 2 * w.length) :
    IsPalRadius w c k ↔ k ≤ radius w c := by
  constructor
  · intro h
    exact Nat.le_findGreatest (by have := h.2.1; omega) h
  · intro h
    exact (Nat.findGreatest_spec (Nat.zero_le _) (isPalRadius_zero hc)).mono h

theorem radius_eq_zero_of_length_lt {w : List α} {c : ℕ} (hc : 2 * w.length < c) :
    radius w c = 0 := by
  rw [radius, Nat.findGreatest_eq_zero_iff]
  intro k _ _ hk
  have := hk.2.1
  omega

theorem radius_le_half (w : List α) (c : ℕ) : radius w c ≤ c / 2 := by
  by_cases hc : c ≤ 2 * w.length
  · exact ((isPalRadius_iff_le_radius hc).mpr le_rfl).1
  · rw [radius_eq_zero_of_length_lt (by omega)]
    exact Nat.zero_le _

theorem add_radius_le_length (w : List α) {c : ℕ} (hc : c ≤ 2 * w.length) :
    (c + 1) / 2 + radius w c ≤ w.length :=
  ((isPalRadius_iff_le_radius hc).mpr le_rfl).2.1

theorem isPalRadius_succ_of_lt_radius {w : List α} {c k : ℕ} (hk : k < radius w c) :
    IsPalRadius w c (k + 1) := by
  by_cases hc : c ≤ 2 * w.length
  · exact (isPalRadius_iff_le_radius hc).mpr hk
  · rw [radius_eq_zero_of_length_lt (by omega)] at hk
    omega

/-- Palindromic factors are characterized by the radius at their center: for `a ≤ b ≤ w.length`,
`w.extract a b` is a palindrome iff `b - a ≤ 2 * radius w (a + b) + (a + b) % 2`. -/
theorem palindrome_extract_iff_le_radius {w : List α} {a b : ℕ} (hab : a ≤ b)
    (hb : b ≤ w.length) :
    (w.extract a b).Palindrome ↔ b - a ≤ 2 * radius w (a + b) + (a + b) % 2 := by
  have key : IsPalRadius w (a + b) ((b - a) / 2) ↔ (w.extract a b).Palindrome := by
    have e1 : (a + b) / 2 - (b - a) / 2 = a := by omega
    have e2 : (a + b + 1) / 2 + (b - a) / 2 = b := by omega
    unfold IsPalRadius
    rw [e1, e2]
    exact ⟨fun h => h.2.2, fun h => ⟨by omega, hb, h⟩⟩
  rw [← key, isPalRadius_iff_le_radius (by omega)]
  omega

/-- **Mirror lemma** (the step of Manacher's algorithm). If the maximal palindrome about center
`C` ends at `R = (C + 1) / 2 + radius w C`, then for every center `c ≥ C` the radii about `c` and
about its mirror image `2 * C - c`, truncated at the distance `R - (c + 1) / 2` from the right end
of that palindrome, agree. -/
theorem min_radius_mirror {w : List α} {C c R : ℕ} (hCc : C ≤ c)
    (hR : R = (C + 1) / 2 + radius w C) (hRn : R ≤ w.length) :
    min (radius w c) (R - (c + 1) / 2) = min (radius w (2 * C - c)) (R - (c + 1) / 2) := by
  set b := R - (c + 1) / 2 with hb
  rcases Nat.eq_zero_or_pos b with hb0 | hbpos
  · rw [hb0, Nat.min_zero, Nat.min_zero]
  have hCR := radius_le_half w C
  have hc2C : c ≤ 2 * C := by omega
  set c' := 2 * C - c with hc'
  have hcn : c ≤ 2 * w.length := by omega
  have hc'n : c' ≤ 2 * w.length := by omega
  have hbig : (w.extract (C / 2 - radius w C) R).Palindrome := by
    have := (isPalRadius_iff_le_radius (w := w) (c := C) (by omega)).mpr le_rfl
    rw [hR]
    exact this.2.2
  set L := C / 2 - radius w C with hL
  have hLR : L + R = C := by omega
  -- Inside `[L, R)`, the palindromic radii `k ≤ b` about `c` and about `c'` correspond under
  -- reflection across the center `C`.
  have hiff : ∀ k, k ≤ b → (IsPalRadius w c k ↔ IsPalRadius w c' k) := by
    intro k hk
    have e1 : L + R - ((c + 1) / 2 + k) = c' / 2 - k := by omega
    have e2 : L + R - (c / 2 - k) = (c' + 1) / 2 + k := by omega
    have e3 : L + R - ((c' + 1) / 2 + k) = c / 2 - k := by omega
    have e4 : L + R - (c' / 2 - k) = (c + 1) / 2 + k := by omega
    constructor
    · rintro ⟨_, _, h⟩
      refine ⟨by omega, by omega, ?_⟩
      have := hbig.extract_reflect h hRn (by omega) (by omega) (by omega)
      rwa [e1, e2] at this
    · rintro ⟨_, _, h⟩
      refine ⟨by omega, by omega, ?_⟩
      have := hbig.extract_reflect h hRn (by omega) (by omega) (by omega)
      rwa [e3, e4] at this
  have h1 : min (radius w c) b ≤ radius w c' := by
    rw [← isPalRadius_iff_le_radius hc'n, ← hiff _ (Nat.min_le_right _ _),
      isPalRadius_iff_le_radius hcn]
    exact Nat.min_le_left _ _
  have h2 : min (radius w c') b ≤ radius w c := by
    rw [← isPalRadius_iff_le_radius hcn, hiff _ (Nat.min_le_right _ _),
      isPalRadius_iff_le_radius hc'n]
    exact Nat.min_le_left _ _
  omega

/-! ## Longest palindromic factors and palindromic prefixes -/

/-- The maximal palindromic factor about center `c` of `w` (empty when `c > 2 * w.length`). -/
@[expose] def maxPalindrome (w : List α) (c : ℕ) : List α :=
  w.extract (c / 2 - radius w c) ((c + 1) / 2 + radius w c)

theorem maxPalindrome_isInfix (w : List α) (c : ℕ) : maxPalindrome w c <:+: w := by
  have key : ∀ a b : ℕ, a ≤ b → w.take a ++ w.extract a b ++ w.drop b = w := by
    intro a b hab
    rw [List.extract_eq_take_drop, List.append_assoc]
    conv_rhs => rw [← List.take_append_drop a w, ← List.take_append_drop (b - a) (w.drop a)]
    rw [List.drop_drop, Nat.add_sub_cancel' hab]
  exact ⟨_, _, key _ _ (by omega)⟩

theorem palindrome_maxPalindrome (w : List α) (c : ℕ) : (maxPalindrome w c).Palindrome := by
  by_cases hc : c ≤ 2 * w.length
  · exact ((isPalRadius_iff_le_radius hc).mpr le_rfl).2.2
  · rw [maxPalindrome, radius_eq_zero_of_length_lt (by omega), List.Palindrome.iff_getElem?]
    intro i hi
    simp only [List.extract_eq_take_drop, List.length_take, List.length_drop] at hi
    omega

theorem length_maxPalindrome (w : List α) {c : ℕ} (hc : c ≤ 2 * w.length) :
    (maxPalindrome w c).length = 2 * radius w c + c % 2 := by
  have h1 := radius_le_half w c
  have h2 := add_radius_le_length w hc
  simp only [maxPalindrome, List.extract_eq_take_drop, List.length_take, List.length_drop]
  omega

/-- Every palindromic factor of `w` is at most as long as the maximal palindrome about its
center. -/
theorem exists_length_le_radius_of_isInfix {w u : List α} (hu : u <:+: w) (hpal : u.Palindrome) :
    ∃ c ≤ 2 * w.length, u.length ≤ 2 * radius w c + c % 2 := by
  obtain ⟨s, t, rfl⟩ := hu
  have hext : (s ++ u ++ t).extract s.length (s.length + u.length) = u := by
    simp only [List.extract_eq_take_drop, List.append_assoc, List.drop_left,
      Nat.add_sub_cancel_left, List.take_left]
  refine ⟨s.length + (s.length + u.length), by simp only [List.length_append]; omega, ?_⟩
  rw [← hext] at hpal
  have := (palindrome_extract_iff_le_radius (by omega)
    (by simp only [List.length_append]; omega)).mp hpal
  omega

/-- A center of `w` whose maximal palindrome is longest. -/
@[expose] def bestCenter (w : List α) : ℕ :=
  ((List.range (2 * w.length + 1)).argmax fun c => 2 * radius w c + c % 2).getD 0

/-- A longest palindromic factor of `w`: the maximal palindrome about `bestCenter w`. -/
@[expose] def longestPalindrome (w : List α) : List α :=
  maxPalindrome w (bestCenter w)

theorem longestPalindrome_isInfix (w : List α) : longestPalindrome w <:+: w :=
  maxPalindrome_isInfix w _

theorem palindrome_longestPalindrome (w : List α) : (longestPalindrome w).Palindrome :=
  palindrome_maxPalindrome w _

/-- `longestPalindrome w` is at least as long as every palindromic factor of `w`. -/
theorem length_le_longestPalindrome {w u : List α} (hu : u <:+: w) (hpal : u.Palindrome) :
    u.length ≤ (longestPalindrome w).length := by
  obtain ⟨c, hc, hlen⟩ := exists_length_le_radius_of_isInfix hu hpal
  set f : ℕ → ℕ := fun c => 2 * radius w c + c % 2
  have hne : (List.range (2 * w.length + 1)).argmax f ≠ none := by
    rw [Ne, List.argmax_eq_none, List.range_eq_nil]
    omega
  obtain ⟨m, hm⟩ := Option.ne_none_iff_exists'.mp hne
  have hmem : m ∈ List.range (2 * w.length + 1) := List.argmax_mem hm
  have hle : f c ≤ f m := List.le_of_mem_argmax (List.mem_range.mpr (by omega)) hm
  have hbest : bestCenter w = m := congrArg (fun o => Option.getD o 0) hm
  rw [longestPalindrome, hbest, length_maxPalindrome w (by rw [List.mem_range] at hmem; omega)]
  exact le_trans hlen hle

/-- Palindromic prefixes are read off the radii: for `k ≤ w.length`, the prefix `w.take k` is a
palindrome iff the maximal palindrome about center `k` reaches the start of `w`. -/
theorem palindrome_take_iff {w : List α} {k : ℕ} (hk : k ≤ w.length) :
    (w.take k).Palindrome ↔ radius w k = k / 2 := by
  have h := palindrome_extract_iff_le_radius (w := w) (Nat.zero_le k) hk
  simp only [List.extract_eq_take_drop, List.drop_zero, Nat.sub_zero, Nat.zero_add] at h
  have := radius_le_half w k
  rw [h]
  omega

end Cslib.Algorithms.Lean.Palindrome
