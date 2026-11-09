/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Data/List/Palindrome.lean`)

public import CslibFrontier.Init
public import Mathlib.Data.List.Palindrome

/-!
# Palindromic factors of lists

Index characterizations of Mathlib's `List.Palindrome`, for whole lists
(`List.Palindrome.iff_getElem?`) and for factors `l.extract a b` (`List.palindrome_extract_iff`),
and the three facts about palindromic factors that center-based palindrome algorithms use:
shrinking a palindromic factor symmetrically keeps it a palindrome
(`List.Palindrome.extract_of_le`), a palindromic factor extends by one letter on each side iff those
two letters agree (`List.palindrome_extract_sub_one_add_one_iff`), and palindromic factors inside a
palindromic factor reflect to palindromic factors (`List.Palindrome.extract_reflect`).

## Main results

* `List.Palindrome.iff_getElem?`: `l` is a palindrome iff `l[i]? = l[l.length - 1 - i]?` for
  every `i < l.length`.
* `List.palindrome_extract_iff`: for `b ≤ l.length`, the factor `l.extract a b` is a palindrome iff
  `l[i]? = l[a + b - 1 - i]?` for every `a ≤ i < b`.
* `List.Palindrome.extract_of_le`: shrinking a palindromic factor symmetrically about its center
  keeps it a palindrome.
* `List.palindrome_extract_sub_one_add_one_iff`: `l.extract (a - 1) (b + 1)` is a palindrome iff
  `l.extract a b` is and `l[a - 1]? = l[b]?`.
* `List.Palindrome.extract_reflect`: if `l.extract L R` and `l.extract a b` are palindromes with
  `L ≤ a ≤ b ≤ R`, then so is the mirror image `l.extract (L + R - b) (L + R - a)`.
-/

public section

namespace List

variable {α : Type*}

/-- Index characterization of palindromes. -/
theorem Palindrome.iff_getElem? {l : List α} :
    Palindrome l ↔ ∀ i < l.length, l[i]? = l[l.length - 1 - i]? := by
  rw [Palindrome.iff_reverse_eq]
  constructor
  · intro h i hi
    rw [← getElem?_reverse hi, h]
  · intro h
    ext i : 1
    by_cases hi : i < l.length
    · rw [getElem?_reverse hi, h i hi]
    · rw [getElem?_eq_none (by simpa only [length_reverse] using Nat.le_of_not_lt hi),
        getElem?_eq_none (Nat.le_of_not_lt hi)]

/-- A factor `l.extract a b` with `b ≤ l.length` is a palindrome iff the letters at positions
symmetric about the midpoint of `[a, b)` agree. -/
theorem palindrome_extract_iff {l : List α} {a b : ℕ} (hb : b ≤ l.length) :
    Palindrome (l.extract a b) ↔ ∀ i, a ≤ i → i < b → l[i]? = l[a + b - 1 - i]? := by
  rw [Palindrome.iff_getElem?]
  have hlen : (l.extract a b).length = b - a := by
    simp only [extract_eq_take_drop, length_take, length_drop]
    omega
  have hget : ∀ j, j < b - a → (l.extract a b)[j]? = l[a + j]? := by
    intro j hj
    simp only [extract_eq_take_drop, getElem?_take, getElem?_drop, hj, ↓reduceIte]
  rw [hlen]
  constructor
  · intro h i hai hib
    have := h (i - a) (by omega)
    rw [hget _ (by omega), hget _ (by omega)] at this
    rw [show i = a + (i - a) by omega, this]
    congr 1
    omega
  · intro h j hj
    rw [hget _ hj, hget _ (by omega), h (a + j) (by omega) (by omega)]
    congr 1
    omega

/-- Shrinking a palindromic factor symmetrically about its center keeps it a palindrome. -/
theorem Palindrome.extract_of_le {l : List α} {a b a' b' : ℕ}
    (h : (l.extract a b).Palindrome) (hb : b ≤ l.length) (ha : a ≤ a') (hb' : b' ≤ b)
    (hsum : a' + b' = a + b) : (l.extract a' b').Palindrome := by
  rw [palindrome_extract_iff hb] at h
  rw [palindrome_extract_iff (by omega)]
  intro i hi hi'
  rw [hsum]
  exact h i (by omega) (by omega)

/-- A palindromic factor extends by one letter on each side iff those two letters agree. -/
theorem palindrome_extract_sub_one_add_one_iff {l : List α} {a b : ℕ} (ha : 0 < a)
    (hab : a ≤ b) (hb : b < l.length) :
    (l.extract (a - 1) (b + 1)).Palindrome ↔ (l.extract a b).Palindrome ∧ l[a - 1]? = l[b]? := by
  rw [palindrome_extract_iff (by omega), palindrome_extract_iff (by omega)]
  constructor
  · intro h
    refine ⟨fun i hi hi' => ?_, ?_⟩
    · rw [h i (by omega) (by omega)]
      congr 1
      omega
    · rw [h (a - 1) (Nat.le_refl _) (by omega)]
      congr 1
      omega
  · rintro ⟨h, hab'⟩ i hi hi'
    by_cases hlo : i = a - 1
    · subst hlo
      rw [hab']
      congr 1
      omega
    by_cases hhi : i = b
    · subst hhi
      rw [show a - 1 + (i + 1) - 1 - i = a - 1 by omega, hab']
    rw [h i (by omega) (by omega)]
    congr 1
    omega

/-- Palindromes reflect inside a palindrome: if `l.extract L R` is a palindrome and
`L ≤ a ≤ b ≤ R`, then the factor `l.extract a b` is a palindrome iff its mirror image
`l.extract (L + R - b) (L + R - a)` is; this is the forward direction. -/
theorem Palindrome.extract_reflect {l : List α} {L R a b : ℕ}
    (hbig : (l.extract L R).Palindrome) (h : (l.extract a b).Palindrome) (hR : R ≤ l.length)
    (hL : L ≤ a) (hab : a ≤ b) (hbR : b ≤ R) :
    (l.extract (L + R - b) (L + R - a)).Palindrome := by
  rw [palindrome_extract_iff hR] at hbig
  rw [palindrome_extract_iff (by omega)] at h
  rw [palindrome_extract_iff (by omega)]
  intro i hi hi'
  -- Reflect `i` into `[a, b)` across the center of `[L, R)`, use `h` there, and reflect back.
  rw [hbig i (by omega) (by omega), h (L + R - 1 - i) (by omega) (by omega),
    hbig (a + b - 1 - (L + R - 1 - i)) (by omega) (by omega)]
  congr 1
  omega

end List
