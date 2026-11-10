/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (test driver)

import Complexity.Init
import Complexity.Algorithms.Lean.Palindrome.Basic
import Complexity.Algorithms.Lean.Palindrome.Manacher

/-!
# Manacher's Algorithm Tests

Kernel-checked (`decide`) and executable (`#guard`) instances for the maximal palindromic radii
`Cslib.Algorithms.Lean.Palindrome.radius` and Manacher's algorithm
(`Complexity.Algorithms.Lean.Palindrome.Manacher`), with non-vacuity instantiations of the
longest-palindrome and palindromic-prefix theorems.
-/

namespace Cslib.Algorithms.Lean.Palindrome.Tests

open Cslib.Algorithms.Lean.Palindrome

set_option linter.hashCommand false

/-! ## Radii at all centers, checked by the kernel through `manacher_eq` -/

-- "abacaba": the whole word is the palindrome of radius 3 about its middle letter (center 7).
example : manacher #['a', 'b', 'a', 'c', 'a', 'b', 'a'] =
    #[0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0] := by
  rw [manacher_eq]; decide

-- "abba": an even palindrome of radius 2 about the middle gap (center 4).
example : manacher #['a', 'b', 'b', 'a'] = #[0, 0, 0, 0, 2, 0, 0, 0, 0] := by
  rw [manacher_eq]; decide

-- All-equal letters: every center's palindrome reaches the nearer end of the word.
example : manacher #['a', 'a', 'a', 'a'] = #[0, 0, 1, 1, 2, 1, 1, 0, 0] := by
  rw [manacher_eq]; decide

-- No palindromic factor longer than one letter: every radius is `0`.
example : manacher #['a', 'b', 'c', 'd'] = #[0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [manacher_eq]; decide

-- Empty and one-letter words.
example : manacher (#[] : Array Char) = #[0] := by
  rw [manacher_eq]; decide

example : manacher #['a'] = #[0, 0, 0] := by
  rw [manacher_eq]; decide

-- Centers beyond `2 * w.length` have radius `0`.
example : radius ['a', 'a'] 5 = 0 := by decide

/-! ## Executable checks and comparison counts -/

#guard manacher "abacaba".toList.toArray = #[0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0]
#guard manacher "abaxabaxabb".toList.toArray =
  #[0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0]
#guard manacher "aaaaaaaa".toList.toArray = #[0, 0, 1, 1, 2, 2, 3, 3, 4, 3, 3, 2, 2, 1, 1, 0, 0]

-- The comparison counts stay within `manacherM_time_le`'s `3 * w.size`.
#guard (manacherM "abacaba".toList.toArray).time = 7
#guard (manacherM "abba".toList.toArray).time = 4
#guard (manacherM "abcd".toList.toArray).time = 5
#guard (manacherM "aaaaaaaa".toList.toArray).time = 7
#guard (manacherM (#[] : Array Char)).time = 0

-- Near-tightness of `manacherM_time_le`: `a b^(n - 2) c` costs `3 * n - 6` comparisons
-- (`n = 10` and `n = 20`).
#guard (manacherM "abbbbbbbbc".toList.toArray).time = 24
#guard (manacherM "abbbbbbbbc".toList.toArray).time ≤ 3 * 10
#guard (manacherM ("a" ++ String.ofList (List.replicate 18 'b') ++ "c").toList.toArray).time = 54

-- One extension phase about the middle of "abacaba", from radius `0`: three successful
-- comparisons, then it stops at the ends of the word without a fourth one.
#guard (extendM "abacaba".toList.toArray 3 4).ret = 3
#guard (extendM "abacaba".toList.toArray 3 4).time = 3
-- A failed comparison costs one tick.
#guard (extendM "abcd".toList.toArray 1 2).ret = 0
#guard (extendM "abcd".toList.toArray 1 2).time = 1

/-! ## Longest palindromic factor and palindromic prefixes -/

example : longestPalindrome ['x', 'a', 'b', 'a', 'c', 'a', 'b', 'a', 'y'] =
    ['a', 'b', 'a', 'c', 'a', 'b', 'a'] := by
  decide

#guard (longestPalindromeM "xabacabay".toList.toArray).ret = (1, 8)
#guard (longestPalindromeM "abcd".toList.toArray).ret = (0, 1)

-- `extract_longestPalindromeM` and `longestPalindromeM_time_le` on a concrete word.
example : ['x', 'a', 'b', 'a', 'c', 'a', 'b', 'a', 'y'].extract
      (longestPalindromeM #['x', 'a', 'b', 'a', 'c', 'a', 'b', 'a', 'y']).ret.1
      (longestPalindromeM #['x', 'a', 'b', 'a', 'c', 'a', 'b', 'a', 'y']).ret.2 =
    ['a', 'b', 'a', 'c', 'a', 'b', 'a'] := by
  rw [show ['x', 'a', 'b', 'a', 'c', 'a', 'b', 'a', 'y'] =
    (#['x', 'a', 'b', 'a', 'c', 'a', 'b', 'a', 'y'] : Array Char).toList from rfl,
    extract_longestPalindromeM]
  decide

example : (longestPalindromeM #['x', 'a', 'b', 'a', 'c', 'a', 'b', 'a', 'y']).time ≤ 27 :=
  longestPalindromeM_time_le _

-- Non-vacuity of `length_le_longestPalindrome`: the palindromic factor "aca" of "xabacabay"
-- bounds the longest palindrome's length below by `3`.
example : 3 ≤ (longestPalindrome ['x', 'a', 'b', 'a', 'c', 'a', 'b', 'a', 'y']).length :=
  length_le_longestPalindrome (u := ['a', 'c', 'a'])
    ⟨['x', 'a', 'b'], ['b', 'a', 'y'], rfl⟩ (List.Palindrome.of_reverse_eq rfl)

-- `palindrome_extract_iff_le_radius` on "abacaba": the factor `[1, 6)` = "bacab" has center `7`.
example : (['a', 'b', 'a', 'c', 'a', 'b', 'a'].extract 1 6).Palindrome :=
  (palindrome_extract_iff_le_radius (by omega) (by decide)).mpr (by decide)

-- `palindrome_take_iff`: "aba" is a palindromic prefix of "abacaba", "ab" is not.
example : (['a', 'b', 'a', 'c', 'a', 'b', 'a'].take 3).Palindrome :=
  (palindrome_take_iff (by decide)).mpr (by decide)

example : ¬ (['a', 'b', 'a', 'c', 'a', 'b', 'a'].take 2).Palindrome := by
  rw [palindrome_take_iff (by decide)]
  decide

end Cslib.Algorithms.Lean.Palindrome.Tests
