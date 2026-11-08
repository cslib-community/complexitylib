/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (test driver)

import Complexity.Init
import Complexity.Algorithms.Lean.KMP.Search
import Complexity.Algorithms.Lean.ZFunction.Basic
import Complexity.Algorithms.Lean.ZFunction.Search
import Mathlib.Data.Char

/-!
# Z-algorithm tests

Executable `#guard` checks and kernel-checked instances for `Cslib.Algorithms.Lean.ZFunction`
(`Basic.lean` and `Search.lean`) and `List.lcpLen`.
-/

namespace Cslib.Algorithms.Lean.ZFunction.Tests

open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.ZFunction

set_option linter.hashCommand false

private def aabxaab : List Char := "aabxaab".toList
private def gusfield : List Char := "aabcaabxaaz".toList

/-! ## The Z-function -/

-- `aabxaab`: the suffix `aab` at position 4 repeats the prefix `aab`.
#guard zFunction aabxaab = [7, 1, 0, 0, 3, 1, 0]
#guard zAlgorithm aabxaab = zFunction aabxaab
#guard zFunction gusfield = [11, 1, 0, 0, 3, 1, 0, 0, 2, 1, 0]
#guard zAlgorithm gusfield = zFunction gusfield
#guard zAlgorithm "abacaba".toList = [7, 0, 1, 0, 3, 0, 1]
#guard zAlgorithm "abababab".toList = [8, 0, 6, 0, 4, 0, 2, 0]
-- Edge cases: the empty word, one letter, a constant word.
#guard zAlgorithm ([] : List Char) = []
#guard zAlgorithm "a".toList = [1]
#guard zAlgorithm "aaaa".toList = [4, 3, 2, 1]

-- A kernel-checked instance of the specification.
example : zFunction [0, 0, 1] = [3, 1, 0] := by
  apply List.ext_getElem (by simp only [length_zFunction, List.length_cons, List.length_nil])
  intro i h1 _
  rw [getElem_zFunction]
  simp only [length_zFunction, List.length_cons, List.length_nil] at h1
  match i with
  | 0 | 1 | 2 => rfl
  | _ + 3 => omega

/-! ## Character comparisons -/

-- `a ^ (n - 1) b` attains the bound `2 * n - 3` for `n ≥ 2`.
#guard (zAlgorithmM "ab".toList.toArray).time = 1
#guard (zAlgorithmM "aab".toList.toArray).time = 3
#guard (zAlgorithmM "aaab".toList.toArray).time = 5
#guard (zAlgorithmM "aaaab".toList.toArray).time = 7
#guard (zAlgorithmM "aaaaaaaaab".toList.toArray).time = 2 * 10 - 3
-- A constant word: `n - 1` matches, then every position is copied.
#guard (zAlgorithmM "aaaaaaaa".toList.toArray).time = 7
#guard (zAlgorithmM gusfield.toArray).time ≤ 2 * 11 - 3
#guard (zAlgorithmM ([] : List Char).toArray).time = 0
#guard (zAlgorithmM "a".toList.toArray).time = 0

-- The bound is a theorem for every input.
example (s : Array Char) : (zAlgorithmM s).time ≤ 2 * s.size - 3 := zAlgorithmM_time_le s

/-! ## Pattern matching -/

#guard zMatches "aab".toList aabxaab = [0, 4]
#guard zMatches "aab".toList aabxaab = KMP.kmpMatchesList "aab".toList aabxaab
#guard zMatches "aba".toList "abababa".toList = [0, 2, 4]
#guard zMatches "aba".toList "abababa".toList = KMP.kmpMatchesList "aba".toList "abababa".toList
-- The pattern overlaps itself and runs into the text: values above `|p|` are allowed.
#guard zMatches "aa".toList "aaaa".toList = [0, 1, 2]
-- No occurrence; a pattern longer than the text.
#guard zMatches "xyz".toList aabxaab = []
#guard zMatches "aabxaabx".toList aabxaab = []
-- The empty pattern occurs at every shift `0, …, |t|`, as in KMP.
#guard zMatches ([] : List Char) "abc".toList = [0, 1, 2, 3]
#guard zMatches ([] : List Char) "abc".toList = KMP.kmpMatchesList [] "abc".toList
#guard zMatches "a".toList ([] : List Char) = []
#guard (zMatchesM "aab".toList.toArray aabxaab.toArray).time ≤ 2 * (3 + 7) - 3

-- Correctness and agreement with KMP are theorems for every input.
example (p t : List Char) : zMatches p t = KMP.kmpMatchesList p t :=
  zMatches_eq_kmpMatchesList p t

/-! ## Longest common prefix -/

#guard List.lcpLen "abcd".toList "abxd".toList = 2
#guard List.lcpLen "abc".toList "abc".toList = 3
#guard List.lcpLen ([] : List Char) "abc".toList = 0
example : List.lcpLen [1, 2, 3] [1, 2, 4] = 2 := by decide

end Cslib.Algorithms.Lean.ZFunction.Tests
