/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (test driver)

import CslibFrontier.Init
import CslibFrontier.Algorithms.Lean.BinarySearch
import CslibFrontier.Algorithms.Lean.KMP.Search
import CslibFrontier.Algorithms.Lean.SuffixArray.Basic
import CslibFrontier.Algorithms.Lean.SuffixArray.Kasai
import CslibFrontier.Algorithms.Lean.SuffixArray.Search
import Mathlib.Data.Char

/-!
# Suffix array, Kasai LCP and suffix-array search tests

Executable `#guard` checks and non-vacuity instantiations for `Cslib.Algorithms.Lean.lowerBoundM`
and `Cslib.Algorithms.Lean.SuffixArray` (`Basic.lean`, `Kasai.lean` and `Search.lean`).
-/

namespace Cslib.Algorithms.Lean.SuffixArray.Tests

open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.SuffixArray

set_option linter.hashCommand false

private def banana : List Char := "banana".toList
private def mississippi : List Char := "mississippi".toList

/-! ## Binary search -/

-- The first failing index of `m < 7` on `[0, 100)` is `7`, found with at most
-- `⌊log₂ 100⌋ + 1 = 7` charged probes.
#guard (lowerBoundM (fun m => pure (decide (m < 7))) 0 100).ret = 7
#guard (lowerBoundM (fun m => do TimeM.tick 1; pure (decide (m * m ≤ 50))) 0 100).ret = 8
#guard (lowerBoundM (fun m => do TimeM.tick 1; pure (decide (m * m ≤ 50))) 0 100).time ≤
  Nat.log 2 100 + 1
-- Empty interval: no probes.
#guard (lowerBoundM (fun _ => do TimeM.tick 1; pure true) 5 5).ret = 5
#guard (lowerBoundM (fun _ => do TimeM.tick 1; pure true) 5 5).time = 0

/-! ## Suffix arrays -/

-- banana: a(5) < ana(3) < anana(1) < banana(0) < na(4) < nana(2).
#guard suffixArray banana = [5, 3, 1, 0, 4, 2]
#guard suffixArray mississippi = [10, 7, 4, 1, 0, 9, 8, 6, 3, 5, 2]
#guard suffixArray ([] : List Char) = []
#guard suffixArray "aaaa".toList = [3, 2, 1, 0]

-- The specification holds for the sorted positions and fails for other permutations or
-- non-permutations.
#guard decide (IsSuffixArray banana [5, 3, 1, 0, 4, 2])
#guard !decide (IsSuffixArray banana [0, 1, 2, 3, 4, 5])
#guard !decide (IsSuffixArray banana [5, 3, 1, 0, 4])
#guard !decide (IsSuffixArray banana [5, 3, 1, 0, 4, 2, 6])
#guard decide (IsSuffixArray ([] : List Char) [])

-- Uniqueness: a kernel-checked suffix array of `banana` is the only one.
example (sa : List ℕ) (h : IsSuffixArray ['b', 'a', 'n', 'a', 'n', 'a'] sa) :
    sa = [5, 3, 1, 0, 4, 2] :=
  h.unique (by decide)

/-! ## LCP arrays and Kasai et al.'s algorithm -/

#guard lcpArray banana (suffixArray banana) = [0, 1, 3, 0, 0, 2]
#guard kasai banana (suffixArray banana) = [0, 1, 3, 0, 0, 2]
#guard lcpArray mississippi (suffixArray mississippi) = [0, 1, 1, 4, 0, 0, 1, 0, 2, 1, 3]
#guard kasai mississippi (suffixArray mississippi) = [0, 1, 1, 4, 0, 0, 1, 0, 2, 1, 3]
#guard kasai ([] : List Char) [] = []
#guard kasai "aaaaaaaaaa".toList (suffixArray "aaaaaaaaaa".toList) =
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

-- Character comparisons stay below `2 * |w|`.
#guard (kasaiM banana.toArray (suffixArray banana).toArray).time = 5
#guard (kasaiM mississippi.toArray (suffixArray mississippi).toArray).time ≤ 2 * 11
#guard (kasaiM "aaaaaaaaaa".toList.toArray (suffixArray "aaaaaaaaaa".toList).toArray).time ≤
  2 * 10

-- The height lemma on `banana`: `lcp[rank[i + 1]] ≥ lcp[rank[i]] - 1` for all `i < |w| - 1`.
#guard
  let sa := suffixArray banana
  let lcp := lcpArray banana sa
  let rk := rankArray banana.length sa
  (List.range (banana.length - 1)).all fun i => lcp[rk[i]!]! - 1 ≤ lcp[rk[i + 1]!]!

-- Non-vacuity: the correctness hypothesis is met by the reference construction.
example (w : List Char) : kasai w (suffixArray w) = lcpArray w (suffixArray w) :=
  kasai_eq_lcpArray (isSuffixArray_suffixArray w)

example (w : List Char) :
    (kasaiM w.toArray (suffixArray w).toArray).time ≤ 2 * w.length := by
  simpa only [List.size_toArray] using kasaiM_time_le w.toArray (suffixArray w).toArray

/-! ## Pattern search -/

-- "ana" occurs at positions 3 and 1 of `banana`, ranks 1 and 2.
#guard search banana (suffixArray banana) "ana".toList = (1, 3)
#guard occurrences banana (suffixArray banana) "ana".toList = [3, 1]
#guard occurrences mississippi (suffixArray mississippi) "issi".toList = [4, 1]
#guard occurrences mississippi (suffixArray mississippi) "ssi".toList = [5, 2]
#guard occurrences mississippi (suffixArray mississippi) "i".toList = [10, 7, 4, 1]
#guard occurrences mississippi (suffixArray mississippi) "mississippi".toList = [0]
-- Absent patterns, including one longer than the text.
#guard occurrences banana (suffixArray banana) "nab".toList = []
#guard occurrences banana (suffixArray banana) "bananas".toList = []
#guard occurrences banana (suffixArray banana) "z".toList = []
-- The empty pattern occurs at every position `i < |w|`.
#guard search mississippi (suffixArray mississippi) [] = (0, 11)
#guard occurrences ([] : List Char) [] "a".toList = []

-- Cross-check against KMP: same positions, except that KMP also reports the empty-suffix
-- position `|w|` for the empty pattern.
#guard (["ana", "na", "a", "b", "banana", "x", ""].map String.toList).all fun p =>
  (occurrences banana (suffixArray banana) p).mergeSort (· ≤ ·) =
    (KMP.kmpMatchesList p banana).filter (· < banana.length)
#guard (["ssi", "issi", "i", "s", "pp", "mississippi", "sis", ""].map String.toList).all fun p =>
  (occurrences mississippi (suffixArray mississippi) p).mergeSort (· ≤ ·) =
    (KMP.kmpMatchesList p mississippi).filter (· < mississippi.length)

-- Character comparisons stay below `2 * |p| * (⌊log₂ |sa|⌋ + 1)`.
#guard (searchM mississippi.toArray (suffixArray mississippi).toArray "ssi".toList).time ≤
  2 * (3 * (Nat.log 2 11 + 1))
#guard (searchM banana.toArray (suffixArray banana).toArray []).time = 0

-- Non-vacuity: the correctness hypothesis is met by the reference construction.
example (w p : List Char) (i : ℕ) :
    i ∈ occurrences w (suffixArray w) p ↔ i < w.length ∧ p <+: w.drop i :=
  mem_occurrences (isSuffixArray_suffixArray w) p

end Cslib.Algorithms.Lean.SuffixArray.Tests
