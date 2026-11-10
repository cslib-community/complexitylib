/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (test driver)

import CslibFrontier.Init
import CslibFrontier.Algorithms.Lean.AhoCorasick.Basic
import CslibFrontier.Algorithms.Lean.AhoCorasick.Search
import CslibFrontier.Algorithms.Lean.AhoCorasick.KMP

/-!
# Aho–Corasick String Matching Tests

Executable `#guard` checks and non-vacuity theorem instantiations for
`Cslib.Algorithms.Lean.AhoCorasick` (`Basic.lean`, `Search.lean` and `KMP.lean`).
-/

namespace Cslib.Algorithms.Lean.AhoCorasick.Tests

open Cslib.Algorithms.Lean.AhoCorasick

set_option linter.hashCommand false

/-! ## `[AhoCorasick1975]`, Figures 1 and 2: keywords `he`, `she`, `his`, `hers` on `ushers` -/

private def kw : List (List Char) := ["he", "she", "his", "hers"].map String.toList
private def ushers : List Char := "ushers".toList

-- Figure 2: `she` and `he` end at position 4 and `hers` at position 6.
#guard search kw ushers = [(4, "she".toList), (4, "he".toList), (6, "hers".toList)]
#guard search kw ushers = occurrences kw ushers

-- Figure 1(b): the failure function on the states 1, …, 9.
#guard ["h", "he", "s", "sh", "she", "hi", "his", "her", "hers"].map
    (fun s => (build kw).fail s.toList) =
  ["", "", "", "h", "he", "", "s", "", "s"].map String.toList

-- Figure 1(c): the output function.
#guard (build kw).out "he".toList = ["he".toList]
#guard (build kw).out "she".toList = ["she".toList, "he".toList]
#guard (build kw).out "his".toList = ["his".toList]
#guard (build kw).out "hers".toList = ["hers".toList]
#guard (build kw).out "sh".toList = []

-- Figure 2: seven goto and failure transitions on the six symbols of `ushers` (Theorem 2:
-- fewer than `2 * 6`), plus one tick for each of the three reported pairs.
#guard (scanM kw ⟨(build kw).fail, fun _ => []⟩ ushers).time = 7
#guard (scanM kw (build kw) ushers).time = 10
#guard (buildM kw).time = 8
#guard (buildM kw).time ≤ (kw.map fun p => 2 * (p.length - 1)).sum
#guard (searchM kw ushers).time = 18
#guard (searchM kw ushers).time ≤
  (kw.map fun p => 2 * (p.length - 1)).sum + 2 * ushers.length + (occurrences kw ushers).length

-- With the constructed output table, a failure table that always fails to the start state
-- misses `hers`.
#guard (scanM kw ⟨fun _ => [], (build kw).out⟩ ushers).ret = [(4, "she".toList), (4, "he".toList)]

/-! ## Edge cases -/

-- Empty text, empty keyword list, and the empty keyword (never reported).
#guard search kw [] = []
#guard (scanM kw (build kw) []).time = 0
#guard search ([] : List (List ℕ)) [1, 2, 3] = []
#guard search [[]] [1, 2] = []
#guard search [[], [1]] [1, 2, 1] = [(1, [1]), (3, [1])]

-- A keyword listed twice is reported once per end position.
#guard search [[1, 1], [1, 1], [2]] [1, 1, 1, 2] = [(2, [1, 1]), (3, [1, 1]), (4, [2])]

-- Keywords that are suffixes of other keywords, and overlapping occurrences.
private def aaa : List (List Char) := ["a", "aa", "aaa"].map String.toList

#guard search aaa "aaaa".toList =
  [(1, "a"), (2, "aa"), (2, "a"), (3, "aaa"), (3, "aa"), (3, "a"), (4, "aaa"), (4, "aa"),
    (4, "a")].map fun (i, y) => (i, y.toList)
#guard (searchM aaa "aaaa".toList).time = 17

/-! ## One keyword: the Knuth–Morris–Pratt special case -/

private def aba : List Char := "aba".toList
private def ababaca : List Char := "ababaca".toList

#guard search [aba] "babababab".toList = [(4, aba), (6, aba), (8, aba)]
#guard search [aba] "babababab".toList =
  (KMP.kmpMatchesList aba "babababab".toList).map fun s => (s + aba.length, aba)
-- `[CLRS2009]`, Figure 32.11(a): π[5] = 3 for `ababaca`.
#guard failure [ababaca] (ababaca.take 5) = ababaca.take (KMP.borderLen ababaca 5)
#guard failure [ababaca] (ababaca.take 5) = "aba".toList

/-! ## Non-vacuity checks -/

-- `IsOccurrence` holds for `hers` at position 6 and fails at position 5.
example : IsOccurrence kw ushers 6 "hers".toList ∧ ¬ IsOccurrence kw ushers 5 "hers".toList :=
  ⟨⟨by decide, by decide, by decide, by decide⟩, fun h => absurd h.2.2.2 (by decide)⟩

/-- `[AhoCorasick1975]`, Figure 1(b): `f(5) = 2`, i.e. the failure state of `she` is `he`. -/
private theorem failure_she : failure kw "she".toList = "he".toList :=
  ((eq_failure_iff (by decide)).mpr ⟨by decide, by decide, by decide, fun x _ hlt _ => by
    have h3 : "she".toList.length = 3 := by decide
    have h2 : "he".toList.length = 2 := by decide
    omega⟩).symm

-- The constructed machine is valid; a machine whose failure table always returns the start state
-- is not.
example : (build kw).IsValid kw ∧ (build kw).fail "she".toList = "he".toList ∧
    ¬ Machine.IsValid kw ⟨fun _ => [], (build kw).out⟩ :=
  ⟨isValid_build kw, ((isValid_build kw) _ (by decide)).1.trans failure_she,
    fun h => absurd ((h "she".toList (by decide)).1.trans failure_she) (by decide)⟩

-- The cost theorems instantiated on the paper's example.
example : (scanM kw ⟨(build kw).fail, fun _ => []⟩ ushers).time < 2 * ushers.length ∧
    (searchM kw ushers).time ≤
      (kw.map fun p => 2 * (p.length - 1)).sum + 2 * ushers.length +
        (occurrences kw ushers).length :=
  ⟨time_scanM_silent_lt kw _ (by decide), time_searchM_le kw ushers⟩

-- Universe-polymorphic instantiation (`Type 1` via `ULift.{1} ℕ`).
example (P : List (List (ULift.{1} ℕ))) (t : List (ULift.{1} ℕ)) :
    search P t = occurrences P t ∧
      (searchM P t).time ≤
        (P.map fun p => 2 * (p.length - 1)).sum + 2 * t.length + (occurrences P t).length :=
  ⟨search_eq P t, time_searchM_le P t⟩

end Cslib.Algorithms.Lean.AhoCorasick.Tests
