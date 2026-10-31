/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (test driver)

import Complexity.Init
import Complexity.Algorithms.Lean.KMP.Basic
import Complexity.Algorithms.Lean.KMP.Search

/-!
# Knuth–Morris–Pratt String Matching Tests

Executable `#guard` checks and non-vacuity theorem instantiations for
`Cslib.Algorithms.Lean.KMP` (`Basic.lean` and `Search.lean`).
-/

namespace Cslib.Algorithms.Lean.KMP.Tests

open Cslib.Algorithms.Lean.KMP

set_option linter.hashCommand false

/-! ## Border, period, and `[CLRS2009]` Figures 32.10–32.11 failure-table checks -/

private def clrsPat : Array Char := "ababaca".toList.toArray

-- `[CLRS2009]`, Figure 32.10(c): π for "ababaca" is [0, 0, 1, 2, 3, 0, 1].
#guard computePrefix clrsPat = #[0, 0, 1, 2, 3, 0, 1]
#guard (computePrefixM clrsPat).time ≤ 2 * (clrsPat.size - 1)

-- `[CLRS2009]`, Lemma 32.5 & Figure 32.11: proper border chains via π* iteration.
#guard borderChain "ababaca".toList 5 = [3, 1, 0]
#guard borderChain "ababaca".toList 7 = [1, 0]
#guard borderChain "ababaca".toList 0 = []
#guard borderChain "ababababca".toList 8 = [6, 4, 2, 0]

-- Minimum period checks (`minPeriod w + maxBorderLen w = w.length`).
#guard maxBorderLen "ababab".toList = 4
#guard minPeriod "ababab".toList = 2
#guard maxBorderLen "ababaca".toList = 1
#guard minPeriod "ababaca".toList = 6

/-! ## Edge cases: empty pattern, empty text, singleton, and overlapping matches -/

-- Empty pattern matches at every position `0 .. t.size` with 0 comparisons.
#guard computePrefix (#[] : Array Nat) = #[]
#guard (computePrefixM (#[] : Array Nat)).time = 0
#guard kmpMatches (#[] : Array Nat) #[10, 20, 30] = [0, 1, 2, 3]
#guard (kmpSearchM (#[] : Array Nat) #[10, 20, 30]).time = 0
#guard kmpMatches (#[] : Array Nat) (#[] : Array Nat) = [0]

-- Nonempty pattern against empty text or shorter text.
#guard kmpMatches #[1] (#[] : Array Nat) = []
#guard kmpMatches #[1, 2, 3, 4] #[1, 2] = []

-- Singleton pattern.
#guard computePrefix #[7] = #[0]
#guard (computePrefixM #[7]).time = 0
#guard kmpMatches #[7] #[7, 3, 7, 7] = [0, 2, 3]

-- Overlapping occurrences (`"aba"` in `"abababa"`, `"aa"` in `"aaaa"`).
#guard kmpMatches #[0, 1, 0] #[0, 1, 0, 1, 0, 1, 0] = [0, 2, 4]
#guard kmpMatches #[1, 1] #[1, 1, 1, 1] = [0, 1, 2]
#guard kmpMatchesList "aba".toList "babababab".toList = [1, 3, 5]

-- Adversarial fallback chain (`p = "aaaaab"`, `t = "aaaaaaaaaaab"`).
private def advPat : Array Char := "aaaaab".toList.toArray
private def advTxt : Array Char := "aaaaaaaaaaab".toList.toArray

#guard computePrefix advPat = #[0, 1, 2, 3, 4, 0]
#guard (computePrefixM advPat).time = 9
#guard (computePrefixM advPat).time ≤ 2 * (advPat.size - 1)
#guard kmpMatches advPat advTxt = [6]
#guard (kmpSearchM advPat advTxt).time ≤ 2 * (advPat.size - 1) + 2 * advTxt.size

/-! ## Non-vacuity and universe-polymorphism checks -/

-- Concrete witness for `IsPrefixTableFor` and `IsDecreasingTable`.
example : IsPrefixTableFor advPat (computePrefix advPat) ∧
    IsDecreasingTable (computePrefix advPat) :=
  ⟨(isPrefixTableFor_computePrefix advPat).2, isDecreasingTable_computePrefix advPat⟩

-- Concrete witness for `IsMatchAt`, `mem_kmpMatches_iff`, ordering, and comparison bounds.
example : IsMatchAt advPat advTxt 6 ∧
    6 ∈ kmpMatches advPat advTxt ∧
    (∀ s, s ∈ kmpMatches advPat advTxt ↔ IsMatchAt advPat advTxt s) ∧
    (kmpMatches advPat advTxt).Pairwise (· < ·) ∧
    (kmpMatches advPat advTxt).Nodup ∧
    (kmpSearchM advPat advTxt).time ≤ 2 * (advPat.size - 1) + 2 * advTxt.size :=
  have hmatch : IsMatchAt advPat advTxt 6 := ⟨by decide, by decide⟩
  ⟨hmatch,
    (mem_kmpMatches_iff advPat advTxt 6).mpr hmatch,
    mem_kmpMatches_iff advPat advTxt,
    pairwise_lt_kmpMatches advPat advTxt,
    nodup_kmpMatches advPat advTxt,
    kmpSearchM_time_le advPat advTxt⟩

-- Concrete witness for border-period duality, `minPeriod_le_of_isPeriod`, and `borderChain`.
example : IsPeriod "ababab".toList 2 ∧
    minPeriod "ababab".toList ≤ 4 ∧
    minPeriod "ababab".toList ≤ 10 ∧
    (3 ∈ borderChain "ababaca".toList 5 ↔
      IsProperBorderLen ("ababaca".toList.take 5) 3) :=
  have hper4 : IsPeriod "ababab".toList 4 :=
    ((isProperBorderLen_iff_isPeriod (w := "ababab".toList) (k := 2)).mp ⟨by decide, by decide⟩).2
  have hper10 : IsPeriod "ababab".toList 10 :=
    fun _ h => absurd (Nat.lt_of_add_left_lt h) (by decide)
  ⟨isPeriod_minPeriod (w := "ababab".toList) (by decide),
    minPeriod_le_of_isPeriod (by decide) hper4,
    minPeriod_le_of_isPeriod (by decide) hper10,
    mem_borderChain_iff (p := "ababaca".toList) (q := 5) (j := 3) (by decide) (by decide)⟩

-- Universe-polymorphic instantiation (`Type 1` via `ULift.{1} Nat`).
example (p t : Array (ULift.{1} Nat)) :
    (∀ s, s ∈ kmpMatches p t ↔ IsMatchAt p t s) ∧
      (kmpSearchM p t).time ≤ 2 * (p.size - 1) + 2 * t.size :=
  ⟨mem_kmpMatches_iff p t, kmpSearchM_time_le p t⟩

end Cslib.Algorithms.Lean.KMP.Tests
