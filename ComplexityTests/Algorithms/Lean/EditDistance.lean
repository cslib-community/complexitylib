/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Algorithms.Lean.EditDistance.LCS

/-!
# Edit distance and longest common subsequence: worked examples

Kernel-checked examples (`decide`, no `native_decide`) for the Wagner–Fischer edit distance, its
traceback and its `TimeM` cost, and for the longest-common-subsequence table and its traceback.
The examples include the textbook pairs kitten/sitting and flaw/lawn, the strings of the running
example of [CLRS, Section 15.4][CLRS2009], empty words, and letter costs that are neither unit nor
symmetric.
-/

public section

namespace ComplexityTests.EditDistance

open scoped List
open Cslib.Algorithms.Lean.EditDistance

/-- `kitten`. -/
@[expose] def kitten : List Char := ['k', 'i', 't', 't', 'e', 'n']
/-- `sitting`. -/
@[expose] def sitting : List Char := ['s', 'i', 't', 't', 'i', 'n', 'g']
/-- `flaw`. -/
@[expose] def flaw : List Char := ['f', 'l', 'a', 'w']
/-- `lawn`. -/
@[expose] def lawn : List Char := ['l', 'a', 'w', 'n']

/-! ### Unit costs (Levenshtein) -/

example : editDist Costs.unit kitten sitting = 3 := by decide
example : editDist Costs.unit flaw lawn = 2 := by decide
example : editDist Costs.unit kitten kitten = 0 := by decide

/-- The traceback on kitten/sitting: two replacements and an insertion. -/
example : optScript Costs.unit kitten sitting =
    [.sub 'k' 's', .sub 'i' 'i', .sub 't' 't', .sub 't' 't', .sub 'e' 'i', .sub 'n' 'n',
      .ins 'g'] := by decide

/-- The traceback on flaw/lawn: a deletion and an insertion. -/
example : optScript Costs.unit flaw lawn =
    [.del 'f', .sub 'l' 'l', .sub 'a' 'a', .sub 'w' 'w', .ins 'n'] := by decide

/-- A script of cost `3` from kitten to sitting is optimal: no script costs less. -/
example (s : EditScript Char) (hs : s.src = kitten) (ht : s.tgt = sitting) :
    3 ≤ s.cost Costs.unit := by
  have h := (isLeast_editDist Costs.unit kitten sitting).2 ⟨s, hs, ht, rfl⟩
  rwa [show editDist Costs.unit kitten sitting = 3 by decide] at h

/-! ### Empty words -/

example : editDist Costs.unit ([] : List Char) [] = 0 := by decide
example : editDist Costs.unit [] sitting = 7 := by decide
example : editDist Costs.unit kitten [] = 6 := by decide
example : optScript Costs.unit [] ['a', 'b'] = [.ins 'a', .ins 'b'] := by decide
example : optScript Costs.unit ['a', 'b'] [] = [.del 'a', .del 'b'] := by decide

/-! ### Costs that are neither unit nor symmetric -/

/-- Deleting costs `3`, inserting costs `2`, and replacing by a different letter costs `4`. -/
@[expose] def skewed : Costs Char where
  del _ := 3
  ins _ := 2
  sub a b := if a = b then 0 else 4

/-- A replacement (`4`) is cheaper than a deletion and an insertion (`5`). -/
example : editDist skewed ['a'] ['b'] = 4 := by decide
/-- Swapping two letters: insert, keep, delete (`5`) beats two replacements (`8`). -/
example : editDist skewed ['a', 'b'] ['b', 'a'] = 5 := by decide
example : optScript skewed ['a', 'b'] ['b', 'a'] = [.del 'a', .sub 'b' 'b', .ins 'a'] := by
  decide
/-- The distance is not symmetric for these costs. -/
example : editDist skewed ['a'] [] = 3 ∧ editDist skewed [] ['a'] = 2 := by decide

/-! ### Cost of the algorithm -/

example : (editDistM Costs.unit kitten sitting).ret = 3 := by decide
/-- `(6 + 1) (7 + 1) = 56` table entries. -/
example : (editDistM Costs.unit kitten sitting).time = 56 := by decide
example : (editDistM Costs.unit ([] : List Char) []).time = 1 := by decide

/-! ### Longest common subsequence -/

/-- `ABCBDAB`, from the running example of [CLRS, Section 15.4][CLRS2009]. -/
@[expose] def clrsX : List Char := ['A', 'B', 'C', 'B', 'D', 'A', 'B']
/-- `BDCABA`, from the running example of [CLRS, Section 15.4][CLRS2009]. -/
@[expose] def clrsY : List Char := ['B', 'D', 'C', 'A', 'B', 'A']

example : lcsLength clrsX clrsY = 4 := by decide
/-- The traceback prefers dropping a letter of the first word on ties, so it returns `BDAB`;
the CLRS traceback returns `BCBA`. Both are longest common subsequences. -/
example : lcs clrsX clrsY = ['B', 'D', 'A', 'B'] := by decide
example : ['B', 'C', 'B', 'A'] <+ clrsX ∧ ['B', 'C', 'B', 'A'] <+ clrsY := by decide
example : lcsLength kitten sitting = 4 := by decide
example : lcsLength ([] : List Char) clrsY = 0 := by decide
example : lcsLength ['a', 'b'] ['c', 'd'] = 0 := by decide
example : (lcsLengthM clrsX clrsY).time = 56 := by decide

/-- No common subsequence of the CLRS strings is longer than `4`. -/
example (z : List Char) (hx : z <+ clrsX) (hy : z <+ clrsY) : z.length ≤ 4 := by
  have h := length_le_lcsLength hx hy
  rwa [show lcsLength clrsX clrsY = 4 by decide] at h

/-- The duality `editDist Costs.indel x y + 2 · lcsLength x y = |x| + |y|`: `5 + 2 · 4 = 7 + 6`. -/
example : editDist Costs.indel clrsX clrsY = 5 := by decide
example : editDist Costs.indel kitten sitting = 5 := by
  have h := editDist_indel_add_two_mul kitten sitting
  rw [show lcsLength kitten sitting = 4 by decide] at h
  simpa [kitten, sitting] using h

/-- `optScript Costs.indel` may return a replacement by a different letter, at cost `2`; a script
without one (delete, then insert) costs the same. -/
example : optScript Costs.indel ['a'] ['b'] = [.sub 'a' 'b'] := by decide
example : ∃ s : EditScript Char, s.IsIndel ∧ s.src = ['a'] ∧ s.tgt = ['b'] ∧
    s.cost Costs.indel = 2 := by
  have h := (isLeast_editDist_indel ['a'] ['b']).1
  rwa [show editDist Costs.indel ['a'] ['b'] = 2 by decide] at h

end ComplexityTests.EditDistance
