/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (test driver)

import Complexity.Init
import Complexity.Algorithms.Lean.BurrowsWheeler.Basic
import Complexity.Algorithms.Lean.BurrowsWheeler.Decode
import Mathlib.Data.Char

/-!
# Burrows–Wheeler Transform Tests

Executable `#guard` checks and non-vacuity instantiations for
`Cslib.Algorithms.Lean.BurrowsWheeler` (`Basic.lean` and `Decode.lean`).
-/

namespace Cslib.Algorithms.Lean.BurrowsWheeler.Tests

open Cslib.Algorithms.Lean.BurrowsWheeler

set_option linter.hashCommand false

/-! ## The running example of [BurrowsWheeler1994], Section 2 -/

-- Algorithm C on `S = abraca`: `L = caraab`, `I = 1`.
#guard bwt "abraca".toList = ("caraab".toList, 1)
-- Step D1: `F = aaabcr`.
#guard bwtFirst "abraca".toList = "aaabcr".toList
-- Step D2: `T = (4 0 5 1 2 3)`.
#guard (List.range 6).map (lfMap "caraab".toList) = [4, 0, 5, 1, 2, 3]
-- Section 4.2: the rank array `P` for `L = caraab`.
#guard rankTable "caraab".toList = [0, 0, 0, 1, 2, 0]
#guard inverseBwt ("caraab".toList, 1) = "abraca".toList
#guard (inverseBwtM ("caraab".toList, 1)).ret = "abraca".toList
#guard (inverseBwtM ("caraab".toList, 1)).time = 6

/-! ## Further examples -/

#guard bwt "banana".toList = ("nnbaaa".toList, 3)
#guard inverseBwt ("nnbaaa".toList, 3) = "banana".toList
-- A periodic word, `(can)^2` (the remark after step D3).
#guard bwt "cancan".toList = ("ccnnaa".toList, 2)
#guard (inverseBwtM ("ccnnaa".toList, 2)).ret = "cancan".toList
#guard (inverseBwtM ("ccnnaa".toList, 2)).time = 6
-- The LF orbit of `I = 2` for `cancan` repeats with period 3: `[2, 4, 0, 2, 4, 0]`.
#guard (List.range 6).map (fun i => (lfMap "ccnnaa".toList)^[i] 2) = [2, 4, 0, 2, 4, 0]

/-! ## Edge cases -/

#guard bwt ([] : List Char) = ([], 0)
#guard inverseBwt (([] : List Char), 0) = []
#guard bwt "x".toList = ("x".toList, 0)
#guard bwt "aaaa".toList = ("aaaa".toList, 0)
#guard inverseBwt ("aaaa".toList, 0) = "aaaa".toList
-- Without the index, the transform is not injective: `ab` and `ba` share `L`.
#guard bwtLast "ab".toList = bwtLast "ba".toList
#guard bwt "ab".toList ≠ bwt "ba".toList
-- Natural-number alphabets: rotations share `L` and are told apart by the index.
#guard bwt [3, 1, 2] = ([3, 1, 2], 2)
#guard bwt [2, 3, 1] = ([3, 1, 2], 1)
#guard inverseBwt ([3, 1, 2], 2) = [3, 1, 2]
#guard inverseBwt ([3, 1, 2], 1) = [2, 3, 1]

/-! ## Non-vacuity of the main theorems -/

example : inverseBwt (bwt [2, 7, 1, 8, 2, 8]) = [2, 7, 1, 8, 2, 8] := inverseBwt_bwt _

example : bwt [1, 2] ≠ bwt [2, 1] := fun h => by
  have := bwt_injective h
  simp at this

example :
    (inverseBwtM (bwt [3, 1, 4, 1, 5, 9, 2, 6])).ret = [3, 1, 4, 1, 5, 9, 2, 6] ∧
      (inverseBwtM (bwt [3, 1, 4, 1, 5, 9, 2, 6])).time = 8 :=
  inverseBwtM_bwt _

example : bwtFirst [3, 1, 2] = (bwtLast [3, 1, 2]).mergeSort (· ≤ ·) :=
  bwtFirst_eq_mergeSort_bwtLast _

example :
    ((List.range (bwtMatrix "cancan".toList).length).map (lfMap (bwtLast "cancan".toList))).Perm
      (List.range (bwtMatrix "cancan".toList).length) :=
  map_lfMap_range_perm _

end Cslib.Algorithms.Lean.BurrowsWheeler.Tests
