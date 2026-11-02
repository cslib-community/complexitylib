/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.Data.BitString.List.Segmented

open Cslib.BitString.Segmented

private def sample : List (List (Entry 1)) :=
  [[(0, true), (1, false)], [], [(1, true)]]

-- Nonempty and empty segments, both marks, and both width-one offsets.
example : encode sample =
    [true, false, true, true, true, false, false, false, true, true, true, false] := by
  decide

example : decode 1 (encode sample) = some sample := by decide

example : (encode sample).length = 12 ∧ entryCount sample = 3 := by decide

-- Offsets in a one-position segment require no bits, while tags and marks remain distinct.
example : encode (k := 0) [[(0, false)], [], [(0, true)]] =
    [true, false, false, false, true, true, false] := by decide

example : decode 0 (encode (k := 0) [[(0, false)], [], [(0, true)]]) =
    some [[(0, false)], [], [(0, true)]] := by decide

-- The parser rejects an entry missing its offset or its mark.
example : decode 1 [true] = none ∧ decode 1 [true, false] = none := by decide

-- Empty supports still pay one delimiter per segment.
example : supportCode (k := 2) (blocks := 3) (fun _ _ => none) = [false, false, false] := by
  decide

private def marked : Fin 2 → Fin 4 → Option Bool :=
  fun block offset =>
    if block.val = 0 ∧ offset.val = 3 then some true
    else if block.val = 1 ∧ offset.val = 0 then some false
    else none

example : supportSegments (k := 2) marked = [[(3, true)], [(0, false)]] := by decide

example : (supportCode (k := 2) marked).length = 10 := by decide

-- A mark change changes the code, even when the unmarked support set stays the same.
example : supportCode (k := 0) (blocks := 1) (fun _ _ => some false) ≠
    supportCode (k := 0) (blocks := 1) (fun _ _ => some true) := by decide
