/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Tactic.PolyTime

/-! Direct predicate-count and Boolean scans with raw-bit and framed-list input encodings.
The list and the bit to search for are both runtime inputs; empty lists are permitted. -/

namespace ComplexityTests.PolyTimeScans

open Turing.MultiTapeTM ComputableTidilyInPolyTime

private abbrev rawInput := encPair encBits encBool
private abbrev framedInput := encPair (encList encBool) encBool

/-- A captured bit controls the predicate uniformly for every raw input word. -/
theorem raw_count : ComputableTidilyInPolyTime
    (fun p : List Bool × Bool => p.1.countP fun b => b == p.2) rawInput encUnary :=
  countPWith (encA := encBool) (encP := encBool)
    (of_finite (fun p : Bool × Bool => p.2 == p.1)) (snd _ _) (fst _ _)

/-- The same counting rule applies directly to framed lists. -/
theorem framed_count : ComputableTidilyInPolyTime
    (fun p : List Bool × Bool => p.1.countP fun b => b == p.2) framedInput encUnary :=
  countPWith (encA := encBool) (encP := encBool)
    (of_finite (fun p : Bool × Bool => p.2 == p.1)) (snd _ _) (fst _ _)

/-- A matching bit can be sought without converting a raw word to a framed list. -/
theorem raw_any : ComputableTidilyInPolyTime
    (fun p : List Bool × Bool => p.1.any fun b => b == p.2) rawInput encBool :=
  anyWithEncoding (encA := encBool) (encP := encBool)
    (of_finite (fun p : Bool × Bool => p.2 == p.1)) (snd _ _) (fst _ _)

/-- The same universal scan applies to raw words. -/
theorem raw_all : ComputableTidilyInPolyTime
    (fun p : List Bool × Bool => p.1.all fun b => b == p.2) rawInput encBool :=
  allWithEncoding (encA := encBool) (encP := encBool)
    (of_finite (fun p : Bool × Bool => p.2 == p.1)) (snd _ _) (fst _ _)

/-- Existing framed-list theorem names and automation still elaborate unchanged. -/
example : ComputableTidilyInPolyTime
    (fun p : List Bool × Bool => p.1.count p.2) framedInput encUnary := by polytime
example : ComputableTidilyInPolyTime
    (fun p : List Bool × Bool => p.1.any fun b => b == p.2) framedInput encBool := by polytime
example : ComputableTidilyInPolyTime
    (fun p : List Bool × Bool => p.1.all fun b => b == p.2) framedInput encBool := by polytime

-- The raw wrappers use the direct certificates and retain inference of their encodings.
example : ComputableTidilyInPolyTime
    (fun p : List Bool × Bool => p.1.count p.2) rawInput encUnary := by polytime
example : ComputableTidilyInPolyTime
    (fun p : List Bool × Bool => p.1.any fun b => b == p.2) rawInput encBool := by polytime
example : ComputableTidilyInPolyTime
    (fun p : List Bool × Bool => p.1.all fun b => b == p.2) rawInput encBool := by polytime

example : [false, true, false, true, true].countP (· == true) = 3 := by decide
example : [false, true].any (· == true) = true := by decide
example : [false, true].all (· == true) = false := by decide
example : ([] : List Bool).countP (· == true) = 0 := rfl
example : ([] : List Bool).any (· == true) = false := rfl
example : ([] : List Bool).all (· == true) = true := rfl

end ComplexityTests.PolyTimeScans
