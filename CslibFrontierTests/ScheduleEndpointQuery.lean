/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.ScheduleEndpointQuery

open Turing.MultiTapeTM.ScheduleEndpointQuery

-- Two stationary rows: a valid first interval returns the next interval.
example : query 1 ⟨List.replicate 8 false, 1, 0⟩ = some (some 1) := by decide

-- A valid last interval returns exhaustion, distinct from an invalid request.
example : query 1 ⟨List.replicate 8 false, 1, 1⟩ = some none := by decide
example : query 1 ⟨List.replicate 8 false, 1, 2⟩ = none := by decide

-- Malformed pairs, incomplete rows, and non-work-head selectors are rejected.
example : query 1 ⟨[false, false, true, true], 1, 0⟩ = none := by decide
example : query 1 ⟨[false, false], 1, 0⟩ = none := by decide
example : query 1 ⟨List.replicate 8 false, 3, 0⟩ = none := by decide
example : query 0 ⟨[false, false], 0, 0⟩ = none := by decide
example : query 1 ⟨[], 0, 0⟩ = none := by decide

-- A huge runtime index fails the range guard before any query evaluation.
example : query 1 ⟨List.replicate 8 false, 1, 2 ^ 100⟩ = none := by decide

-- Moving right can leave the left outgoing block with no later appearance.
example : query 1 ⟨[false, false, false, true, false, false, false, false], 0, 0⟩ =
    some none := by decide

-- The generic API confirms that valid extraction/decoding cannot reject an input later.
example (a : Input) (ha : valid 2 a = true) : (query 2 a).isSome = true := by
  rw [query_isSome, ha]

-- The reusable pair decoder rejects malformed words independently of the query guard.
example : Turing.MultiTapeTM.ScheduleBits.decodePairs [true, true] = none := by decide
example : Turing.MultiTapeTM.ScheduleBits.decodePairs [false] = none := by decide

-- Runtime selectors distinguish work heads with different movements.
example : query 2
    ⟨[false, false, false, true, false, false, false, false, false, false, false, false], 3, 0⟩ =
    some (some 1) := by decide
example : query 2
    ⟨[false, false, false, true, false, false, false, false, false, false, false, false], 0, 0⟩ =
    some none := by decide

-- The right port remains in the window when the queried movement is rightward.
example : query 1 ⟨[false, false, false, true, false, false, false, false], 2, 0⟩ =
    some (some 1) := by decide
