/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Complexity.Problems.SAT.ExactOne.DrawingPorts

/-! # Indexed collar ports

The matcher constrains only present source exits. Completion preserves those exits and fills
the unused port deterministically, even when an unused prescribed exit repeats a present one.
-/

open Cslib.Complexity.SAT.ExactOne

-- The absent third prescription does not constrain the candidate collar.
example : portsMatch 2 3 1 3 (3, 1, 0) = true :=
  (portsMatch_iff 2 3 1 3 (3, 1, 0)).mpr (by decide)

-- The same candidate is rejected when the third prescription is present.
example : portsMatch 3 3 1 3 (3, 1, 0) = false := by decide

-- The first matching collar completes the two distinct prescribed exits.
example : choosePorts 2 3 1 3 = (3, 1, 0) := by decide

-- A client recovers the present indexed port through the matcher API.
example : (choosePorts 2 3 1 3).side 1 = 1 :=
  choosePorts_matches 2 3 1 3 (by decide) 1 (by decide)
