/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.PreprocessingInput
public import Complexity.Algorithms.WordRAM.ThreeSum.Decision.Admissible
public import Complexity.Algorithms.WordRAM.ThreeSum.Host.ExecuteAt

/-!
# Shared quantitative budgets for ordinary native 3SUM

The finite reduction's common packed length and instance count determine the charged host
budget. These definitions are independent of whether the native controller stores a complete
catalogue or consumes each node during traversal. They retain their existing declaration names
and values, extracted from `Decision.Execute` for both concrete clients.

## Main definitions

* `instanceLength`, `instanceBound`: finite reduction length and count bound.
* `cost`: complete host budget with the actual packed length and concrete callee time.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.Decision

open Cslib.WordRAM

/-- The exact common packed length already produced by native preprocessing. -/
def instanceLength (κ n : ℕ) : ℕ :=
  8 * Cslib.Algorithms.ThreeSum.ChanHe.mPar n (2 * (n + 2) ^ κ) ^ 2

/-- The existing finite count bound, with the same original-input magnitude. -/
def instanceBound (κ n : ℕ) : ℕ :=
  (2 * Cslib.Algorithms.ThreeSum.labelBits (2 * (n + 2) ^ κ) ^ 2 + 2) *
    (2 * Nat.log 2 n + 2) ^ 5

/-- Every preprocessing, pointer, matrix, callee and control instruction, including halt.
The callee is charged at the packed side and coarse polynomial filler actually passed to it. -/
def cost {r : ℕ} (κ : ℕ) (c : Host.Callee r) (n : ℕ) : ℕ :=
  ChanHe.Preprocessing.cost κ n + 4 * envelopeExponent κ + 32 +
    instanceBound κ n * (Host.callerTime (instanceLength κ n)
      (c.time (Host.sideLength (instanceLength κ n)) (2 * (n + 2) ^ envelopeExponent κ + 1)) + 12)

end Cslib.Algorithms.WordRAM.ThreeSum.Decision
