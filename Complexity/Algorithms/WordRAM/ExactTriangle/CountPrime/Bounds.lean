/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.CountPrime.Setup
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Strassen.State

/-!
# Original-parameter native modular-counter budgets

These numerical expressions account for actual native arithmetic, memory and recursion.
They contain no supplied execution, multiplication, count or running-time certificate.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime

/-- The original entry/modulus bounds and the proved recursive signed magnitude envelope. -/
@[expose] def magnitudeBudget (p k A : ℕ) : ℕ := A + p + 2 * (p + 4) * 16 ^ k + 1

/-- The workspace ends after the actual root/descendant frame stack. -/
@[expose] def memoryEnd (n p k scratch : ℕ) : ℕ :=
  scratch + 3 * (n * n) + 2 ^ k + 4 * (4 ^ k * p) + 7 * (k + 1)

/-- Three real residue calls, table/two matrix writers, actual Strassen and the count scan. -/
@[expose] def readyCost (n p k : ℕ) : ℕ :=
  Strassen.traceBudget p k + (14 * p + 48) * 4 ^ k + 11 * (2 ^ k - 1) +
    91 * (n * n) + 4 * k + 81

/-- Complete caller execution, including its actual logarithm and layout setup, before halt. -/
@[expose] def cost (n p : ℕ) : ℕ := readyCost n p (Nat.clog 2 n) + 9 * Nat.clog 2 n + 31

end Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime
