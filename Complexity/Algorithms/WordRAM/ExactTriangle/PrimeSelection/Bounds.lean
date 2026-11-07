/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.CountPrime.Monotone
public import Mathlib.Data.Nat.Sqrt

/-!
# Charged budgets for concrete prime selection

Each eligible prime calls the actual modular counter. Monotonicity bounds each call by the
counter at the largest possible modulus, with all six argument copies charged separately.
The loop budget additionally includes native square tests, trial division and minimum updates.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.PrimeSelection

/-- Uniform charge for an actual counter call, including its six argument copies. -/
@[expose] def countTimeBound (n D : ℕ) : ℕ := CountPrime.cost n (Nat.sqrt D) + 6

/-- Complete concrete selector pre-halt charge, including initialization and loop control. -/
@[expose] def timeBound (n D : ℕ) : ℕ :=
  (Nat.sqrt D + 1) * (countTimeBound n D + 7 * Nat.sqrt D + 20) + 10

end Cslib.Algorithms.WordRAM.ExactTriangle.PrimeSelection
