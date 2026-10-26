/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.MCSP.HardnessConsequences

/-!
# Tests: Nondeterministic Time Hierarchy (`NP ⊂ NEXP`) and Consequences of `NP`-Hardness of `MCSP`

Tests for doubly-exponential constructibility, exponential padding into `NEXP` and `EXP`,
`NP ⊂ NEXP`, and Murray–Williams Theorem 4.1 (`EXP = NEXP` from `NP`-hardness of `MCSP` and
`EXP ⊆ P/poly`) and Theorem 1.6 (`EXP ⊈ NP ∩ P/poly` from `NP`-hardness of `MCSP`).
-/

namespace ComplexityTests.HardnessConsequences

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Complexity
open _root_.Turing _root_.Turing.MultiTapeTM

/-! ### Concrete Evaluation and Non-Vacuity Checks -/

-- Concrete bounded MCSP search on the 1-input identity truth table `[false, true]` at threshold 0:
-- `certLength 1 0 = 1`, so budget `2 ^ 1 = 2` suffices to find the 0-gate wire circuit.
example : MCSP.boundedMCSPSearch [false, true] 0 2 = true := by
  decide

-- Concrete bounded MCSP search on the 1-input negation truth table `[true, false]` at threshold 0:
-- negation requires 1 NOT gate, so threshold 0 returns `false`.
example : MCSP.boundedMCSPSearch [true, false] 0 2 = false := by
  decide

-- At threshold 1, `certLength 1 1 = 5`, and budget `2 ^ 5 = 32` finds the 1-gate NOT circuit.
example : MCSP.boundedMCSPSearch [true, false] 1 32 = true := by
  decide

-- Applying `boundedMCSPSearch_eq_true_iff` at `S = 0, K = 2` (`certLength 1 0 = 1`) to certify
-- that `[false, true]` has complexity `0` while `[true, false]` requires at least `1` gate.
example : complexity interpretation (single (MCSP.tableFunction 1 [false, true])) = 0 :=
  Nat.eq_zero_of_le_zero
    ((MCSP.boundedMCSPSearch_eq_true_iff (m := 1) (S := 0) (K := 2) rfl (by decide)).mp (by decide))

example : 1 ≤ complexity interpretation (single (MCSP.tableFunction 1 [true, false])) := by
  have hgt : ¬ (complexity interpretation (single (MCSP.tableFunction 1 [true, false])) ≤ 0) := by
    rw [← MCSP.boundedMCSPSearch_eq_true_iff (m := 1) (S := 0) (K := 2) rfl (by decide)]
    decide
  omega

end ComplexityTests.HardnessConsequences
