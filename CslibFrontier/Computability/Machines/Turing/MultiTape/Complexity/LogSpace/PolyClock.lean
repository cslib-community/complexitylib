/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init

/-!
# The polynomial clock of logarithmic-space machines

A machine that stays within space `c * (log₂ n + 1)` has polynomially many reachable views on an
input of length `n` (`Turing.MultiTapeNTM.two_pow_coreLengthBound_log_le`). So if every branch
halts, every branch halts within `2 * (2 * (n + 1)) ^ d` steps, for an exponent `d` depending only
on the machine and `c` (`Turing.MultiTapeNTM.exists_runsInTime_polynomial_of_runsInSpace_log`).
This file names that bound, so that the halting-time theorem, the clocked configuration graphs of
fair-coin machines and the randomized log-space classes state the same clock the same way.

## Main definitions

* `Turing.polyClock`: the polynomial clock `2 * (2 * (n + 1)) ^ d`.
-/

public section

namespace Turing

/-- **The polynomial clock of logarithmic-space machines**: `2 * (2 * (n + 1)) ^ d` steps on an
input of length `n`. -/
@[expose] def polyClock (d n : ℕ) : ℕ := 2 * (2 * (n + 1)) ^ d

end Turing
