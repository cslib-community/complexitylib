/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Logic.Function.Iterate

/-!
# Streaming a column of a ternary block schedule

A fixed tape count determines the constant radix of one schedule row. The reader discards one
row at each iteration and increments a binary counter when its selected column has the requested
digit. Runtime interval indices control iteration; no list of earlier indices or power with a
runtime exponent is allocated.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.ScheduleRead

/-- Remaining schedule rows and the number of matching digits already encountered. -/
abbrev State := ℕ × ℕ

/-- Consume one schedule row, counting a selected column's digit. The parameters `k`, `c` and
`δ` are fixed for a reader; only the suffix and counter are runtime state. -/
@[expose] def step (k c δ : ℕ) : State → State := fun (suffix, count) =>
  (suffix / 3 ^ (k + 1), count + if suffix / 3 ^ c % 3 = δ then 1 else 0)

/-- Count the selected digit in the first `i` rows of the actual binary schedule number. -/
@[expose] def read (k c δ : ℕ) (a : ℕ × ℕ) : ℕ :=
  ((step k c δ)^[a.2] (a.1, 0)).2

end Turing.MultiTapePTM.BlockComputation.ScheduleRead
