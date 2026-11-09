/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Run

/-!
# Input-tape lookups

Lemmas for reading `Turing.inputAt`. Position `0` is the left end cell and position `q + 1` holds
`x[q]`, so the lookup is blank exactly at `0` and beyond `x.length`.

## Main results

* `Turing.inputAt_zero`, `Turing.inputAt_succ`: the lookup at the left end cell and at a data cell.
* `Turing.inputAt_eq_none_iff`, `Turing.inputAt_eq_some_iff`: when the lookup is blank, and which
  symbols it reads.
-/

public section

namespace Turing

variable {Symbol : Type*} (x : List Symbol)

/-- Position `0` is the blank left end cell. -/
@[simp]
theorem inputAt_zero : inputAt x 0 = none := rfl

/-- Position `q + 1` holds the `q`-th input symbol. -/
@[simp]
theorem inputAt_succ (q : ℕ) : inputAt x (q + 1) = x[q]? := rfl

/-- The input tape is blank at the left end cell and beyond the input. -/
theorem inputAt_eq_none_iff (j : ℕ) : inputAt x j = none ↔ j = 0 ∨ x.length < j := by
  cases j with
  | zero => simp
  | succ q => simp only [inputAt_succ, List.getElem?_eq_none_iff]; omega

/-- The input tape holds `s` at `j` exactly when `j = q + 1` with `x[q] = s`. -/
theorem inputAt_eq_some_iff {s : Symbol} (j : ℕ) :
    inputAt x j = some s ↔ ∃ q, j = q + 1 ∧ x[q]? = some s := by
  cases j with
  | zero => simp
  | succ q => simp

end Turing
