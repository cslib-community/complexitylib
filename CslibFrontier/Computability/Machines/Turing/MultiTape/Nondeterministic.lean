/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: submitted #1111 @3441fa81

public import Cslib.Computability.Machines.Turing.MultiTape.Nondeterministic

/-!
# Output growth along run paths

The additions of cslib PR #1111 to
`Cslib.Computability.Machines.Turing.MultiTape.Nondeterministic`: a step emits at most one symbol,
so a run path emits at most one symbol per step.

## Main results

* `Turing.MultiTapeNTM.RunPath.length_output_last_le`: a run path emits at most one symbol per
  step.
-/

@[expose] public section

namespace Turing

variable {k : ℕ} {State Symbol : Type*} {input : List Symbol}

namespace MultiTapeNTM

variable {ntm : MultiTapeNTM k Symbol State}

namespace RunPath

/-- A step emits at most one symbol. -/
lemma length_output_le_of_step {c c' : Cfg k Symbol State input} (h : ntm.Step c c') :
    c'.output.length ≤ c.output.length + 1 := by
  grind [Step, Action.apply_output, Option.length_toList_le]

/-- A run path emits at most one symbol per step. -/
lemma length_output_last_le (p : ntm.RunPath input) :
    p.last.output.length ≤ p.head.output.length + p.time := by
  induction p using RelSeries.inductionOn' with
  | singleton c => simp [time]
  | snoc p c hc ih =>
    have := length_output_le_of_step hc
    simp only [time, RelSeries.last_snoc, RelSeries.head_snoc, RelSeries.snoc_length] at ih ⊢
    lia

end RunPath

end MultiTapeNTM

end Turing
