/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)
-- vendored: these lemmas sit in `Universal/Compose.lean` on that branch; they are kept apart here
-- so that clients of the halting step need not import the universal machine

public import Complexity.Computability.Machines.Turing.MultiTape.Deterministic

/-!
# The first halt and the computed output

A time bound gives a step at which the run first halts, and the output at that step is the
computed output.

## Main results

* `Turing.MultiTapeTM.exists_haltsAt_of_runsInTime`: the first halt is no later than the time
  bound.
* `Turing.MultiTapeTM.output_haltsAt`: the output at the first halt is the computed output.
-/

namespace Turing.MultiTapeTM

section Halting

variable {k : ℕ} {State Symbol : Type*} {tm : MultiTapeTM k Symbol State}

/-- The output at the first halt is the computed output. -/
public lemma output_haltsAt {input output : List Symbol} {h : ℕ}
    (hc : tm.Computes input output) (hh : tm.HaltsAt (tm.initCfg input) h) :
    (tm.runFrom (tm.initCfg input) h).output = output := by
  obtain ⟨u, hu, rfl⟩ := hc
  rw [hh.runFrom_eq (hh.le_of_halted hu)]

/-- The first halt is no later than the time bound. -/
public lemma exists_haltsAt_of_runsInTime {input : List Symbol} {t : ℕ}
    (ht : tm.RunsInTime input t) : ∃ h ≤ t, tm.HaltsAt (tm.initCfg input) h :=
  exists_haltsAt (runsInTime_iff_halted.mp ht)

end Halting

end Turing.MultiTapeTM
