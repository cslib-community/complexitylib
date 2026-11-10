/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (addition to `Plumbing/Tidy/Defs.lean`)

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.Tidy.Defs
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Run

/-!
# Runs of tidy computations

A tidy computation (`Turing.MultiTapeTM.ComputesTidilyInTimeAndSpace`) is, in particular, a run from
the initial configuration that has halted after the given number of steps with the given output.

## Main results

* `Turing.MultiTapeTM.ComputesTidilyInTimeAndSpace.runFrom_initCfg_eq`.
* `Turing.MultiTapeTM.ComputesTidilyInTimeAndSpace.runFrom_initCfg`.
-/

public section

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State : Type*} {tm : MultiTapeTM k Symbol State}

/-- A tidy computation restores all work tapes and heads within its stated time bound. -/
theorem ComputesTidilyInTimeAndSpace.runFrom_initCfg_eq {input output : List Symbol} {t s : ℕ}
    (h : tm.ComputesTidilyInTimeAndSpace input output t s) :
    tm.runFrom (tm.initCfg input) t = wordsCfg input none (fun _ => []) output :=
  initCfg_eq_wordsCfg input ▸ (computesTidily_iff_runFrom.mp h).1

/-- A tidy computation halts after the given number of steps from the initial configuration, with
the given output. -/
theorem ComputesTidilyInTimeAndSpace.runFrom_initCfg {input output : List Symbol} {t s : ℕ}
    (h : tm.ComputesTidilyInTimeAndSpace input output t s) :
    (tm.runFrom (tm.initCfg input) t).Halted ∧
      (tm.runFrom (tm.initCfg input) t).output = output := by
  rw [h.runFrom_initCfg_eq]
  exact ⟨rfl, rfl⟩

end Turing.MultiTapeTM
