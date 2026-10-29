/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (addition to `Plumbing/Tidy/Defs.lean`; `computesTidily_iff` as stated in
-- crei:crei/tidy-universal @7f7c0696, before the run paths of cslib #1117)

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Tidy.Defs
public import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.TransformsTapes

/-!
# Tidy computations as runs

A tidy computation (`Turing.MultiTapeTM.ComputesTidilyInTimeAndSpace`) is the run of exactly the
given number of steps from the start with blank work tapes to the halted configuration with blank
work tapes that has emitted the output, together with the space bound. This is
`Turing.MultiTapeTM.computesTidily_iff` as stated in Christian Reitwiessner's branch
`crei/tidy-universal`, from which the vendored modules use it.

## Main results

* `Turing.MultiTapeTM.computesTidily_iff_runFrom`: a tidy computation, read on runs.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State : Type*} {tm : MultiTapeTM k Symbol State} {t s : ℕ}

/-- A tidy computation is a single run between `Turing.wordsCfg` configurations with
blank work tapes, which emits the output, together with the space bound. -/
theorem computesTidily_iff_runFrom {input output : List Symbol} :
    tm.ComputesTidilyInTimeAndSpace input output t s ↔
      tm.runFrom (wordsCfg input (some tm.q₀) (fun _ => []) []) t =
          wordsCfg input none (fun _ => []) output ∧
        (MultiTapeNTM.RunPath.ofDeterministic tm (wordsCfg input (some tm.q₀) (fun _ => []) [])
          t).space ≤ s := by
  rw [computesTidily_iff, ← exists_runPath_iff_runFrom rfl]

end Turing.MultiTapeTM
