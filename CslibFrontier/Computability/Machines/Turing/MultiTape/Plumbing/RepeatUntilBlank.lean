/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)
-- vendored: `ConfinedRun.confined` is stated with the cells visited by a run path since cslib #1122

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.RepeatUntilBlank

/-!
# Confined runs

The addition of Christian Reitwiessner's branch `crei/tidy-universal` to
`Cslib.Computability.Machines.Turing.MultiTape.Plumbing.RepeatUntilBlank`: a run between two
configurations that keeps every head within a window, which loops built like
`Turing.MultiTapeTM.repeatUntilBlank` accumulate round by round. The branch also reproves
`Turing.MultiTapeTM.transformsTapes_repeatUntilBlank` through confined runs; that proof is not
copied.

## Main definitions

* `Turing.MultiTapeTM.ConfinedRun`: a run of a given length, with every head within `[-r, r]`.
-/

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

/-- `M` runs from `start` to `finish` in `steps` steps, with every head within `[-r, r]`. -/
public structure ConfinedRun (M : MultiTapeTM k Symbol State)
    (start finish : Cfg k Symbol State input) (steps r : ℕ) : Prop where
  reaches : M.runFrom start steps = finish
  confined : ∀ l,
    (MultiTapeNTM.RunPath.ofDeterministic M start steps).visitedByTapeHead l ⊆
      Finset.Icc (-(r : ℤ)) (r : ℤ)

end Turing.MultiTapeTM
