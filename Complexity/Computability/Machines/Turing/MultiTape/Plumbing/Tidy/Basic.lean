/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

-- upstream: submitted #1111 @3441fa81
-- `ComputableTidilyInTimeAndSpace.length_le` is from crei:crei/tidy-universal @7f7c0696
-- (unsubmitted).

public import Complexity.Computability.Machines.Turing.MultiTape.Internal.KernelFacts
public import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.ExtendTapes
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Tidy.Defs

/-!
# Basic properties of tidy computations

A tidy computation is a computation, it emits at most one symbol per step, and it stays tidy when
the machine is given more work tapes.

## Main results

* `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.computableInTimeAndSpace`: a tidily
  computable function is computable, within the same bounds.
* `Turing.MultiTapeTM.ComputesTidilyInTimeAndSpace.length_output_le`: a tidy computation emits at
  most one symbol per step.
* `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.length_le`: the output of a tidily computable
  function is no longer than its time bound.
* `Turing.MultiTapeTM.ComputesTidilyInTimeAndSpace.extendTapes`: a tidy computation stays tidy with
  more work tapes.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {α β : Type*} {k : ℕ} {Symbol State : Type*}

variable {tm : MultiTapeTM k Symbol State}

/-- A tidy computation of a function is a computation of it. -/
theorem ComputesFunTidilyInTimeAndSpace.computesFunInTimeAndSpace {encIn : α ↪ List Symbol}
    {encOut : β ↪ List Symbol} {f : α → β} {t s : α → ℕ}
    (h : ComputesFunTidilyInTimeAndSpace tm encIn encOut f t s) :
    tm.ComputesFunInTimeAndSpace encIn encOut f t s :=
  fun a => (h a).computesInTimeAndSpace

/-- The output of a tidily computable function is no longer than its time bound. -/
theorem ComputableTidilyInTimeAndSpace.length_le {f : α → β} {encIn : α ↪ List Bool}
    {encOut : β ↪ List Bool} {t s : α → ℕ}
    (h : ComputableTidilyInTimeAndSpace f encIn encOut t s) (a : α) :
    (encOut (f a)).length ≤ t a :=
  let ⟨_, _, _, _, htm⟩ := h
  (htm a).length_output_le

/-- A tidily computable function is computable. -/
theorem ComputableTidilyInTimeAndSpace.computableInTimeAndSpace {f : α → β}
    {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {t s : α → ℕ}
    (h : ComputableTidilyInTimeAndSpace f encIn encOut t s) :
    ComputableInTimeAndSpace f encIn encOut t s :=
  let ⟨k, State, hfinite, tm, htm⟩ := h
  ⟨k, State, hfinite, tm, htm.computesFunInTimeAndSpace⟩

end Turing.MultiTapeTM
