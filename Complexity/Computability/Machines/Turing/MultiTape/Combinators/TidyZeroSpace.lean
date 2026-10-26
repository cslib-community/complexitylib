/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

-- upstream: submitted #1138 @b1635b2e
-- The section on the identity (`tidyCopy`) is from crei:crei/tidy-universal @7f7c0696
-- (unsubmitted).

public import Complexity.Computability.Machines.Turing.MultiTape.Internal.KernelZeroSpace
public import Mathlib.Basic.Finite.Sum
public import Complexity.Computability.Machines.Turing.MultiTape.Combinators.Id
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.RewindInput
public import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.Sequential
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Tidy.Defs

/-!
# Tidiness is free at zero space

A machine that runs in zero space has no work tapes
(`Turing.MultiTapeTM.ComputableInTimeAndSpace.exists_no_work_tapes`), so the only part of its
final configuration that can differ from the start is the input head. Following it with
`Turing.MultiTapeTM.rewindInput` moves that head back, which makes the computation tidy in the
sense of `Turing.MultiTapeTM.ComputesTidilyInTimeAndSpace`.

## Main definitions

* `Turing.MultiTapeTM.tidyCopy`: the identity, as a tidy machine without work tapes.

## Main results

* `Turing.MultiTapeTM.ComputableInTimeAndSpace.computableTidilyInTimeAndSpace`: a function
  computable in time `t` and zero space is computable tidily in time `2 * t + 2` and zero space.
* `Turing.MultiTapeTM.computableTidilyInTimeAndSpace_id`: the identity is tidily computable in
  linear time and zero space.
-/

namespace Turing.MultiTapeTM

/-- A function computable in time `t` and zero space is computable tidily in time `2 * t + 2` and
zero space: the machine has no work tapes, so it suffices to rewind the input head. -/
public theorem ComputableInTimeAndSpace.computableTidilyInTimeAndSpace {α β : Type*}
    {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {f : α → β} {t : α → ℕ}
    (h : ComputableInTimeAndSpace f encIn encOut t (fun _ => 0)) :
    ComputableTidilyInTimeAndSpace f encIn encOut (fun a => 2 * t a + 2) (fun _ => 0) := by
  rcases isEmpty_or_nonempty α with _ | _
  · exact ⟨0, Unit, inferInstance, nop 0 Bool, isEmptyElim⟩
  · obtain ⟨State, hfin, tm, htm⟩ := h.exists_no_work_tapes
    exact ⟨0, State ⊕ RewindState, inferInstance, tm.seq (rewindInput Bool),
      fun a => (htm a).computesTidily_seq_rewindInput⟩

/-- The identity is tidily computable in time linear in the length of the input and zero space. -/
public theorem computableTidilyInTimeAndSpace_id {α : Type*} {enc : α ↪ List Bool} :
    ComputableTidilyInTimeAndSpace (id : α → α) enc enc
      (fun a => 2 * (enc a).length + 4) (fun _ => 0) :=
  ⟨0, _, inferInstance, tidyCopy Bool, fun a => computesTidily_tidyCopy (enc a)⟩

end Turing.MultiTapeTM
