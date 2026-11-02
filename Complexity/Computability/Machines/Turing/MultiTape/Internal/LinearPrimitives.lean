/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Internal.FrameMachines
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.KernelTransducer
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.NormalForm
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.DegreeComposition
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Degree.Primitives
import Cslib.Computability.Machines.Turing.MultiTape.Combinators.AlmostConstant
import Cslib.Computability.Machines.Turing.MultiTape.Combinators.Id
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Degree-one certificates from finite transducers

The shared streaming machines give linear time and zero workspace. The actual runtime bounds
encoded output growth, so these are degree-1/1 certificates. Copy, constant and composition rules
come from the existing degree calculus.
-/

@[expose] public section

namespace Turing.MultiTapeTM.ComputableInDegree


variable {α β γ : Type*} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool}
  {encOut : γ ↪ List Bool}

/-- A finite transducer gives a common linear bound from its actual clock and zero workspace. -/
theorem of_transducer {Q : Type} [Finite Q] (τ : Transducer Bool Q) {f : α → β}
    (h : ∀ a, encMid (f a) = τ.run τ.q₀ (encIn a)) :
    ComputableInDegree f encIn encMid 1 1 := by
  apply of_bounds (t := fun a => 2 * (encIn a).length + 3) (s := fun _ => 0)
    ⟨3, fun _ => by simp only [pow_one]; omega⟩ (DegreeBounded.const 0)
  exact ⟨0, _, inferInstance, τ.toTM, fun a => by
    rw [h a]
    exact τ.computesInTimeAndSpace_toTM (encIn a)⟩

/-- Frame the encoded input using the shared streaming machine. -/
theorem of_frame {f : α → β} (h : ∀ a, encMid (f a) = frame (encIn a)) :
    ComputableInDegree f encIn encMid 1 1 :=
  of_transducer Encodings.frameT fun a => (h a).trans (Encodings.frameT_run _).symm

/-- Read the first framed word, including the prescribed behavior on incomplete frames. -/
theorem of_unframe {f : α → β} (h : ∀ a, encMid (f a) = unframe (encIn a)) :
    ComputableInDegree f encIn encMid 1 1 :=
  of_transducer (Internal.FrameMachines.readFrameT true) fun a =>
    (h a).trans (Internal.FrameMachines.readFrameT_run_true _).symm

/-- Drop the first framed word using the same shared parser. -/
theorem of_dropFrame {f : α → β} (h : ∀ a, encMid (f a) = dropFrame (encIn a)) :
    ComputableInDegree f encIn encMid 1 1 :=
  of_transducer (Internal.FrameMachines.readFrameT false) fun a =>
    (h a).trans (Internal.FrameMachines.readFrameT_run_false _).symm

end Turing.MultiTapeTM.ComputableInDegree
