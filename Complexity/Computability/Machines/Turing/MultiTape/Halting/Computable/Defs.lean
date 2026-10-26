/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Internal.ResourceFacts
public import Complexity.Init
public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic
import Complexity.Computability.Machines.Turing.MultiTape.Deterministic

/-!
# Total native computability

The unbounded model and its witness characterization are moved unchanged from the higher halting
calculus. This module imports only machine semantics, not a resource-calculus implementation.
-/

@[expose] public section
namespace Turing.MultiTapeTM

variable {α β : Type*} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool}

/-- `f` is computable: some machine with a binary alphabet and finitely many states computes it
with respect to the encodings `encIn` and `encOut` within some time and space bounds. -/
def IsComputable (f : α → β) (encIn : α ↪ List Bool) (encOut : β ↪ List Bool) : Prop :=
  ∃ t s : α → ℕ, ComputableInTimeAndSpace f encIn encOut t s

/-- **Computability is computability by a total machine**: some machine with a binary alphabet and
finitely many states halts on every encoded input with the encoded value. -/
theorem isComputable_iff {f : α → β} :
    IsComputable f encIn encMid ↔ ∃ (k : ℕ) (State : Type) (_ : Finite State)
      (tm : MultiTapeTM k Bool State), ∀ a, tm.Computes (encIn a) (encMid (f a)) := by
  refine ⟨fun ⟨_, _, k, State, hfin, tm, htm⟩ => ⟨k, State, hfin, tm, fun a => (htm a).1⟩,
    fun ⟨k, State, hfin, tm, htm⟩ => ?_⟩
  choose t s hts using fun a => (htm a).exists_computesInTimeAndSpace
  exact ⟨t, s, k, State, hfin, tm, hts⟩

/-- Functions computable within bounds are computable. -/
theorem ComputableInTimeAndSpace.isComputable {f : α → β} {t s : α → ℕ}
    (h : ComputableInTimeAndSpace f encIn encMid t s) : IsComputable f encIn encMid :=
  ⟨t, s, h⟩

end Turing.MultiTapeTM
