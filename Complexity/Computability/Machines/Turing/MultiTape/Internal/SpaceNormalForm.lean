/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Plain
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.NormalForm

/-!
# Normalized machine witnesses for charged space bounds

Native multi-pass simulations need machines with aligned tape origins. Normalize a plain charged
space certificate at that boundary, retaining its encoding and output charge. Time remains
existential; the space window changes by a uniform constant factor.
-/

public section

namespace Turing.MultiTapeTM.Internal.NormalForm

/-- A normalized realizing machine for a plain charged-space certificate. -/
theorem space {α β : Type*} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
    {f : α → β} {S : α → ℕ} (h : ComputableInSpace f encIn encOut S) :
    ∃ T : α → ℕ, ∃ c : ℕ,
      (∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : MultiTapeTM k Bool State),
        ∀ a, tm.ComputesTidilyInTimeAndSpace (encIn a) (encOut (f a))
          (c * (T a + 1)) (c * (S a + 1))) ∧
      ∀ a, (encOut (f a)).length ≤ c * (S a + 1) :=
  let ⟨T, hT⟩ := h.exists_inO
  let ⟨c, hc, hl⟩ := inO hT
  ⟨T, c, hc, hl⟩

end Turing.MultiTapeTM.Internal.NormalForm
