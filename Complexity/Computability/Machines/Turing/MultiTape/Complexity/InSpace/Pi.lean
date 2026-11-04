/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Plain
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Pi
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Pi
import Mathlib.Tactic.Linarith

/-!
# Fixed finite families in linear native space

A fixed finite family whose entries are each computed in linear encoded-input space can be
assembled within the same asymptotic space bound. The native tuple constructor retains the
input and sums component bounds; the fixed number of components is absorbed into its constant.
Neither the entries nor their encodings need to be finite or uniformly bounded.

## Main results

* `Turing.MultiTapeTM.ComputableInSpace.pi_linear`: assemble a fixed finite family in linear
  encoded-input space.
-/

public section

namespace Turing.MultiTapeTM.ComputableInSpace

/-- Assemble a fixed finite family from native linear-space component certificates.
The hidden constant may depend on the fixed index type, never on runtime values. -/
theorem pi_linear {α Index Value : Type} [Fintype Index]
    {input : α ↪ List Bool} {enc : Value ↪ List Bool} {values : α → Index → Value}
    (hvalues : ∀ i, ComputableInSpace (fun a => values a i) input enc
      (fun a => (input a).length)) :
    ComputableInSpace values input (encPi enc) (fun a => (input a).length) := by
  classical
  choose T hT using fun i => (hvalues i).exists_inO
  refine (of_inO (ComputableInO.pi hT)).weaken ?_
  exact ⟨Fintype.card Index + 1, fun a => by simp; nlinarith⟩

end Turing.MultiTapeTM.ComputableInSpace
