/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Data/Set/Finite/Lattice.lean`, next to
-- `iInf_iSup_of_antitone`)

public import CslibFrontier.Init
public import Mathlib.Data.Set.Finite.Lattice

/-!
# Swapping `∀` and `∃` over a finite type

If `p i j` gets harder as `j` grows and `i` ranges over a finite type, then a witness `i` for each
`j` gives one witness for all `j` (`Finite.forall_exists_iff_exists_forall_of_antitone`). This is
Mathlib's `iInf_iSup_of_antitone` in the frame `Prop`, stated with quantifiers. Finite games use it:
a winning answer from a finite set for each number of rounds gives one answer that wins every
finite game.

## Main results

* `Finite.forall_exists_iff_exists_forall_of_antitone`: `(∀ j, ∃ i, p i j) ↔ ∃ i, ∀ j, p i j` for
  a finite type of `i`, a directed type of `j`, and `p i` antitone in `j`.
-/

public section

namespace Finite

/-- Over a finite type of witnesses, a witness for each `j` of a condition that gets harder as `j`
grows gives one witness for all `j`. -/
theorem forall_exists_iff_exists_forall_of_antitone {ι ι' : Type*} [Finite ι] [Preorder ι']
    [Nonempty ι'] [IsDirectedOrder ι'] {p : ι → ι' → Prop} (hp : ∀ i, Antitone (p i)) :
    (∀ j, ∃ i, p i j) ↔ ∃ i, ∀ j, p i j := by
  simpa only [iSup_Prop_eq, iInf_Prop_eq] using (iInf_iSup_of_antitone hp).to_iff

end Finite
