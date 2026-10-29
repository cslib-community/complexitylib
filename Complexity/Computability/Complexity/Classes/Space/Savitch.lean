/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Space
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Space.Savitch

/-!
# Savitch's theorem: `NPSPACE = PSPACE`

Every problem decided by a nondeterministic machine within polynomial space is decided by a
deterministic machine within polynomial space: Savitch's decider
(`Turing.MultiTapeNTM.savitchDecide`), which runs his midpoint recursion with an explicit stack on
the codes of the finite views of the nondeterministic machine. With the converse inclusion,
`NPSPACE = PSPACE` [Sipser, Corollary 8.6][Sipser2013]. Both classes are machine-defined: the
deterministic class by plain total decision within polynomial space, the nondeterministic class by
accepting computation paths, with every computation path within the space bound and every branch
halting. The simulation uses only the space bound and acceptance, so it applies to recognizers,
whose branches may run forever (`Cslib.Complexity.mem_PSPACE_of_recognizesInSpace`).

## Main results

* `Cslib.Complexity.mem_PSPACE_of_recognizesInSpace`: Savitch's theorem for recognizers, whose
  branches need not halt.
* `Cslib.Complexity.NPSPACE_subset_PSPACE`: Savitch's theorem for polynomial space.
* `Cslib.Complexity.NPSPACE_eq_PSPACE`: the two classes are equal.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Corollary 8.6][Sipser2013]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 4.2][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool}

/-- **Savitch's theorem for recognizers**: a problem recognized by a nondeterministic machine
within polynomial space, whose branches need not halt, is in `PSPACE`. -/
theorem mem_PSPACE_of_recognizesInSpace {k : ℕ} {State : Type} [Finite State]
    {ntm : MultiTapeNTM k Bool State} {A : Set α} {s : α → ℕ}
    (hs : PolyBounded (fun a => (enc a).length) s) (hA : ntm.RecognizesInSpace enc A s) :
    A ∈ PSPACE enc := by
  obtain ⟨c, d, hcd⟩ := hs.exists_le
  obtain ⟨t, s', hs', hdecide⟩ := ntm.exists_polyBounded_space_savitchDecide enc c d
  exact ⟨fun a => ntm.savitchDecide c d (enc a), ⟨t, s', hs', hdecide⟩,
    fun a => (hA a).2.trans (MultiTapeNTM.savitchDecide_eq_true_iff (hA a).1 (hcd a)).symm⟩

/-- **Savitch's theorem for polynomial space**: every problem decided by a nondeterministic
machine within polynomial space is decided by a deterministic machine within polynomial space,
namely Savitch's decider [Sipser, Corollary 8.6][Sipser2013]. -/
theorem NPSPACE_subset_PSPACE : NPSPACE enc ⊆ PSPACE enc := by
  rintro A ⟨k, State, hfinite, ntm, s, hs, hA⟩
  exact mem_PSPACE_of_recognizesInSpace hs hA.recognizesInSpace

/-- **`NPSPACE = PSPACE`** [Sipser, Corollary 8.6][Sipser2013]. -/
theorem NPSPACE_eq_PSPACE : NPSPACE enc = PSPACE enc :=
  Set.Subset.antisymm NPSPACE_subset_PSPACE PSPACE_subset_NPSPACE

end Cslib.Complexity
