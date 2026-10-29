/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.LogSpace
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Reachability

/-!
# Nondeterministic logarithmic space is within polynomial time

A nondeterministic machine within logarithmic space has polynomially many reachable views: a view
other than its input is described by a code of length `O(log n)`
(`Turing.MultiTapeNTM.length_coreCode_le`). It accepts exactly when a halted view with output
`[true]` is reachable from its initial view, which breadth-first search decides in polynomial time
(`Turing.MultiTapeNTM.exists_computableInPolyTime_searchAccepts`). So `NL ⊆ P`
[Sipser, Section 8.5][Sipser2013], and with `Cslib.Complexity.L_subset_NL` the chain
`L ⊆ NL ⊆ P`.

## Main results

* `Cslib.Complexity.mem_P_of_recognizesInSpace`: logspace recognizers, whose branches need not
  halt, are within polynomial time.
* `Cslib.Complexity.NL_subset_P`: nondeterministic logarithmic space is within polynomial time.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Section 8.5][Sipser2013]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 4.1][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool}

/-- **Logspace recognizers are within polynomial time**: a problem recognized by a
nondeterministic machine within logarithmic space, whose branches need not halt, is in `P`, by
breadth-first search through the polynomially many reachable views. -/
theorem mem_P_of_recognizesInSpace {k : ℕ} {State : Type} [Finite State]
    {ntm : MultiTapeNTM k Bool State} {A : Set α} {c : ℕ}
    (h : ntm.RecognizesInSpace enc A fun a => c * (Nat.log2 (enc a).length + 1)) : A ∈ P enc := by
  obtain ⟨rounds, hrounds, hpoly⟩ :=
    ntm.exists_computableInPolyTime_searchAccepts (enc := enc) fun a => (h a).1
  exact ⟨_, hpoly, fun a =>
    (h a).2.trans (MultiTapeNTM.searchAccepts_iff (h a).1 (hrounds a)).symm⟩

/-- **Nondeterministic logarithmic space is within polynomial time**: breadth-first search
through the polynomially many reachable views decides acceptance. -/
theorem NL_subset_P : NL enc ⊆ P enc := by
  rintro A ⟨k, State, _, ntm, c, h⟩
  exact mem_P_of_recognizesInSpace h.recognizesInSpace

end Cslib.Complexity
