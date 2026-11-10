/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.LogSpace
import CslibFrontier.Computability.Complexity.Classes.Space.Nondeterministic.DeterministicTime
import CslibFrontier.Computability.Complexity.Classes.Time.TwoPow

/-!
# Nondeterministic logarithmic space is within polynomial time

A nondeterministic machine within space `s` is decided deterministically within time
`2 ^ O(log₂ n + s)` by breadth-first search through its reachable views
(`Turing.MultiTapeNTM.RecognizesInSpace.mem_DTIME`). Within logarithmic space this time is
polynomial (`Cslib.Complexity.DTIME_two_pow_mul_log2_succ_subset`). So `NL ⊆ P`
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

public section

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool}

/-- **Logspace recognizers are within polynomial time**: a problem recognized by a
nondeterministic machine within logarithmic space, whose branches need not halt, is in `P`, by
breadth-first search through the polynomially many reachable views. -/
theorem mem_P_of_recognizesInSpace {k : ℕ} {State : Type} [Finite State]
    {ntm : MultiTapeNTM k Bool State} {A : Set α} {c : ℕ}
    (h : ntm.RecognizesInSpace enc A fun a => c * (Nat.log2 (enc a).length + 1)) : A ∈ P enc := by
  obtain ⟨d, hd⟩ := h.mem_DTIME (s := fun n => c * (Nat.log2 n + 1))
  refine mem_P_iff_exists_mem_DTIME.mpr ⟨_, DTIME_two_pow_mul_log2_succ_subset (d * (c + 1))
    (DTIME_mono (fun n => le_of_eq ?_) hd)⟩
  ring_nf

/-- **Nondeterministic logarithmic space is within polynomial time**: breadth-first search
through the polynomially many reachable views decides acceptance. -/
theorem NL_subset_P : NL enc ⊆ P enc := by
  rintro A ⟨k, State, _, ntm, c, h⟩
  exact mem_P_of_recognizesInSpace h.recognizesInSpace

end Cslib.Complexity
