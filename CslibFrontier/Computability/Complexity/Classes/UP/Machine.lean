/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.UP
public import CslibFrontier.Computability.Complexity.Classes.SharpP.Characterization

/-!
# The native machine characterization of UP

The parsimonious #P characterization preserves the at-most-one accepting-count condition in
the verifier definition of `UP` [Papadimitriou94]. Ambiguity counts accepting transition
occurrence traces, not distinct final configurations or all branches. Rejecting branches are
unrestricted in number, and enlarging an adequate clock does not multiply halted branches.

The tape count, finite control, machine and polynomial clock are fixed before the input.
Every branch halts without getting stuck on the encoding image; `encBits` covers all binary
inputs. No decoder or halting/correctness contract outside that image is assumed.

## Main results

* `Cslib.Complexity.mem_UP_iff_exists_machine`: UP is native polynomial time with at most one
  accepting occurrence trace per encoded input.

## References

* [C. H. Papadimitriou, *Computational Complexity*][Papadimitriou94]

The actual guess-and-verify construction and its formalization credits are in
`Classes.SharpP.Characterization`; this module transports the ambiguity bound through its
exact accepting-count equality.
-/

public section

open Turing

namespace Cslib.Complexity

variable {α : Type} {enc : α ↪ List Bool} {A : Set α}

/-- UP is exactly native polynomial-time computation with at most one accepting branch.
All machine parameters precede the input; the ambiguity bound concerns accepting branches only.
The all-branches clock is in encoded input length, with no halting claim outside the encoding. -/
theorem mem_UP_iff_exists_machine :
    A ∈ UP enc ↔
      ∃ (k : ℕ) (State : Type) (_ : Finite State) (machine : MultiTapeCTM k Bool State)
        (clock : Polynomial ℕ), machine.Nonblocking ∧ ∀ a,
          machine.HaltsWithin (clock.eval (enc a).length) (Cfg.init machine.initial (enc a)) ∧
          machine.acceptCount (clock.eval (enc a).length) (Cfg.init machine.initial (enc a)) ≤ 1 ∧
          (a ∈ A ↔ machine.acceptCount (clock.eval (enc a).length)
            (Cfg.init machine.initial (enc a)) = 1) := by
  constructor
  · rintro ⟨f, hf, hle, hA⟩
    obtain ⟨k, State, hfinite, machine, clock, hnon, hm⟩ :=
      mem_SharpP_iff_exists_machine.mp hf
    refine ⟨k, State, hfinite, machine, clock, hnon, fun a => ?_⟩
    rw [(hm a).2]
    exact ⟨(hm a).1, hle a, hA a⟩
  · rintro ⟨k, State, hfinite, machine, clock, _, hm⟩
    exact ⟨_, machine.acceptCount_mem_SharpP enc clock,
      fun a => (hm a).2.1, fun a => (hm a).2.2⟩

end Cslib.Complexity
