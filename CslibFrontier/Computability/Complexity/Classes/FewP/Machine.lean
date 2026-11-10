/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.FewP
public import CslibFrontier.Computability.Complexity.Classes.SharpP.Characterization

/-!
# The native machine characterization of FewP

The parsimonious #P characterization preserves the polynomial accepting-count bound in the
verifier definition of `FewP` [AllenderRubinstein1988],
[BorchertHemaspaandraRothe2000, Section 1]. The bound counts accepting transition occurrence
traces; repeated equal successors remain distinct. Rejecting and total branch counts are not
required to satisfy this ambiguity bound.

The tape count, finite control, machine, all-branches clock and ambiguity polynomial are fixed
before the input. Both polynomials are evaluated at encoded input length, and the ambiguity
polynomial may be zero. The halting contract covers the encoding image, or every binary input
when specialized to `encBits`.

## Main results

* `Cslib.Complexity.mem_FewP_iff_exists_machine`: FewP is native polynomial time with
  polynomially many accepting occurrence traces per encoded input.

## References

* [E. Allender, R. Rubinstein, *P-printable sets*][AllenderRubinstein1988]
* [B. Borchert, L. Hemaspaandra, J. Rothe,
  *Restrictive acceptance suffices for equivalence problems*][BorchertHemaspaandraRothe2000]

The actual guess-and-verify construction and its formalization credits are in
`Classes.SharpP.Characterization`; this module transports the ambiguity bound through its
exact accepting-count equality.
-/

@[expose] public section

open Turing

namespace Cslib.Complexity

variable {α : Type} {enc : α ↪ List Bool} {A : Set α}

/-- FewP is exactly native polynomial time with a separate polynomial accepting-branch bound.
All parameters precede the input. The clock bounds every branch, while the ambiguity polynomial
bounds only accepting branches, and both are evaluated at encoded input length. -/
theorem mem_FewP_iff_exists_machine :
    A ∈ FewP enc ↔
      ∃ (k : ℕ) (State : Type) (_ : Finite State) (machine : MultiTapeCTM k Bool State)
        (clock ambiguity : Polynomial ℕ), machine.Nonblocking ∧ ∀ a,
          machine.HaltsWithin (clock.eval (enc a).length) (Cfg.init machine.initial (enc a)) ∧
          machine.acceptCount (clock.eval (enc a).length) (Cfg.init machine.initial (enc a)) ≤
            ambiguity.eval (enc a).length ∧
          (a ∈ A ↔ 0 < machine.acceptCount (clock.eval (enc a).length)
            (Cfg.init machine.initial (enc a))) := by
  constructor
  · rintro ⟨f, hf, ambiguity, hle, hA⟩
    obtain ⟨k, State, hfinite, machine, clock, hnon, hm⟩ :=
      mem_SharpP_iff_exists_machine.mp hf
    refine ⟨k, State, hfinite, machine, clock, ambiguity, hnon, fun a => ?_⟩
    rw [(hm a).2]
    exact ⟨(hm a).1, hle a, hA a⟩
  · rintro ⟨k, State, hfinite, machine, clock, ambiguity, _, hm⟩
    exact ⟨_, machine.acceptCount_mem_SharpP enc clock, ambiguity,
      fun a => (hm a).2.1, fun a => (hm a).2.2⟩

end Cslib.Complexity
