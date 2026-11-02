/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.PP
public import Complexity.Computability.Complexity.Classes.Promise.Basic

/-!
# Strict-majority completions of bounded-error promise problems

A verifier for `PromiseBPP` gives a language in `PP` separating its yes- and no-instances:
accept exactly when strictly more than half of its random strings are accepted. This is a direct
consequence of the existing bounded-error and strict-majority definitions. Ties are rejected;
outside the promise, no bounded-error margin is asserted for the completion.

## Main results

* `Cslib.Complexity.PromiseBPP_subset_promiseClass_PP`: every bounded-error promise problem
  has a strict-majority completion in `PP`.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-- Every problem in `PromiseBPP` has a completion in `PP`, using the same seeded verifier.
The completion accepts by strict majority, including on inputs outside the promise. -/
theorem PromiseBPP_subset_promiseClass_PP {α : Type} {enc : α ↪ List Bool} :
    PromiseBPP enc ⊆ promiseClass (PP enc) := by
  rintro Q ⟨p, V, hV, hQ⟩
  let L : Set α := {a | 2 ^ p.eval (enc a).length <
    2 * acceptCount V a (p.eval (enc a).length)}
  have hsolve := hQ.solvedBy_majority
  refine ⟨L, ⟨p, V, hV, fun _ => Iff.rfl⟩, ?_, ?_⟩
  · intro a ha
    exact of_decide_eq_true (hsolve.1 a ha)
  · refine Set.disjoint_right.mpr fun a ha hL => ?_
    have hno := hsolve.2 a ha
    simp only [decide_eq_false_iff_not] at hno
    exact hno hL

end Cslib.Complexity
