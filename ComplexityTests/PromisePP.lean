/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.Promise.PP
import ComplexityTests.PromiseProbabilistic

/-! A strict-majority completion of a genuinely partial promise problem.

The reused verifier answers the first input bit on the promised singleton words, but answers a
fair coin on the empty word. Majority still solves the promise, with ties rejecting on `[]`.
-/

namespace ComplexityTests.PromisePP

open Cslib.Complexity Turing.MultiTapeTM ComplexityTests.PromiseProbabilistic

/-- The fixture's computed fallback can be expressed through an emptiness test and fixed heads. -/
theorem partialVerifier_polyTime :
    ComputableInPolyTime partialVerifier (encPair encBits encBits) encBool := by
  have heq : partialVerifier = fun p : List Bool × List Bool =>
      if p.1.isEmpty then p.2.headD false else p.1.headD false := by
    funext ⟨x, r⟩
    cases x <;> rfl
  rw [heq]
  fun_prop

/-- Majority solves the promised yes- and no-instances even though the empty word has no gap. -/
example : partialSingletonBit.SolvedBy (fun a => decide
    (2 ^ 1 < 2 * acceptCount partialVerifier a 1)) := by
  simpa only [Polynomial.eval_one] using
    solvesWithBoundedError_partialSingletonBit.solvedBy_majority

/-- The unpromised empty word is an exact tie and is rejected by the strict-majority rule. -/
example : ([] : List Bool) ∉ partialSingletonBit.promise ∧
    acceptCount partialVerifier [] 1 = 1 ∧
    decide (2 ^ 1 < 2 * acceptCount partialVerifier [] 1) = false := by
  constructor
  · simp [partialSingletonBit, PromiseProblem.promise]
  · decide

/-- The class-level inclusion supplies a `PP` language containing the yes-word and excluding the
no-word, with no requirement on how that language answers other words. -/
example : ∃ L ∈ PP encBits, [true] ∈ L ∧ [false] ∉ L := by
  have hQ : partialSingletonBit ∈ PromiseBPP encBits :=
    ⟨1, partialVerifier, partialVerifier_polyTime,
      solvesWithBoundedError_partialSingletonBit⟩
  obtain ⟨L, hL, hyes, hno⟩ := PromiseBPP_subset_promiseClass_PP hQ
  refine ⟨L, hL, hyes rfl, ?_⟩
  intro hm
  exact Set.disjoint_left.mp hno hm rfl

end ComplexityTests.PromisePP
