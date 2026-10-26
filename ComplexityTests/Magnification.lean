/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.MCSP.Magnification

/-!
# Tests for Hardness Magnification via Circuit-Min-Merge

Concrete checks for `GapMCSP.slice_yesSet_eq_true_iff`, `validCertificate`, `evalCertificate`,
`agreesOnPoint`, and yes- and no-instances of `CircuitMinMergeLanguage`.
-/

namespace Cslib.MCSP.Tests.Magnification

open Cslib.Circuits Cslib.Circuits.Boolean Cslib.Complexity Cslib.MCSP Turing.MultiTapeTM

-- The projection `x ↦ x 0` on 1 input has circuit complexity 0, so its truth table lies in
-- `GapMCSP.yesSet (fun _ => 0)` and the 2-bit slice evaluates to `true`.
example : List.ofFn (truthTable 1 (fun x : BitString 1 => x 0)) ∈ GapMCSP.yesSet (fun _ => 0) := by
  rw [GapMCSP.ofFn_mem_yesSet_iff, Equiv.symm_apply_apply, complexity_single_proj]

example : (GapMCSP.yesSet (fun _ => 0)).slice (2 ^ 1)
    (truthTable 1 (fun x : BitString 1 => x 0)) = true := by
  rw [GapMCSP.slice_yesSet_eq_true_iff, Equiv.symm_apply_apply, complexity_single_proj]

-- At size 0 on 1 input, `[false]` is the valid certificate for the projection `x ↦ x 0`.
example : validCertificate 1 0 [false] = true := by decide
example : evalCertificate 1 0 [false] [false] = false := by decide
example : evalCertificate 1 0 [false] [true] = true := by decide

-- Point agreement on 2-bit inputs.
example : agreesOnPoint 2 0 [true] [false, false] [false, false] [false, false] [true, false] =
    true := by decide

-- A concrete yes-instance of `CircuitMinMergeLanguage` at `n = 1, s = 0, p = [], j = 0`:
-- both child certificates `[false]` compute `x ↦ x 0` on `[false]` and `[true]`, and `[false]` is
-- the unique valid size-0 certificate on 1 input.
example : (((1, 0), ([], 0)), [true, false, true, false]) ∈ CircuitMinMergeLanguage := by
  refine ⟨rfl, rfl, [false], ⟨⟨rfl, by decide, fun x hx => ?_⟩, fun w' hw' hmerged => ?_⟩, rfl⟩
  · rcases List.length_eq_one_iff.1 hx with ⟨b, rfl⟩
    cases b <;> decide
  · rcases List.length_eq_one_iff.1 hw' with ⟨b, rfl⟩
    cases b <;> decide

-- A concrete no-instance of `CircuitMinMergeLanguage` at `n = 1, s = 0, p = [], j = 1`:
-- both children are valid (`ok₀ = ok₁ = true`), and the unique valid size-0 certificate on 1 input
-- is `w = [false]`, whose bit `j - 1 = 0` is `false`.
example : (((1, 0), ([], 1)), [true, false, true, false]) ∉ CircuitMinMergeLanguage := by
  rintro ⟨_, _, w, ⟨⟨hwlen, hvalid, _⟩, _⟩, hbit⟩
  rcases List.length_eq_one_iff.1 hwlen with ⟨b, rfl⟩
  cases b
  · exact Bool.false_ne_true hbit
  · exact Bool.false_ne_true hvalid

-- A concrete no-instance of `CircuitMinMergeLanguage` when a child validity bit is `false`.
example : (((1, 0), ([], 0)), [false, false, true, false]) ∉ CircuitMinMergeLanguage := by
  rintro ⟨hok₀, _⟩
  exact Bool.false_ne_true hok₀

end Cslib.MCSP.Tests.Magnification
