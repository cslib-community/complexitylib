/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.Layered.Padding.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
Concrete clients of layered padding, including empty schedules, zero-width rows, repeated
outputs and a schedule already over budget. Malformed references exercise preservation of the
specified fallback semantics and total runtime; they do not assert well-formedness.
-/

namespace ComplexityTests.CircuitLayerPadding

open Cslib.Circuits.Boolean.Layered Turing.MultiTapeTM

private def shared : List (List Node) :=
  [[.nand 0 1], [.copy 0, .nand 0 0, .copy 0]]

-- Padding preserves sharing and repeated output positions while reaching the target count.
example : WellFormed 2 shared := by simp [shared, WellFormed, Node.Valid]
example : WellFormed 2 (padTo 2 5 shared) :=
  (show WellFormed 2 shared by simp [shared, WellFormed, Node.Valid]).padTo 5
example : (padTo 2 5 shared).length = 5 ∧ outputWidth 2 (padTo 2 5 shared) = 3 := by
  decide +kernel
example : ∀ a b : Bool, eval [a, b] (padTo 2 5 shared) =
    [!(a && b), a && b, !(a && b)] := by decide +kernel

-- With no original layers, padding carries the original row and free output permutation.
example : select (eval [false, true] (padTo 2 3 [])) [1, 0, 1] =
    [true, false, true] := by decide +kernel
example (inputs : List Bool) (target : ℕ) :
    eval inputs (padTo inputs.length target []) = inputs := by simp

-- Constants create a nonempty row from no inputs. Empty rows also remain valid through copies.
example : WellFormed 0 (padTo 0 4 [[.const true, .const false]]) :=
  (show WellFormed 0 [[.const true, .const false]] by simp [WellFormed, Node.Valid]).padTo 4
example : eval [] (padTo 0 4 [[.const true, .const false]]) = [true, false] := by
  decide +kernel
example : WellFormed 0 (padTo 0 3 []) ∧ (padTo 0 3 []).length = 3 ∧
    eval [] (padTo 0 3 []) = [] := by
  exact ⟨(wellFormed_nil 0).padTo 3, by decide +kernel⟩
example : outputWidth 1 (padTo 1 4 [[]]) = 0 ∧
    eval [true] (padTo 1 4 [[]]) = [] := by decide +kernel

-- Padding does not truncate a schedule whose length already exceeds the requested budget.
example : padTo 2 1 shared = shared := by decide +kernel
example : padTo 2 0 shared = shared := by decide +kernel

-- Huge invalid binary references retain their existing false fallback through padding.
example : eval [] (padTo 0 3 [[.copy (2 ^ 100)]]) = [false] := by decide +kernel

-- The certificate is uniform in both unary parameters and the complete raw schedule.
example : ComputableInPolyTime
    (fun p : ℕ × ℕ × List (List Node) => padTo p.1 p.2.1 p.2.2)
    (encPair encUnary (encPair encUnary (encList (encList encNode))))
    (encList (encList encNode)) := by fun_prop

/--
info: 'Cslib.Circuits.Boolean.Layered.eval_padTo' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms eval_padTo

/--
info: 'Cslib.Circuits.Boolean.Layered.WellFormed.padTo' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms WellFormed.padTo

end ComplexityTests.CircuitLayerPadding
