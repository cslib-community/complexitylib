/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.SingleTape.Palindrome

/-!
# Tests for crossing sequences and the palindrome lower bound

A concrete single-tape machine with computed crossing sequences, the sum and halting edge cases,
the hard palindrome inputs, and a failing instance of `DecidesPalindromesInTime`.
-/

namespace ComplexityTests.SingleTapeCrossing

open Cslib Cslib.Turing SingleTapeTM

/-- A one-state machine that moves right over the input and halts on the first blank. -/
def rightMover : SingleTapeTM Bool where
  State := Unit
  q₀ := ()
  tr _
    | some s => (⟨some s, some .right⟩, some ())
    | none => (⟨none, none⟩, none)

/-- On `[true, false]` the head crosses the boundary between cells `0` and `1` once, entering
the (only) running state; it never crosses the boundary left of the input. -/
example : (rightMover.absInit [true, false]).crossings 1 3 = [some ()] := rfl

example : (rightMover.absInit [true, false]).crossings 0 3 = [] := by decide

example : (rightMover.absInit [true, false]).crossings 2 3 = [some ()] := rfl

/-- After three steps the run has halted on the blank cell `2`. -/
example : ((rightMover.absInit [true, false]).run 3).state = none ∧
    ((rightMover.absInit [true, false]).run 3).pos = 2 := by decide

/-- Edge case: a halted configuration crosses no boundary. -/
example (a : rightMover.AbsCfg) (h : a.state = none) (k : ℤ) (t : ℕ) :
    a.crossings k t = [] :=
  AbsCfg.crossings_of_none h k t

/-- The sum lemma on three boundaries: two crossings within three steps. -/
example : ∑ k ∈ ({0, 1, 2} : Finset ℤ), ((rightMover.absInit [true, false]).crossings k 3).length
    ≤ 3 :=
  AbsCfg.sum_length_crossings_le _ _ _

/-- The hard inputs are palindromes. -/
example : palWord false true 1 [true, false] = [true, false, false, false, true] := rfl

example : (palWord false true 1 [true, false]).Palindrome := by
  rw [List.Palindrome.iff_reverse_eq]
  rfl

/-- A failing instance: `rightMover`, like every single-tape machine, does not decide
palindromes in linear time. -/
example : ¬ rightMover.DecidesPalindromesInTime false true true fun n => 5 * (n + 1) :=
  not_decidesPalindromesInTime_linear Bool.false_ne_true 5

end ComplexityTests.SingleTapeCrossing
