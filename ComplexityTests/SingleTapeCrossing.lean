/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.SingleTape.Palindrome

/-!
# Tests for crossing sequences and the palindrome lower bound

A concrete single-tape machine with computed crossing sequences, the sum and halting edge cases,
translation invariance, cut-and-paste at different positions (and why the prefix hypothesis is
needed), a decider that answers under the head, the hard palindrome inputs, and failing instances
of both palindrome decision notions.
-/

namespace ComplexityTests.SingleTapeCrossing

open Cslib Cslib.Turing SingleTapeTM Relation

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

/-- Translation invariance on a concrete run: shifting by `3` moves the crossing at `1` to `4`. -/
example : ((rightMover.absInit [true, false]).shift 3).crossings 4 3 = [some ()] := rfl

/-- Cut-and-paste with prefixes of different lengths: the crossing sequence after `[true]` on
`[true, false]` matches the one after `[false, true]` on `[false, true, true]`, so the run on
`[true, true]` halts within `3 + 4` steps. -/
example : ((rightMover.absInit ([true] ++ [true])).run (3 + 4)).state = none :=
  (cut_and_paste_run (u₁ := [true]) (v₁ := [false]) (u₂ := [false, true]) (v₂ := [true])
    (t₁ := 3) (t₂ := 4) (by simp) rfl rfl rfl).1

/-- A one-state machine that halts at once, leaving the tape unchanged. -/
def stayer : SingleTapeTM Bool where
  State := Unit
  q₀ := ()
  tr _ s := (⟨s, none⟩, none)

/-- Edge case: the hypothesis that the prefixes are both empty or both nonempty cannot be
dropped from `cut_and_paste_run`. With `u₁ = []`, `v₁ = [false]`, `u₂ = [false]` and
`v₂ = [true]`, both runs halt after one step without crossing the boundary after the prefix, yet
the run on `u₁ ++ v₂ = [true]` scans `true` while both original runs scan `false`. -/
example : ((stayer.absInit ([] ++ [false])).run 1).state = none ∧
    ((stayer.absInit ([false] ++ [true])).run 1).state = none ∧
    (stayer.absInit ([] ++ [false])).crossings ([] : List Bool).length 1 =
      (stayer.absInit ([false] ++ [true])).crossings [false].length 1 ∧
    ((stayer.absInit ([] ++ [true])).run (1 + 1)).scanned = some true ∧
    ((stayer.absInit ([] ++ [false])).run 1).scanned = some false ∧
    ((stayer.absInit ([false] ++ [true])).run 1).scanned = some false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Nonvacuity of `DecidesByHeadInTime`: `stayer` decides within one step the words whose first
letter is `true`, answering with the symbol it leaves under the head. -/
example : stayer.DecidesByHeadInTime id {w : List Bool | w.head? = some true} true fun _ => 1 := by
  intro w
  refine ⟨⟨none, BiTape.mk₁ (w.map id)⟩, RelatesWithinSteps.single ?_, rfl, ?_⟩
  · simp only [TransitionRelation, step, initCfg, stayer, List.map_id]
    rw [BiTape.write_head_self]
    rfl
  · simp only [BiTape.head_mk₁, List.map_id]
    exact Iff.rfl

/-- The hard inputs are palindromes. -/
example : palWord 1 [true, false] = [true, false, false, false, true] := rfl

example : (palWord 1 [true, false]).Palindrome := by
  rw [List.Palindrome.iff_reverse_eq]
  rfl

/-- A failing instance: `rightMover`, like every single-tape machine, does not decide
palindromes in linear time. -/
example : ¬ rightMover.DecidesPalindromesInTime false true true fun n => 5 * (n + 1) :=
  not_decidesPalindromesInTime_linear Bool.false_ne_true 5

/-- Nor does `stayer`, even answering under the head. -/
example : ¬ stayer.DecidesByHeadInTime id {w : List Bool | w.Palindrome} true
    fun n => 5 * (n + 1) :=
  not_decidesByHeadInTime_palindromes_linear id true 5

end ComplexityTests.SingleTapeCrossing
