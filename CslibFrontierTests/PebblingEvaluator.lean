/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests of the pebbling evaluator)

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Space.PebblingEvaluator

/-! # The pebbling evaluator with gate calls

The computation on indices `0, 1, 2, 3` has source `[true]`, and the gate at `i` concatenates the
values at `i - 1` and `i - 2` (the second child of `1` is `0`). Its values are the unary Fibonacci
numbers `1, 2, 3, 5`. The gate machine is halted from the start and returns the concatenation of
the words it is started on. With four pebbles every index is pebblable, so the evaluator halts with
the value of index `3`, five `true`s, stored at `3`, and every state of its run fits the bound of
`exists_runFrom_machine`. -/

@[expose] public section

namespace CslibFrontierTests.PebblingEvaluator

open Turing Turing.MultiTapeTM Cslib.Pebbling Cslib.Pebbling.Descending
  Cslib.Pebbling.Descending.Evaluator

/-- Children `i - 1` and `i - 2`, for the single parameter. -/
def child (_ : Unit) (i : ℕ) (a : Fin 2) : ℕ := if a = 0 then i - 1 else i - 2

/-- The gate machine: halted from the start, it returns the concatenation of its words. -/
def gate : QueryMachine (List Bool) where
  init := []
  query _ := 0
  next cb := cb.1
  emit _ := []
  halted _ := true
  finish x := x

/-- The values: Fibonacci numbers in unary. -/
def value (i : ℕ) : List Bool := List.replicate ([1, 2, 3, 5].getD i 0) true

/-- The parameter carries no bits. -/
def encUnit : Unit ↪ List Bool := ⟨fun _ => [], fun _ _ _ => rfl⟩

theorem child_lt : ∀ i, 0 < i → ∀ a, child () i a < i := by
  intro i hi a
  unfold child
  split_ifs <;> omega

theorem flatten_eq : ∀ i, 0 < i → i < 4 →
    ((List.finRange 2).map fun a => value (child () i a)).flatten = value i := by
  have h : ∀ i < 4, 0 < i →
      ((List.finRange 2).map fun a => value (child () i a)).flatten = value i := by decide
  exact fun i hi h4 => h i h4 hi

theorem length_value_le : ∀ i < 4, (value i).length ≤ 5 := by decide

theorem pebblable : BlackPebblable (graph (N := 4) (child ())) 4 3 := by
  have h := blackPebblable_fintypeCard (wellFounded_graph (N := 4) (child ()) child_lt) 3
  rwa [Fintype.card_fin] at h

/-- The evaluator with four pebbles and room `45 = (4 + 1) * (4 + 4 + 1)` for a round of the walk
on four indices. -/
abbrev fibEvaluator := machine child (fun _ => 4) (fun _ => 45) (fun _ => [true]) gate
  (fun _ _ xs => xs.flatten)

-- The evaluator halts with the value of index `3` stored at `3`, within the space of
-- `exists_runFrom_machine`.
example : ∃ T c, fibEvaluator.runFrom [] (.inl (initialCaller () 4 3)) T = .inl c ∧
      c.2.lookup 3 = some (List.replicate 5 true) ∧
      ∀ t ≤ T, (QueryMachine.encWithCalls (encCaller encUnit) encBits
        (fibEvaluator.runFrom [] (.inl (initialCaller () 4 3)) t)).length ≤
          2 * callerBound 0 4 4 5 + 5 + 2 := by
  obtain ⟨T, -, -, ⟨c, hc, hl⟩, hB⟩ := exists_runFrom_machine child (fun _ => 4) (fun _ => 45)
    (fun _ => [true]) gate (fun _ _ xs => xs.flatten) encUnit encBits [] (p := ()) (N := 4)
    (root := 3) (value := value) (V := 5) (D := 5) child_lt pebblable le_rfl rfl length_value_le
    fun i hi h4 => ⟨0, rfl, flatten_eq i hi h4, fun t ht => by
      obtain rfl := Nat.le_zero.1 ht
      change (((List.finRange 2).map fun a => value (child () i a)).flatten).length ≤ 5
      rw [flatten_eq i hi h4]
      exact length_value_le i h4⟩
  exact ⟨T, c, hc, hl, hB⟩

end CslibFrontierTests.PebblingEvaluator
