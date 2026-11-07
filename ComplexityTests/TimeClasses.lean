/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import Complexity.Computability.Complexity.Classes.FunctionTime
import Complexity.Computability.Complexity.Classes.SharpP.Time
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat.Bits
import Cslib.Computability.Machines.Turing.MultiTape.Combinators.Id
import Cslib.Computability.Machines.Turing.MultiTape.Combinators.AlmostConstant
import Mathlib.Tactic.FinCases

/-! Concrete function-time and terminal-path-counting clients.

The deterministic copy machine witnesses linear function time, and a constant binary natural
output witnesses constant function time. Native singleton rejecting/accepting machines witness
counts zero and one, while two identical accepting occurrences witness count two. Increasing the
clock leaves that terminal count at two, rather than multiplying it by free choice-bit padding.
-/

namespace ComplexityTests.TimeClasses

open Cslib.Complexity _root_.Turing _root_.Turing.MultiTapeTM

example : (id : List Bool → List Bool) ∈ FTIME encBits encBits (fun n => n + 1) :=
  FTIME.of_computableInTimeAndSpace (s := fun _ => 0) computableInTimeAndSpace_id

/-- Counts are output in binary: this machine computes the natural `2`, not a decision bit. -/
example : (fun _ : List Bool => 2) ∈ FTIME encBits encNat (fun _ => 1) := by
  obtain ⟨c, h⟩ := computableInTimeAndSpace_of_const (encIn := encBits) (encOut := encNat) 2
  refine ⟨0, c, fun _ => 0, ?_⟩
  simpa only [Nat.zero_mul, Nat.zero_add, Function.const_def] using h

private def stop (bit : Bool) : MultiTapeMachine.Action 0 Bool Unit Empty :=
  .step { inputTape := 0, workTapes := Fin.elim0, output := some bit, state := none }
    Empty.elim Empty.elim

private def singleton (bit : Bool) : MultiTapeCTM 0 Bool Unit where
  initial := ()
  tr _ _ _ _ := [stop bit]

private def double : MultiTapeCTM 0 Bool Unit where
  initial := ()
  tr _ _ _ _ := [stop true, stop true]

private theorem singleton_halts (bit : Bool) (input : List Bool) :
    (singleton bit).HaltsWithin 1 (Cfg.init (singleton bit).initial input) := by
  apply MultiTapeCTM.HaltsWithin.step (by exact List.cons_ne_nil _ _)
  intro index
  fin_cases index
  exact .halt rfl

private theorem double_halts (input : List Bool) :
    double.HaltsWithin 1 (Cfg.init double.initial input) := by
  apply MultiTapeCTM.HaltsWithin.step (by exact List.cons_ne_nil _ _)
  intro index
  fin_cases index <;> exact .halt rfl

private theorem singleton_count (bit : Bool) (input : List Bool) :
    (singleton bit).acceptCount 1 (Cfg.init (singleton bit).initial input) =
      if bit then 1 else 0 := by
  change (singleton bit).branchCount (· == [true]) _ _ = _
  rw [(singleton_halts bit input).branchCount_eq_countP,
    MultiTapeCTM.runList_succ _ _ 0 () rfl]
  cases bit <;>
    simp [MultiTapeCTM.actions, singleton, stop, MultiTapeMachine.Action.emptyOracleEquiv,
      Turing.Action.apply, Cfg.init]

private theorem double_count (input : List Bool) :
    double.acceptCount 1 (Cfg.init double.initial input) = 2 := by
  change double.branchCount (· == [true]) _ _ = 2
  rw [(double_halts input).branchCount_eq_countP,
    MultiTapeCTM.runList_succ _ _ 0 () rfl]
  simp [MultiTapeCTM.actions, double, stop, MultiTapeMachine.Action.emptyOracleEquiv,
      Turing.Action.apply, Cfg.init]

/-- Zero counts come from real rejecting terminal branches, not a stuck transition table. -/
example (t : ℕ → ℕ) : (fun _ : List Bool => 0) ∈ SharpTIME encBits t := by
  refine ⟨0, 1, 0, Unit, inferInstance, singleton false, ?_, fun input => ?_⟩
  · intro _ _ _
    exact List.cons_ne_nil _ _
  · constructor
    · simpa only [Nat.zero_mul, Nat.zero_add] using singleton_halts false (encBits input)
    · simpa only [Nat.zero_mul, Nat.zero_add, Bool.false_eq_true, ↓reduceIte] using
        singleton_count false (encBits input)

example (t : ℕ → ℕ) : (fun _ : List Bool => 1) ∈ SharpTIME encBits t := by
  refine ⟨0, 1, 0, Unit, inferInstance, singleton true, ?_, fun input => ?_⟩
  · intro _ _ _
    exact List.cons_ne_nil _ _
  · constructor
    · simpa only [Nat.zero_mul, Nat.zero_add] using singleton_halts true (encBits input)
    · simpa only [Nat.zero_mul, Nat.zero_add, ↓reduceIte] using
        singleton_count true (encBits input)

/-- Repeated identical actions are two paths, even though they have the same final configuration. -/
example (t : ℕ → ℕ) : (fun _ : List Bool => 2) ∈ SharpTIME encBits t := by
  refine ⟨0, 1, 0, Unit, inferInstance, double, ?_, fun input => ?_⟩
  · intro _ _ _
    exact List.cons_ne_nil _ _
  · constructor
    · simpa only [Nat.zero_mul, Nat.zero_add] using double_halts (encBits input)
    · simpa only [Nat.zero_mul, Nat.zero_add] using double_count (encBits input)

/-- Six extra time steps after halting do not create new accepting paths. -/
example (input : List Bool) : double.acceptCount 7 (Cfg.init double.initial input) = 2 := by
  change double.branchCount (· == [true]) 7 (Cfg.init double.initial input) = 2
  rw [(double_halts input).branchCount_eq (by decide)]
  exact double_count input

private def stuck : MultiTapeCTM 0 Bool Unit where
  initial := ()
  tr _ _ _ _ := []

/-- An empty live choice list fails the all-branches halting contract. -/
example (input : List Bool) : ¬ stuck.HaltsWithin 7 (Cfg.init stuck.initial input) := by
  intro h
  cases h with
  | halt hhalt => cases hhalt
  | step hnon _ => exact hnon rfl

end ComplexityTests.TimeClasses
