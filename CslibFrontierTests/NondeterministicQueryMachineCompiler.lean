/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.NondeterministicQueryMachine.Compiler
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite

/-! Tests for the native compiler of nondeterministic query machines on looping recognizers and
input-dependent start states. -/

namespace CslibFrontierTests.NondeterministicQueryMachineCompiler

open Turing Turing.MultiTapeTM

/-- Accept when the first input bit is `true`; otherwise loop in state `2` forever. The choice
bit is ignored. -/
private def firstBit : NondeterministicQueryMachine (Fin 3) where
  init := 0
  query _ := 0
  next p := if p.1 = 0 ∧ p.2.1 = some true then 1 else 2
  halted q := q == 1
  accept q := q == 1

/-- On the input `[false]`, every branch from the start state stays out of the halting state. -/
private theorem firstBit_run_ne_one (choices : List Bool) : firstBit.run [false] choices ≠ 1 := by
  have h (choices : List Bool) : firstBit.replay [false] choices 2 = 2 := by
    induction choices with
    | nil => rfl
    | cons b choices ih => exact ih
  cases choices with
  | nil => decide
  | cons b choices =>
    change firstBit.replay [false] choices 2 ≠ 1
    rw [h]
    decide

example : firstBit.Accepts [true] := ⟨[false], rfl, rfl⟩

example : ¬ firstBit.Accepts [false] := fun ⟨choices, hhalt, _⟩ =>
  firstBit_run_ne_one choices (beq_iff_eq.mp hhalt)

/-- The rejecting branch never halts, so no common abstract clock exists. -/
example (t : ℕ) : ¬ firstBit.HaltsWithin [false] t := fun h =>
  firstBit_run_ne_one _ (beq_iff_eq.mp (h (List.replicate t false) List.length_replicate))

/-- A looping recognizer with a constant start state compiles in logarithmic space. -/
example : ∃ (k : ℕ) (State : Type) (_ : Finite State) (ntm : MultiTapeNTM k Bool State) (c : ℕ),
    ntm.RecognizesInSpace encBits {input | firstBit.Accepts input}
      fun input => c * (Nat.log2 input.length + 1) :=
  firstBit.exists_recognizesInSpace (enc := encBits) (encS := encFinite (Fin 3))
    (ComputableInSpace.of_finite _) (ComputableInSpace.of_finite _)
    (ComputableInSpace.of_finite _) (ComputableInSpace.of_finite _)
    (fun _ => firstBit.init) (A := {input | firstBit.Accepts input}) (fun _ => Iff.rfl)
    (fun input : List Bool => Nat.log2 input.length + 1) (fun _ => le_rfl)
    ((ComputableInSpace.constZero _).mono_le fun _ => Nat.zero_le _)
    ⟨Nat.card (Fin 3), fun input choices =>
      (length_encFinite_lt (firstBit.run input choices)).le.trans
        (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))⟩

/-- The start state is the input bit itself: `true` halts and accepts at once, while `false`
loops forever. No step changes the state. -/
private def ownBit : NondeterministicQueryMachine Bool where
  init := false
  query _ := 0
  next p := p.1
  halted q := q
  accept q := q

private theorem ownBit_replay_false (choices : List Bool) :
    ownBit.replay (encBool false) choices false = false := by
  induction choices with
  | nil => rfl
  | cons b choices ih => exact ih

example : (ownBit.withInit true).Accepts (encBool true) := ⟨[], rfl, rfl⟩

example : ¬ (ownBit.withInit false).Accepts (encBool false) := by
  rintro ⟨choices, hhalt, -⟩
  rw [NondeterministicQueryMachine.run_withInit, ownBit_replay_false] at hhalt
  exact Bool.false_ne_true hhalt

/-- The start state depends on the input: the compiled machine recognizes `{true}`, starting
from the input bit, in constant space. -/
example : ∃ (k : ℕ) (State : Type) (_ : Finite State) (ntm : MultiTapeNTM k Bool State) (c : ℕ),
    ntm.RecognizesInSpace encBool {true} fun _ => c * 1 := by
  refine ownBit.exists_recognizesInSpace (enc := encBool) (encS := encBool)
    (ComputableInSpace.of_finite _) (ComputableInSpace.of_finite _)
    (ComputableInSpace.of_finite _) (ComputableInSpace.of_finite _)
    id (A := {true}) (fun b => ?_) (fun _ => 1) (fun _ => by simp)
    ((ComputableInSpace.of_finite id).mono_le fun _ => by simp)
    ⟨1, fun b choices => by simp⟩
  cases b
  · refine ⟨fun h => absurd h (by decide), fun ⟨choices, hhalt, _⟩ => ?_⟩
    change ownBit.replay (encBool false) choices false = true at hhalt
    rw [ownBit_replay_false] at hhalt
    exact absurd hhalt Bool.false_ne_true
  · exact ⟨fun _ => ⟨[], rfl, rfl⟩, fun _ => rfl⟩

end CslibFrontierTests.NondeterministicQueryMachineCompiler
