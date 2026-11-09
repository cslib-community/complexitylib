/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests of the native local replay gate)

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.QueryReplayGateCorrect
public import ComplexityTests.Machines.Turing.MultiTape.NativeBlockCodec

/-!
# Native local-gate regressions

The input head reaches the right blank boundary while a work head moves to the left block.
Correct labels return the updated window; changing either head's expected label returns FAIL.
The left blank boundary and the positive-width guard are tested separately.
-/

@[expose] public section

namespace ComplexityTests.QueryReplayGate

open Turing MultiTapeTM MultiTapePTM.BlockComputation
open MultiTapePTM.BlockComputation.QueryReplay

example : Motion.inputMatches 2 0 0 0 .neg = true := rfl
example : Motion.inputMatches 2 0 0 0 .zero = false := rfl
example : Motion.inputMatches 2 0 1 0 .zero = true := rfl
example : Motion.inputMatches 2 0 1 1 .pos = true := rfl
example : Motion.inputMatches 2 0 0 3 .pos = true := rfl
example : Motion.workMatches 2 0 .neg = true := rfl
example : Motion.workMatches 2 2 .zero = true := rfl
example : Motion.workMatches 2 4 .pos = true := rfl

def row (input work : SignType) : Option (Fin 1) → SignType :=
  fun h => h.elim input (fun _ => work)

def raw : RawResult 1 (Fin 1) := (some 0, fun _ => 0, .empty, fun _ => [0, 1, 2])

def reader : MultiTapeTM 1 Bool (Fin 1) := MultiTapeTM.ofTr 0 fun _ input _ =>
  { inputTape := .pos, workTapes := fun _ => (some input, .neg), output := some true,
    state := none }

noncomputable def gate := Gate.machine reader NativeBlockCodec.code

def start (expected : Option (Fin 1) → SignType) : Gate.State 1 (Fin 1) :=
  ((0, 0, expected), Load.load (1, 1, (0, 0), raw))

def done (expected : Option (Fin 1) → SignType) : Gate.State 1 (Fin 1) :=
  ((0, 0, expected), ⟨1, 1, 0, 2, none, fun _ => 0, fun _ => [0, 2, 2], .accept⟩)

private theorem run_one (expected : Option (Fin 1) → SignType) :
    gate.runFrom [true] (start expected) 1 = done expected := by
  unfold gate start
  rw [Gate.runFrom_eq]
  simp only [QueryMachine.runFrom_succ, QueryMachine.runFrom_zero, QueryMachine.step,
    QueryReplay.machine, QueryMachine.read, tick, reader, MultiTapeTM.tr_ofTr]
  rfl

example : Motion.valid (0, 0, row .pos .neg, (done (row .pos .neg)).2) = true := rfl
example : Motion.valid (0, 0, row .zero .neg, (done (row .zero .neg)).2) = false := rfl
example : Motion.valid (0, 0, row .pos .zero, (done (row .pos .zero)).2) = false := rfl
example : Motion.valid (0, 0, row .zero .zero,
    { (done (row .zero .zero)).2 with width := 0 }) = false := rfl

example : Encoding.NativeDecode.parse (k := 1) NativeBlockCodec.code
    (1, gate.finish (gate.runFrom [true] (start (row .pos .neg)) 1)) =
      some (none, fun _ => 0, .accept, fun _ => [0, 2, 2]) := by
  rw [run_one]
  decide

example : gate.finish (gate.runFrom [true] (start (row .zero .neg)) 1) =
    List.replicate (Encoding.width 1 1 1) false := by rw [run_one]; decide
example : gate.finish (gate.runFrom [true] (start (row .pos .zero)) 1) =
    List.replicate (Encoding.width 1 1 1) false := by rw [run_one]; decide

/-- The actual final word, including FAIL, has a native certificate using retained storage. -/
example : ComputableInSpace gate.finish Gate.encState encBits
    (fun state => (Gate.encState state).length) := Gate.machine_finish_inSpace _ _

end ComplexityTests.QueryReplayGate
