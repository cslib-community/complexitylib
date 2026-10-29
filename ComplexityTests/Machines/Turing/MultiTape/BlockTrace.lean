/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: local-only (test driver)

public import Complexity.Computability.Machines.Turing.MultiTape.BlockTrace
import Mathlib.Tactic.NormNum

/-! # Native time-block boundary tests

The concrete machine writes an actual zero at a negative work-tape address, moves left,
emits one zero after an existing output prefix, and halts. The symbolic controls include
zero work tapes, arbitrary nonhalting prefixes and clipped final blocks.
-/

public section

open Turing
namespace BlockTraceTests

/-- A one-step native machine that writes and emits zero, then halts. -/
@[expose] def writeZero : MultiTapeTM 1 Bool Unit := MultiTapeTM.ofTr () fun _ _ _ =>
  { inputTape := 0
    workTapes := fun _ => (some (some false), -1)
    output := some false
    state := none }

/-- A blank native tape with negative head position and an existing output prefix. -/
@[expose] def start : Cfg 1 Bool Unit [] :=
  { state := some ()
    inputPos := 0
    workTapes := fun _ _ => none
    workTapePos := fun _ => -2
    output := [true, true] }

-- The zero-radius window stores the real blank marker, not a default Boolean zero.
example : start.workWindow 0 0 0 = none := rfl
example : start.workWindow 0 0 0 ≠ some false := by decide

/-- The native write changes the scanned negative cell into a written zero. -/
theorem writtenZero : (writeZero.runFrom start 1).workTapes 0 (-2) = some false := by
  rw [MultiTapeTM.runFrom_one, MultiTapeTM.step_of_state (show start.state = some () from rfl)]
  simp [writeZero, Action.apply, start]

example : (writeZero.runFrom start 1).workTapePos 0 = -3 := by
  rw [MultiTapeTM.runFrom_one, MultiTapeTM.step_of_state (show start.state = some () from rfl)]
  simp [writeZero, Action.apply, start]

-- A genuinely exterior negative cell remains blank.
example : (writeZero.runFrom start 1).workTapes 0 (-4) = none := by
  have hout : (1 : ℤ) < |(-4 : ℤ) - start.workTapePos 0| := by norm_num [start]
  exact writeZero.workTapes_runFrom_eq_of_outside_window start 1 0 (-4) hout

-- New output contains no copy of the old prefix.
example : writeZero.blockEmitted start 1 = [false] := by
  unfold MultiTapeTM.blockEmitted
  rw [MultiTapeTM.runFrom_one, MultiTapeTM.step_of_state (show start.state = some () from rfl)]
  simp [writeZero, Action.apply, start]

example : (writeZero.runFrom start 1).output = [true, true, false] := by
  rw [MultiTapeTM.runFrom_one, MultiTapeTM.step_of_state (show start.state = some () from rfl)]
  simp [writeZero, Action.apply, start]

private theorem haltedAfterOne : (writeZero.runFrom start 1).Halted := by
  rw [MultiTapeTM.runFrom_one, MultiTapeTM.step_of_state (show start.state = some () from rfl)]
  simp [writeZero, Action.apply, Cfg.Halted]

-- All later blocks retain the ENTIRE halted native configuration.
example (width index : ℕ) : writeZero.blockStart (writeZero.runFrom start 1) width index =
    writeZero.runFrom start 1 :=
  writeZero.blockStart_eq_of_halted _ haltedAfterOne width index

-- Zero and clipped-final cases use real native runs, not an assumed halting computation.
example : MultiTapeTM.blockDuration 10 4 2 = 2 := rfl
example : MultiTapeTM.blockDuration 10 4 3 = 0 := rfl
example (horizon index : ℕ) : MultiTapeTM.blockDuration horizon 0 index = 0 := by simp
example : writeZero.runFrom (writeZero.blockStart start 4 2)
    (MultiTapeTM.blockDuration 10 4 2) = writeZero.runFrom start 10 := by
  simpa using writeZero.runFrom_blockDuration start 10 4 2 (by decide)

-- No finite-control or halting premise: any native machine's local head stays in its window.
example {k : ℕ} {State : Type} {input : List Bool} (tm : MultiTapeTM k Bool State)
    (cfg : Cfg k Bool State input) (duration : ℕ) (tape : Fin k) :
    |(tm.runFrom cfg duration).workTapePos tape - cfg.workTapePos tape| ≤ (duration : ℤ) :=
  tm.workTapePos_runFrom_abs_sub_le cfg duration tape

-- With no work tapes the snapshot has no hidden work-tape payload.
example {State : Type} {input : List Bool} (cfg : Cfg 0 Bool State input) (radius : ℕ)
    (i : Fin 0) : cfg.workWindow radius i = fun _ => none := i.elim0

end BlockTraceTests
