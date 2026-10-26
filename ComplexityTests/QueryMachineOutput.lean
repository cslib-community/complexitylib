/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests of query-machine output)

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.QueryMachine

/-!
# Query-machine output after halting

The transition freezes at a halted state even when its raw emission function is nonempty.
Padding a clock must not invoke that function again or duplicate the final word.
-/

@[expose] public section

namespace ComplexityTests.QueryMachineOutput

open Turing

/-- The initial state is halted even though its raw emission function is nonempty. -/
def halted : QueryMachine Unit where
  init := ()
  query _ := 0
  next _ := ()
  emit _ := [true]
  halted _ := true
  finish _ := [false]

example : halted.output [] 0 = [false] := rfl

example : halted.output [] 3 = [false] := by decide

/-- Emit the first input bit, then halt and append a final bit. -/
def echoOnce : QueryMachine Bool where
  init := false
  query _ := 0
  next _ := true
  emit p := [p.2.getD false]
  halted := id
  finish _ := [false]

example : echoOnce.output [true] 1 = [true, false] := by decide

example : echoOnce.output [true] 4 = [true, false] := by decide

example : echoOnce.output [] 4 = [false, false] := by decide

example (k : ℕ) : echoOnce.output [true] (1 + k) = [true, false] := by
  rw [echoOnce.output_add_of_halted [true] (t := 1) (by decide)]
  decide

end ComplexityTests.QueryMachineOutput
