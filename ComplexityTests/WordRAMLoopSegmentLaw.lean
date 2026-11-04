/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Computability.WordRAM.Randomized.LoopSegmentLaw

/-!
# A paid loop-segment observation law

A one-bit program sets its first register to one, exits the loop and observes that register.
The single segment charges the body and two loop instructions; finishing charges two more.
-/

@[expose] public section

namespace ComplexityTests.WordRAMLoopSegmentLaw

open Cslib Cslib.WordRAM

def start : Data 2 := ⟨![0, 1], fun _ => 0⟩

def stop : Data 2 := start.set 0 1

example : ExecRandLaw 1 (.loop (.lt 0 1) (.op (.const 0 1) : Code .standard 2)) start
    (· = stop) 5 0 (fun y => y.regs 0) (PMF.pure 1) := by
  have hbody : ExecWithin 1 (.op (.const 0 1) : Code .standard 2) start stop 1 :=
    (Exec.const (by decide)).within
  have hlaw := LoopSegmentLaw.single (cond := Cond.lt 0 1)
    (show (Cond.lt 0 1).Holds start by decide)
    (ExecRandLaw.of_execWithin (P := (· = stop)) (f := fun y => y.regs 0) hbody rfl)
  exact hlaw.finish fun y hy => hy ▸ (by decide)

end ComplexityTests.WordRAMLoopSegmentLaw
