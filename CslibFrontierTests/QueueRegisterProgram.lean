/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.DataStructure.Queue.WordRAM.RegisterProgram

/-! Paid raw setup in the same globally chosen register file as both method bodies. These
checks establish six actual writes and literal dirty-memory preservation; the full initialized
representation and persistent dispatcher certificate remain separate proof obligations. -/

@[expose] public section

namespace ComplexityTests.QueueRegisterProgram

open Cslib.WordRAM
open Cslib.DataStructure.Queue.WordRAM

/-- Every entry register and cell starts dirty, including the frontier and count words. -/
def rawTwo : Data registers := ⟨fun _ => 3, fun _ => 3⟩

theorem rawTwo_bounded : rawTwo.Bounded 2 :=
  ⟨fun _ => (by decide : Fits 2 3), fun _ => (by decide : Fits 2 3)⟩

-- The decisive old width2/base1/C1 domain, with no two extra count cells.
example : ∃ y, Exec 2 (initializeCode 1 1) rawTwo y 6 ∧ y.Bounded 2 ∧
    y.mem = rawTwo.mem := by
  exact ⟨initialized 1 1 rawTwo, initialize_exec rawTwo_bounded (by decide)⟩

/-- Capacity zero still starts from arbitrary dirty bounded memory. -/
def rawOne : Data registers := ⟨fun _ => 1, fun _ => 1⟩

theorem rawOne_bounded : rawOne.Bounded 1 :=
  ⟨fun _ => (by decide : Fits 1 1), fun _ => (by decide : Fits 1 1)⟩

example : ∃ y, Exec 1 (initializeCode 0 0) rawOne y 6 ∧ y.Bounded 1 ∧
    y.mem = rawOne.mem := by
  exact ⟨initialized 0 0 rawOne, initialize_exec rawOne_bounded (by decide)⟩

end ComplexityTests.QueueRegisterProgram
