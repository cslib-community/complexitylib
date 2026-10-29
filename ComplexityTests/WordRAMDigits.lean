/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.WordRAM.Multiword.Transfer
import Complexity.Computability.WordRAM.Multiword.Bitwise
import Complexity.Computability.WordRAM.Multiword.Shift

/-! Shared digit clients work without importing the full multiplication development. -/

namespace WordRAMDigitsTests

open Cslib.WordRAM Cslib.WordRAM.Multiword

open Lean Elab Command in
run_cmd do
  if (← getEnv).header.moduleNames.contains
      `Complexity.Computability.WordRAM.Multiword.Mul then
    throwError "digit operations must not import full multiplication"

-- The representation applies to arbitrary register counts, including zero and one, and a minimal
-- client can set up workspace and assemble digits without any multiplication theorem.
example (x0 : Data 0) (x1 : Data 1) (x5 : Data 5) :
    (value 2 x0 [] = 0 ∧ Bounded 2 x0 [] ∧ value 10 x1 [0, 0] = x1.regs 0 + 10 * x1.regs 0) ∧
    Exec 2 Workspace.setup x5 (Workspace.setupResult 2 x5) 6 ∧
    (Workspace.setupResult 2 x5).regs 4 = x5.regs 4 ∧
    (Transfer.assemble ([0, 1] : List (Fin 5)) 2).size = 12 :=
  ⟨⟨rfl, by simp [Bounded], rfl⟩,
   Workspace.exec_setup (by decide) x5,
   Workspace.setup_digit 2 x5 (by dsimp [Workspace.IsDigit]; omega),
   Transfer.size_assemble [0, 1] 2⟩

end WordRAMDigitsTests
