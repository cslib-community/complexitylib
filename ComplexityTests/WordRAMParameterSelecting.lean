/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

-- upstream: local-only (tests)

import Complexity.Algorithms.WordRAM.ExactTriangle.ParameterSelecting.Program

/-!
# Complete parameter-selecting program on actual small inputs

These runs execute the real parameter block, its computed small flag, the real exhaustive
solver and original-argument restoration. The three matrix spans alias, high old registers
are nonzero and scratch/outside memory is dirty. No fast-geometry theorem is applied to these
small dimensions. Complete admitted large-geometry clients are separate proof clients.
-/

set_option linter.hashCommand false

namespace ComplexityTests.WordRAMParameterSelecting

open Cslib.WordRAM
open Cslib.Algorithms.WordRAM.ExactTriangle

private def smallInput (n : ℕ) (z : ℤ) : Data 640 :=
  { regs := fun j =>
      if j.val = 0 then n else if j.val = 1 then z.natAbs + 1
      else if j.val = 2 ∨ j.val = 3 ∨ j.val = 4 then 1
      else if j.val = 5 then n * n + 16 else 717
    mem := fun q => if 1 ≤ q ∧ q < n * n + 1 then Signed.encode z else 99 }

private def runSmall (n : ℕ) (z : ℤ) : Option (List ℕ) :=
  (ParameterSelecting.program.eval 32 12 (smallInput n z)).map fun (y, _) =>
    [y.regs 0, y.regs 1, y.regs 2, y.regs 3, y.regs 4, y.regs 5, y.regs 6,
      y.regs (ParameterSelecting.parameterBank DyadicParameters.Reg.fast),
      y.regs (ParameterSelecting.parameterBank DyadicParameters.Reg.window),
      y.regs (ParameterSelecting.parameterBank DyadicParameters.Reg.groups),
      y.mem 0, y.mem (n * n + 15), y.regs 639]

#guard runSmall 0 0 == some [0, 1, 1, 1, 1, 16, 0, 0, 1, 1, 99, 99, 717]
#guard runSmall 1 0 == some [1, 1, 1, 1, 1, 17, 1, 0, 1, 1, 99, 99, 717]
#guard runSmall 1 1 == some [1, 2, 1, 1, 1, 17, 0, 0, 1, 1, 99, 99, 717]
#guard runSmall 1 (-1) == some [1, 2, 1, 1, 1, 17, 0, 0, 1, 1, 99, 99, 717]
#guard runSmall 2 0 == some [2, 1, 1, 1, 1, 20, 1, 0, 1, 1, 99, 99, 717]

end ComplexityTests.WordRAMParameterSelecting
