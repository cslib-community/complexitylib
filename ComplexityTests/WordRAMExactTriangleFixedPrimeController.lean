/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

-- upstream: local-only (tests)

import Complexity.Algorithms.WordRAM.ExactTriangle.FixedPrime.Controller
import Complexity.Algorithms.WordRAM.ExactTriangle.FixedPrime.Potential

/-!
# Concrete native catalogue controller regressions

These executions check actual counter delivery, failed/successful returns and the real loop's
exit guard. They are controller fixtures, not supplied-callee/full-solver execution examples.
The initialized valid-geometry solver clients are checked in their separate test module.
-/

set_option linter.hashCommand false

namespace ComplexityTests.WordRAMExactTriangleFixedPrimeController

open Cslib.WordRAM
open Cslib.Algorithms.WordRAM.ExactTriangle

private def fixture (flag : ℕ) : Data 416 :=
  { regs := fun j =>
      if j.val = 40 then 7 else if j.val = 392 then flag else if j.val = 396 then 3
      else if j.val = 400 then 2 else if j.val = 401 then 7 else if j.val = 403 then 5
      else if j.val = 404 then 1 else 99
    mem := fun a => if a = 17 then 123 else 0 }

private def observe (code : Code .standard 416) (flag : ℕ) : Option (List ℕ × ℕ) :=
  (code.eval 16 0 (fixture flag)).map fun (y, t) =>
    ([y.regs FixedPrime.Reg.index, y.regs FixedPrime.Reg.limit,
      y.regs FixedPrime.Reg.found, y.regs FixedPrime.Reg.scans, y.regs FixedPrime.Reg.one,
      y.regs 392, y.mem 17], t)

#guard observe FixedPrime.setup 1 == some ([0, 7, 0, 0, 1, 1, 123], 5)
#guard observe FixedPrime.select 0 == some ([2, 7, 99, 5, 1, 0, 123], 1)
#guard observe FixedPrime.receive 0 == some ([3, 7, 0, 8, 1, 0, 123], 6)
#guard observe FixedPrime.receive 1 == some ([3, 3, 1, 8, 1, 1, 123], 5)

-- A successful return closes the actual loop immediately, even with zero body fuel. The
-- embedded body is the real record program, not a substitute solver.
private def stopped : Option (ℕ × ℕ) := do
  let (y, _) ← FixedPrime.receive.eval 16 0 (fixture 1)
  let (z, t) ← (Code.loop (.lt FixedPrime.Reg.index FixedPrime.Reg.limit)
    FixedPrime.step).eval 16 0 y
  pure (z.regs FixedPrime.Reg.scans, t)

#guard stopped == some (8, 2)

-- A failed record leaves more work and therefore cannot exit with zero body fuel.
private def pending : Option (Data 416 × ℕ) := do
  let (y, _) ← FixedPrime.receive.eval 16 0 (fixture 0)
  (Code.loop (.lt FixedPrime.Reg.index FixedPrime.Reg.limit) FixedPrime.step).eval 16 0 y

#guard pending.isNone

-- The single reserve pays exactly one actual success and none for an unsuccessful return.
example : 20 + 2 + (11 + 7 * (5 + 1 - 1)) ≤ 8 + 11 + 7 * (1 + 5 + 1) :=
  FixedPrime.pay_return (by decide) (by decide : 2 ≤ 1 + 1) (by decide)

end ComplexityTests.WordRAMExactTriangleFixedPrimeController
