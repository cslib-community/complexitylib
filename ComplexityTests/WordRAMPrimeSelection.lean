/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

-- upstream: local-only (tests)

import Complexity.Algorithms.WordRAM.ExactTriangle.PrimeSelection.Keep

/-!
# Native prime-selector controller regressions

These execute the actual selector/trial-division controller with small explicit score programs.
The scores isolate enumeration, endpoints, minimum updates and stable ties. They are not
modular triangle counters and do not certify the missing concrete-counter instantiation.
-/

set_option linter.hashCommand false

namespace ComplexityTests.WordRAMPrimeSelection

open Cslib.WordRAM
open Cslib.Algorithms.WordRAM.ExactTriangle.PrimeSelection

private abbrev p : Fin 128 := 65
private abbrev result : Fin 128 := 70
private abbrev divisor : Fin 128 := 127

private def remainderScore : Code .standard 128 := ram[
  divisor ← #5; result ← p % divisor ]

private def constantScore : Code .standard 128 := ram[ result ← #1 ]

private def runScore (D : ℕ) (score : Code .standard 128) : Code .standard 160 :=
  .seq (ram[ Reg.window ← #D; Reg.side ← #0; Reg.inputAB ← #10;
    Reg.inputBC ← #20; Reg.inputAC ← #30; Reg.scratch ← #100 ]) (program score)

-- The lower endpoint 3 belongs to the D=36 window. Prime 5 then improves its score to zero.
#guard match (runScore 36 remainderScore).eval 10 1000 (.init [999]) with
  | some (y, _) => y.regs Reg.best == 5 && y.regs Reg.bestCount == 0 &&
      y.regs Reg.found == 1 && y.mem 1 == 999 && y.regs Reg.inputAB == 10
  | none => false

-- Equal scores retain the first prime, including the closed lower endpoint.
#guard match (runScore 36 constantScore).eval 10 1000 (.init [999]) with
  | some (y, _) => y.regs Reg.best == 3 && y.regs Reg.bestCount == 1 && y.mem 1 == 999
  | none => false

-- D=25 excludes the prime at the open upper endpoint 5 and the candidate below sqrt(D)/2.
#guard match (runScore 25 remainderScore).eval 10 1000 (.init [999]) with
  | some (y, _) => y.regs Reg.best == 3 && y.regs Reg.bestCount == 3
  | none => false

-- No admitted geometry is asserted here: an empty window leaves the explicit zero default.
#guard match (runScore 4 constantScore).eval 10 1000 (.init [999]) with
  | some (y, _) => y.regs Reg.best == 0 && y.regs Reg.found == 0 && y.mem 1 == 999
  | none => false

end ComplexityTests.WordRAMPrimeSelection
