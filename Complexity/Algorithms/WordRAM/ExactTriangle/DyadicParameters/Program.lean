/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.ExactTriangle.ParameterChoice
public import Complexity.Algorithms.WordRAM.NatLog
public import Complexity.Computability.WordRAM.Power.Rename
public import Complexity.Computability.WordRAM.Compile

/-!
# Native coarse ExactTriangle parameter computation

The fixed program computes the original parameter family from raw n using the existing
binary logarithm and two actual power calls. It leaves memory and the original dimension
unchanged. The flag explicitly separates the fast geometry from the small regime; no solver
or asymptotic endpoint is asserted by computing these parameters.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.DyadicParameters

open Cslib.WordRAM

namespace Reg
/-- Original matrix dimension, preserved. -/
abbrev side : Fin 16 := 0
/-- Complete logarithm-block count. -/
abbrev blocks : Fin 16 := 1
/-- Matrix/tile exponent m. -/
abbrev level : Fin 16 := 2
/-- Actual window D. -/
abbrev window : Fin 16 := 3
/-- Actual group count g. -/
abbrev groups : Fin 16 := 4
/-- Actual tensor depth L. -/
abbrev tensorDepth : Fin 16 := 5
/-- Raw Boolean for the positive-block (fast geometry) regime. -/
abbrev fast : Fin 16 := 6
/-- Shared logarithm argument / power result. -/
abbrev workValue : Fin 16 := 7
/-- Shared logarithm result / power counter. -/
abbrev workCount : Fin 16 := 8
/-- Power base register. -/
abbrev workBase : Fin 16 := 9
/-- Power exponent register. -/
abbrev workExponent : Fin 16 := 10
/-- Power constant-one register. -/
abbrev workOne : Fin 16 := 11
/-- Logarithm block divisor. -/
abbrev divisor : Fin 16 := 12
/-- Constant 36. -/
abbrev thirtySix : Fin 16 := 13
/-- Constant 19. -/
abbrev nineteen : Fin 16 := 14
/-- Constant four. -/
abbrev four : Fin 16 := 15
end Reg

/-- The logarithm uses registers 7 through 10. -/
@[expose] def logRegisters (i : Fin 4) : Fin 16 := ⟨i.val + 7, by omega⟩

/-- The subsequent power calls reuse registers 7 through 11. -/
@[expose] def powerRegisters (i : Fin 5) : Fin 16 := ⟨i.val + 7, by omega⟩

/-- Compute the integer exponents from the actual logarithm and deliver the first power call. -/
@[expose] def prepare : Code .standard 16 := ram[
  Reg.divisor ← #1296; Reg.blocks ← Reg.workCount / Reg.divisor;
  Reg.thirtySix ← #36; Reg.level ← Reg.thirtySix * Reg.blocks;
  Reg.nineteen ← #19; Reg.tensorDepth ← Reg.nineteen * Reg.level;
  Reg.four ← #4; Reg.workBase ← Reg.four;
  Reg.workExponent ← Reg.blocks ]

/-- Preserve g and deliver the second actual power call. -/
@[expose] def nextPower : Code .standard 16 := ram[
  Reg.groups ← Reg.workValue;
  Reg.workBase ← Reg.four; Reg.workExponent ← Reg.level ]

/-- Copy D and compute the explicit fast/small flag. -/
@[expose] def finish : Code .standard 16 :=
  .seq (ram[ Reg.window ← Reg.workValue; Reg.fast ← #0 ])
    (.branch (.lt Reg.fast Reg.blocks) (ram[ Reg.fast ← #1 ]) (ram[ Reg.fast ← Reg.fast ]))

/-- One uniform standard program for all input dimensions. -/
@[expose] def program : Code .standard 16 :=
  .seq (ram[ Reg.workValue ← Reg.side ])
    (.seq (NatLog.program.rename logRegisters)
      (.seq prepare (.seq (Power.program.rename powerRegisters)
        (.seq nextPower (.seq (Power.program.rename powerRegisters) finish)))))

/-- The native parameter code is fixed and cannot inspect physical width. -/
theorem program_fixed : (program.program Reg.fast).length ≤ 128 ∧
    ¬(program.program Reg.fast).ReadsWidth := by decide +kernel

end Cslib.Algorithms.WordRAM.ExactTriangle.DyadicParameters
