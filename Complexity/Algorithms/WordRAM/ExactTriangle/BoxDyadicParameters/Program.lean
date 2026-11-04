/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.ExactTriangle.BoxParameterChoice
public import Complexity.Algorithms.WordRAM.ExactTriangle.DyadicParameters.Program

/-!
# Native integer-block parameters for the improved box solver

The actual logarithm and two power calls compute `b=floor(log2(n)/2394)`, `m=63b`,
`D=4^m`, `g=4^(2b)` and `L=21m`. The existing sixteen-register bank and unchanged power
handoff/fast-flag code are reused. These are original native integer parameters rather than
the source's fractional-root computation. Complete charged execution is proved separately.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.BoxDyadicParameters

open Cslib.WordRAM DyadicParameters

/-- Compute every exponent from the real logarithm and deliver the group power call. -/
@[expose] def prepare : Code .standard 16 :=
  let levelFactor : Fin 16 := 13
  let depthFactor : Fin 16 := 14
  ram[ Reg.divisor ← #2394; Reg.blocks ← Reg.workCount / Reg.divisor;
    levelFactor ← #63; Reg.level ← levelFactor * Reg.blocks;
    depthFactor ← #21; Reg.tensorDepth ← depthFactor * Reg.level;
    Reg.four ← #4; Reg.workBase ← Reg.four;
    Reg.workExponent ← Reg.blocks + Reg.blocks ]

/-- Actual integer logarithm, exponent arithmetic, two native powers and fast/small flag. -/
@[expose] def program : Code .standard 16 :=
  .seq (ram[ Reg.workValue ← Reg.side ])
    (.seq (NatLog.program.rename logRegisters)
      (.seq prepare (.seq (Power.program.rename powerRegisters)
        (.seq nextPower (.seq (Power.program.rename powerRegisters) finish)))))

/-- The retuned native parameter program is fixed and never reads physical width. -/
theorem program_fixed : (program.program Reg.fast).length ≤ 128 ∧
    ¬(program.program Reg.fast).ReadsWidth := by decide +kernel

end Cslib.Algorithms.WordRAM.ExactTriangle.BoxDyadicParameters
