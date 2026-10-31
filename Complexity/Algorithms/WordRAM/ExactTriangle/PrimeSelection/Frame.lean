/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.PrimeSelection.Program
import Mathlib.Tactic.NormNum

/-!
# Prime-selector register frames

The entire counting program runs below register 128. The selector preserves its original
dimensions, original matrix pointers and workspace pointer, as well as the upper caller bank,
regardless of the counting program's internal register usage. This is a syntactic register
frame; memory preservation additionally requires the concrete counter's memory contract.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.PrimeSelection

open Cslib.WordRAM

/-- The actual selector preserves the original parameters/pointers and the upper caller bank. -/
theorem preserves_input (counter : Code .standard 128) (i : Fin 160)
    (hi : (131 ≤ i.val ∧ i.val ≤ 136) ∨ 143 ≤ i.val) :
    (program counter).Preserves i := by
  have hc : (counter.rename counterRegisters).Preserves i :=
    counter.preserves_rename_of_forall_ne counterRegisters i (by
      intro j hj
      have hv := congrArg (fun i : Fin 160 => i.val) hj
      dsimp only [counterRegisters] at hv
      omega)
  have ht : (PrimeTrial.program.rename trialRegisters).Preserves i :=
    PrimeTrial.program.preserves_rename_of_forall_ne trialRegisters i (by
      intro j hj
      have hv := congrArg (fun i : Fin 160 => i.val) hj
      dsimp only [trialRegisters] at hv
      omega)
  simp only [program, body, candidate, trial, count, keep, nop, Code.Preserves, hc, ht,
    Op.dest, Op.bin, ne_eq, Option.some.injEq, Reg.best, Reg.bestCount, Reg.found, Reg.cursor,
    Reg.square, Reg.fourSquare, Reg.one, Reg.zero, Reg.four, Reg.trialArg, Reg.countSide,
    Reg.countPrime, Reg.countAB, Reg.countBC, Reg.countAC, Reg.countScratch, Fin.ext_iff]
  norm_num
  omega

end Cslib.Algorithms.WordRAM.ExactTriangle.PrimeSelection
