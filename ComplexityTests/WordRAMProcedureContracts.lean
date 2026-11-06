/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

-- upstream: local-only (tests)

import Complexity.Computability.WordRAM.Call
import Complexity.Computability.WordRAM.CopySum

/-!
# Named copy postconditions across an ordinary register-bank call

The source values include dirty destination memory and a nonzero accumulator. The caller reads
only the named memory and total fields, while the outside-bank register keeps its original word.
-/

namespace ComplexityTests.WordRAMProcedureContracts

open Cslib.WordRAM

private def input : Data 9 :=
  ⟨![1, 10, 2, 99, 99, 99, 99, 5, 777], fun q =>
    if q = 1 then 3 else if q = 2 then 4 else 99⟩

private def bank : Fin 8 → Fin 9 := Fin.castLE (by decide)

example : ∃ y, ExecWithin 8 (ArrayCopySum.program.rename bank) input y 20 ∧
    y.regs (bank ArrayCopySum.Reg.total) = 12 ∧ y.mem 10 = 3 ∧ y.mem 11 = 4 ∧
    y.mem 12 = 99 ∧ y.regs 8 = 777 := by
  obtain ⟨y, hy, post, hframe⟩ := ExecWithin.rename_post (Fin.castLE_injective _)
    (ArrayCopySum.exec (w := 8) (input.comap bank) (by decide) (by decide) (by decide)
      (by decide) (by decide))
  have post := post.of_comap
  refine ⟨y, hy, ?_, ?_, ?_, ?_, ?_⟩
  · exact post.total.trans (by decide)
  · simpa +decide [input, bank, ArrayCopy.copyPrefix, Function.update_apply] using
      congrFun post.memory 10
  · simpa +decide [input, bank, ArrayCopy.copyPrefix, Function.update_apply] using
      congrFun post.memory 11
  · simpa +decide [input, bank, ArrayCopy.copyPrefix, Function.update_apply] using
      congrFun post.memory 12
  · exact hframe 8 (by decide)

end ComplexityTests.WordRAMProcedureContracts
