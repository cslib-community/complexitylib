/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.BinaryDecrementFlag

/-! Decrement flags are work-tape data, leaving the real output empty. -/

namespace CslibFrontierTests.BinaryDecrementFlag

open Turing Turing.MultiTapeTM Cslib.BitString

/-- Borrowing through two zeros takes seven steps and reports success on the flag tape. -/
example {input : List Bool} (ip : Fin (input.length + 2)) :
    binaryDecrement.outputToTape.runFrom
      ⟨some binaryDecrement.q₀, ip,
        Fin.lastCases (tapeOfList []) (fun _ => tapeOfList [false, false, true]),
        fun _ => 0, []⟩ 7 =
      ⟨none, ip, Fin.lastCases (tapeOfList [false])
        (fun _ => tapeOfList [true, true, false]), Fin.lastCases 1 (fun _ => 0), []⟩ := by
  simpa [BinaryDecrement.zeros, lsbValue, decrement] using
    runFrom_binaryDecrement_outputToTape ip [false, false, true]

/-- The flag characterization is a Boolean equality, usable directly for rewriting. -/
example (w : List Bool) : (!w.contains true) = decide (lsbValue w = 0) :=
  BinaryDecrement.underflow_eq w

end CslibFrontierTests.BinaryDecrementFlag
