/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.PreprocessingProgram

/-! # Executed initialized-input Chan–He preprocessing -/

namespace ComplexityTests.NativeChanHePreprocessing

open Cslib.WordRAM
open Cslib.Algorithms.WordRAM.ThreeSum.ChanHe

-- This successful physical width is smaller than the exported frontend sufficient width.
-- All parameters, the prime bitmap, reservations, descriptor loads and root skips execute.
-- The empty frontend still has twenty roots, rather than bypassing the algorithm.
/-- info: true -/
#guard_msgs in
#eval decide ((Code.eval 32 256 (Preprocessing.program 0) (Data.init [])).map (fun yn =>
  [yn.1.regs Traversal.outputCount, yn.1.regs Preprocessing.packedLength,
    yn.1.regs Preprocessing.candidateLimit, yn.1.regs Traversal.primeCount,
    yn.1.regs Preprocessing.current, yn.1.regs Preprocessing.power,
    yn.1.regs Preprocessing.outputCapacity, yn.1.regs Preprocessing.heapFloor,
    yn.1.regs Traversal.heap, yn.1.mem 0]) =
    some [0, 294912, 192, 43, 20, 9, 180, 575, 575, 0])

-- The complete native program faults during actual parameter arithmetic at an invalid width.
/-- info: true -/
#guard_msgs in
#eval (Code.eval 1 256 (Preprocessing.program 0) (Data.init [])).isNone

end ComplexityTests.NativeChanHePreprocessing
