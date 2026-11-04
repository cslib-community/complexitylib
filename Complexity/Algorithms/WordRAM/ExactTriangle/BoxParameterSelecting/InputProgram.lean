/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.BoxParameterSelecting.Program
public import Complexity.Algorithms.WordRAM.ExactTriangle.ParameterSelecting.InputProgram

/-!
# Initialized input delivery for the automatic box solver

The existing fifteen-instruction original dimension/magnitude/matrix-pointer header precedes
the actual retuned solver. Input is the original two-scalar canonical signed matrix encoding;
no geometry, selected prime or time certificate is an input word.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.BoxParameterSelecting

open Cslib.WordRAM ParameterSelecting

/-- Actual original-input header followed by the complete automatic box solver. -/
@[expose] def entryProgram : Code .standard 640 := .seq entryHeader program

end Cslib.Algorithms.WordRAM.ExactTriangle.BoxParameterSelecting
