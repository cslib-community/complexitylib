/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime
public import Complexity.Algorithms.WordRAM.ExactTriangle.BoxFixedPrime

/-!
# Caller-safe native box-backed fixed-prime solver

The actual existing original-array copy/sum, computed-modulus setup and raw return code
surround a real compilation of `BoxFixedPrime.program`. The 640-register ABI, protected
selector bank and eight original caller arguments are shared with `CallableFixedPrime`.
No whole-window clear or caller-supplied width, solver or execution certificate is introduced.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.CallableBoxFixedPrime

open Cslib.WordRAM CallableFixedPrime

/-- Actual address translation and dirty-load normalization of the complete box controller. -/
@[expose] def solve : Code .standard 640 :=
  (MemoryWindow.compile BoxFixedPrime.program).rename sourceBank

/-- All original copies, actual width computation, box solving and raw return instructions. -/
@[expose] def program : Code .standard 640 := .seq adapt (.seq setup (.seq solve receive))

end Cslib.Algorithms.WordRAM.ExactTriangle.CallableBoxFixedPrime
