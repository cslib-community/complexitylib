/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

import CslibFrontier.Computability.PolyTime.CSP.Edge.Buffer

/-! The exact-width round trip is available from an ordinary shared buffer import alone. -/

namespace CslibFrontierTests.EdgeCSPSolverBuffer

open Cslib.Logic.PL Cslib.Logic.PL.CSP Cslib.Complexity.CSP

example {F : CSP Table ℕ} (bits : List Bool)
    (h : bits.length = (incidenceList F).length) :
    bits = (incidenceList F).map (EdgeAugmenting.labeling F bits) :=
  EdgeAugmenting.buffer_eq bits h

end CslibFrontierTests.EdgeCSPSolverBuffer
