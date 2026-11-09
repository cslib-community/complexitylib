/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct.FrontProgram

/-!
# Scalar and layout prefix before physical snapshot gathering

`setupLayout` computes parameters, threshold and protected snapshot address from ordinary
scalar headers. After the charged physical gather, callers use `BoxProduct.programFromSnapshot`
for the shared continuation, including raw-matrix doubling and original-input restoration.
No source load interprets a physical pointer as a virtual offset.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PointerInput

open Cslib.WordRAM

/-- Compute the original threshold and every layout parameter before native gathering. -/
@[expose] def setupLayout : Code .standard 160 :=
  .seq BoxProduct.loadThreshold (.seq QueriedProduct.parameters QueriedProduct.layout)

/-- Charge the ordinary runtime parameter and layout calculations. -/
@[expose] def prefixTime (L : ℕ) : ℕ :=
  BoxProduct.thresholdTime L +
    ((16 * L + 49) + ((6 * L + 16) * 2 ^ L + 16)) + 50

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PointerInput
