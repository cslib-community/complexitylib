/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct.FrontProgram

/-!
# Snapshot entry to the routed box product

The prefix computes parameters and the protected snapshot address from ordinary scalar headers.
The continuation starts after an actual physical gather has populated that snapshot. It retains
coordinate adaptation, raw-matrix doubling, routing, band/table kernels, occurrence reconstruction
and original-input restoration. No source load interprets a physical pointer as a virtual offset.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PointerInput

open Cslib.WordRAM

/-- Compute the original threshold and every layout parameter before native gathering. -/
@[expose] def setupLayout : Code .standard 160 :=
  .seq BoxProduct.loadThreshold (.seq QueriedProduct.parameters QueriedProduct.layout)

/-- Route gathered original occurrences and preserve their stable original indices. -/
@[expose] def routing : Code .standard 160 :=
  .seq QueriedProduct.prepareQueries
    (.seq (Wanted.program.rename QueriedProduct.bank) QueriedProduct.saveGroups)

/-- Prepare the original shared band encodings from the gathered snapshot. -/
@[expose] def front : Code .standard 160 :=
  .seq routing (.seq (QueriedProduct.prepareMatrices true)
    (BandPreparation.program.rename QueriedProduct.bank))

/-- The unchanged mathematical back end, including original-input and threshold restoration. -/
@[expose] def continuation : Code .standard 160 :=
  .seq front (.seq BoxProduct.prepareGeometry (.seq BoxProduct.evaluateTiles
    (.seq QueriedProduct.reconstruct BoxProduct.restoreInput)))

/-- Charge the ordinary runtime parameter and layout calculations. -/
@[expose] def prefixTime (L : ℕ) : ℕ :=
  BoxProduct.thresholdTime L +
    ((16 * L + 49) + ((6 * L + 16) * 2 ^ L + 16)) + 50

/-- Charge routing after the original snapshot has actually been gathered. -/
@[expose] def routingTime (L m N Q : ℕ) : ℕ :=
  (14 * Q + 10) + Wanted.timeBound L m N Q +
    (7 * Cslib.Algorithms.MatrixMultiplication.Schonhage.numBands L m N ^ 2 + 14 * Q + 37)

/-- Charge the original routing and raw-matrix adaptation and band preparation. -/
@[expose] def frontTime (L m N Q : ℕ) : ℕ :=
  routingTime L m N Q + (8 * (2 * (N * Cslib.Algorithms.MatrixMultiplication.Schonhage.D m)) + 10) +
    BandPreparation.timeBound L m N

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PointerInput
