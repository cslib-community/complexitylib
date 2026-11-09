/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct.Program
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct.Input
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Product.Routing

/-!
# Original-input routing and shared band production for box products

A preliminary readonly parameter pass locates the appended threshold before the existing
router reuses low memory. The unchanged routing and band programs compute real tile spans,
wanted codes, a stable original-index permutation and shared canonical leaf encodings.
The extra parameter pass and threshold load are charged explicitly. `frontFromSnapshot` and
`programFromSnapshot` expose the actual shared suffixes after a charged snapshot copy or gather;
they include matrix adaptation, original-occurrence reconstruction and restoration.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct

open Cslib.WordRAM Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Locate the final original threshold word using computed matrix dimensions. -/
@[expose] def thresholdLoad : Code .standard 160 :=
  let rows := QueriedProduct.bank BandPreparation.rows
  let columns := QueriedProduct.bank BandPreparation.columns
  ram[
    QueriedProduct.Reg.address ← #4;
    QueriedProduct.Reg.queryCount ← *QueriedProduct.Reg.address;
    QueriedProduct.Reg.address ← rows * columns;
    QueriedProduct.Reg.address ← QueriedProduct.Reg.address + QueriedProduct.Reg.address;
    QueriedProduct.Reg.value ← QueriedProduct.Reg.queryCount + QueriedProduct.Reg.queryCount;
    QueriedProduct.Reg.address ← QueriedProduct.Reg.address + QueriedProduct.Reg.value;
    QueriedProduct.Reg.value ← #5;
    QueriedProduct.Reg.address ← QueriedProduct.Reg.address + QueriedProduct.Reg.value;
    Reg.threshold ← *QueriedProduct.Reg.address ]

/-- Read the ordinary threshold before either producer mutates the original payload. -/
@[expose] def loadThreshold : Code .standard 160 :=
  .seq QueriedProduct.parameters thresholdLoad

/-- Shared actual routing, matrix adaptation and bands from a populated snapshot. -/
@[expose] def frontFromSnapshot (bits : Bool) : Code .standard 160 :=
  .seq QueriedProduct.routingFromSnapshot (.seq (QueriedProduct.prepareMatrices bits)
    (BandPreparation.program.rename QueriedProduct.bank))

/-- Charge all actual routing, matrix adaptation and band construction after the snapshot. -/
@[expose] def snapshotFrontTime (L m N Q : ℕ) : ℕ :=
  QueriedProduct.routingFromSnapshotTime L m N Q + (8 * (2 * (N * D m)) + 10) +
    BandPreparation.timeBound L m N

/-- Actual original-coordinate routing and actual shared band encodings. -/
@[expose] def front (bits : Bool) : Code .standard 160 :=
  .seq loadThreshold (.seq QueriedProduct.prepareRouting
    (.seq (QueriedProduct.prepareMatrices bits)
      (BandPreparation.program.rename QueriedProduct.bank)))

/-- Restore the appended original threshold after the unchanged original-prefix restoration. -/
@[expose] def restoreThreshold : Code .standard 160 := ram[
  QueriedProduct.Reg.address ← QueriedProduct.Reg.inputSize;
  *QueriedProduct.Reg.address ← Reg.threshold ]

/-- Both original-prefix restoration and the additional original threshold store are charged. -/
@[expose] def restoreInput : Code .standard 160 :=
  .seq QueriedProduct.restoreInput restoreThreshold

/-- Complete fixed native product: real routing/encodings, one geometry construction,
all retained-table query batches, original-order reconstruction and input restoration. -/
@[expose] def program (bits : Bool) : Code .standard 160 :=
  .seq (front bits) (.seq prepareGeometry (.seq evaluateTiles
    (.seq QueriedProduct.reconstruct restoreInput)))

/-- Complete shared suffix, including exact occurrence reconstruction and restoration. -/
@[expose] def programFromSnapshot (bits : Bool) : Code .standard 160 :=
  .seq (frontFromSnapshot bits) (.seq prepareGeometry (.seq evaluateTiles
    (.seq QueriedProduct.reconstruct restoreInput)))

/-- Readonly preliminary parameter pass and the nine actual threshold-adapter instructions. -/
@[expose] def thresholdTime (L : ℕ) : ℕ :=
  ((16 * L + 49) + ((6 * L + 16) * 2 ^ L + 16)) + 9

/-- The charged original routing, actual matrix adaptation and shared encoding preparation. -/
@[expose] def frontTime (L m N Q : ℕ) : ℕ :=
  thresholdTime L + QueriedProduct.routingTimeBound L m N Q +
    (8 * (2 * (N * D m)) + 10) + BandPreparation.timeBound L m N

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct
