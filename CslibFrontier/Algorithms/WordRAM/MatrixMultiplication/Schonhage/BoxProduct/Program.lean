/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct.Layout
public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Product.Arguments

/-!
# One-geometry native box-product controller

The existing producer and router keep their 160-register caller protocol. Six unused
high registers retain the ordinary threshold and actual box geometry between tile calls.
Every tile reloads the low box bank, constructs its retained values, executes all wanted
queries, and copies temporary answers into the protected grouped buffer.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct

open Cslib.WordRAM

/-- Reuse the unchanged fixed box kernels in the caller's low register bank. -/
@[expose] def boxBank (i : Fin 64) : Fin 160 := ⟨i.val, by omega⟩

theorem boxBank_injective : Function.Injective boxBank := by
  intro i j h
  exact Fin.ext (congrArg (fun i : Fin 160 => i.val) h)

namespace Reg

/-- Ordinary original threshold, retained before low-memory producer reuse. -/
abbrev threshold : Fin 160 := 147
/-- Actual shared box-directory base. -/
abbrev directory : Fin 160 := 148
/-- Actual compact descriptor base. -/
abbrev records : Fin 160 := 149
/-- Actual reusable signed value-table base. -/
abbrev values : Fin 160 := 150
/-- Actual computed compact box count. -/
abbrev count : Fin 160 := 151
/-- Actual reusable temporary-answer base, above the work stack. -/
abbrev results : Fin 160 := 152

end Reg

/-- Supply original scalars to the actual geometry constructor. -/
@[expose] def geometryHead : Code .standard 160 :=
  let L := boxBank BoxTable.Reg.levels
  let m := boxBank BoxTable.Reg.inner
  let t := boxBank BoxTable.Reg.threshold
  let D := boxBank BoxTable.Reg.directory
  ram[ Reg.directory ← QueriedProduct.Reg.memoryLimit;
    L ← QueriedProduct.Reg.depth; m ← QueriedProduct.Reg.inner;
    t ← Reg.threshold; D ← Reg.directory ]

/-- Retain the computed geometry and initialize the actual tile index and temporary answers. -/
@[expose] def geometryFinish : Code .standard 160 :=
  let R := boxBank BoxTable.Reg.records
  let V := boxBank BoxTable.Reg.values
  let K := boxBank BoxTable.Reg.count
  ram[ Reg.records ← R; Reg.values ← V; Reg.count ← K;
    Reg.results ← QueriedProduct.Reg.depth + QueriedProduct.Reg.one;
    Reg.results ← Reg.results * QueriedProduct.Reg.leaves;
    QueriedProduct.Reg.temporary ← #10;
    Reg.results ← Reg.results + QueriedProduct.Reg.temporary;
    QueriedProduct.Reg.temporary ← #5;
    Reg.results ← Reg.results * QueriedProduct.Reg.temporary;
    Reg.results ← Reg.results + Reg.values; Reg.results ← Reg.results + Reg.count;
    QueriedProduct.Reg.index ← #0 ]

/-- Construct the real geometry once, before the entire tile loop. -/
@[expose] def prepareGeometry : Code .standard 160 :=
  .seq geometryHead (.seq (BoxTable.geometry.rename boxBank) geometryFinish)

/-- Restore every low scalar read by the retained-value constructor after ordinary span setup. -/
@[expose] def restoreBoxArguments : Code .standard 160 :=
  let L := boxBank BoxTable.Reg.levels
  let m := boxBank BoxTable.Reg.inner
  let t := boxBank BoxTable.Reg.threshold
  let H := boxBank BoxTable.Reg.height
  let T := boxBank BoxTable.Reg.span
  let D := boxBank BoxTable.Reg.directory
  let R := boxBank BoxTable.Reg.records
  let V := boxBank BoxTable.Reg.values
  let K := boxBank BoxTable.Reg.count
  let A := boxBank BoxTable.Reg.arrayA
  let B := boxBank BoxTable.Reg.arrayB
  let S := boxBank BoxTable.Reg.slots
  let oldA := QueriedProduct.bank PrunedQuery.arrayA
  let oldB := QueriedProduct.bank PrunedQuery.arrayB
  ram[ ⟪BoxTable.constants.rename boxBank⟫; A ← oldA; B ← oldB;
    L ← QueriedProduct.Reg.depth; m ← QueriedProduct.Reg.inner; t ← Reg.threshold;
    H ← m - t; T ← QueriedProduct.Reg.leaves; D ← Reg.directory;
    R ← Reg.records; V ← Reg.values; K ← Reg.count;
    S ← H + QueriedProduct.Reg.one; S ← S * T ]

/-- Save the computed low ABI before its registers are reused by the box constructor. -/
@[expose] def batchArguments : Code .standard 160 :=
  let next := boxBank BoxBatch.Reg.next
  let stop := boxBank BoxBatch.Reg.stop
  let output := boxBank BoxBatch.Reg.output
  let queries := QueriedProduct.bank PrunedQuery.queries
  let count := QueriedProduct.bank PrunedQuery.queryCount
  let answers := QueriedProduct.bank PrunedQuery.output
  ram[ next ← queries; stop ← queries + count; output ← Reg.results;
    QueriedProduct.Reg.destination ← answers; QueriedProduct.Reg.length ← count ]

/-- Reuse actual span/pointer arithmetic, retain the real cursors and fully restore the box ABI. -/
@[expose] def tileArguments : Code .standard 160 :=
  .seq QueriedProduct.tileArguments (.seq batchArguments restoreBoxArguments)

/-- Actual temporary-result copy, retaining the original protected grouped-answer layout. -/
@[expose] def copyResults : Code .standard 160 :=
  .seq (ram[ QueriedProduct.Reg.source ← Reg.results ]) QueriedProduct.copyCall

/-- One native retained table, all sparse queries in its real span, and actual answer delivery. -/
@[expose] def tileStep : Code .standard 160 :=
  .seq tileArguments (.seq (BoxTable.tile.rename boxBank)
    (.seq (BoxBatch.queryProgram.rename boxBank)
      (.seq copyResults (ram[
        QueriedProduct.Reg.index ← QueriedProduct.Reg.index + QueriedProduct.Reg.one ]))))

/-- All tiles use the same compact geometry and reusable value/query/result allocation. -/
@[expose] def evaluateTiles : Code .standard 160 :=
  .loop (.lt QueriedProduct.Reg.index QueriedProduct.Reg.tiles) tileStep

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct
