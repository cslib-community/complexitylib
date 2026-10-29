/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Product.Parameters

/-!
# Persistent queried-product caller scalars

## Main definitions

* `QueriedProduct.Parameters`: ordinary equalities describing computed high-register values.

## Main results

* `QueriedProduct.Parameters.reframe`: preserve the scalar protocol through actual low-bank calls.

The record contains no execution, cost, layout-validity or intermediate-state-fit assertion.
-/

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Persistent high-register contents after the native layout calculation. -/
public structure Parameters (L m N Q : ℕ) (x : Data 160) : Prop where
  /-- Original depth. -/
  depth : x.regs depth = L
  /-- Original inner depth. -/
  inner : x.regs inner = m
  /-- Original outer matrix dimension. -/
  rows : x.regs rows = N
  /-- Original request count, including repetitions. -/
  queryCount : x.regs queryCount = Q
  /-- Original thin dimension. -/
  columns : x.regs columns = D m
  /-- Complete subset-scan size. -/
  masks : x.regs masks = 2 ^ L
  /-- Original band-array size. -/
  cells : x.regs cells = 7 ^ L
  /-- Shared encoding-array size. -/
  leaves : x.regs leaves = 10 ^ L
  /-- Computed number of shared bands. -/
  bands : x.regs bands = numBands L m N
  /-- Computed number of tile calls. -/
  tiles : x.regs tiles = numBands L m N ^ 2
  /-- Complete original prefix size. -/
  inputSize : x.regs inputSize = inputEnd m N Q
  /-- Protected source snapshot. -/
  snapshot : x.regs snapshot = snapshotBase L m N Q
  /-- Saved actual offsets. -/
  offsets : x.regs offsets = offsetBase L m N Q
  /-- Saved actual query codes. -/
  codes : x.regs codes = codeBase L m N Q
  /-- Saved original-position permutation. -/
  originals : x.regs originals = originalBase L m N Q
  /-- Grouped-answer block. -/
  grouped : x.regs grouped = groupedBase L m N Q
  /-- Original-order answer block. -/
  output : x.regs output = outputBase L m N Q
  /-- Reusable native kernel scratch. -/
  scratch : x.regs scratch = scratchBase L m N Q
  /-- Shared timestamp directory. -/
  stamps : x.regs stamps = stampBase L m N Q
  /-- One past the complete allocation. -/
  memoryLimit : x.regs memoryLimit = memoryEnd L m N Q
  /-- Constant zero. -/
  zero : x.regs zero = 0
  /-- Constant one. -/
  one : x.regs one = 1
  /-- Unsigned multiplier for signed encoding. -/
  two : x.regs two = 2
  /-- Constant three. -/
  three : x.regs three = 3
  /-- Constant four. -/
  four : x.regs four = 4
  /-- Original matrix payload offset. -/
  five : x.regs five = 5
  /-- Constant six. -/
  six : x.regs six = 6
  /-- Both original matrix payloads. -/
  matrixWords : x.regs matrixWords = 2 * (N * D m)
  /-- Original coordinate-pair offset. -/
  queryOffset : x.regs queryOffset = queryInputBase m N
  /-- Low routing allocation end. -/
  wantedEnd : x.regs wantedEnd = Wanted.memoryLimit L m N Q
  /-- Low producer allocation end. -/
  bandEnd : x.regs bandEnd = BandPreparation.memoryEnd L m N
  /-- Computed low shared catalogue base. -/
  catalogue : x.regs catalogue = BandPreparation.catalogueBase L m N

/-- Registers holding the persistent caller protocol. -/
@[expose] public def parameterRegisters : Finset (Fin 160) :=
  {depth, inner, rows, queryCount, columns, masks, cells, leaves, bands, tiles, inputSize,
    snapshot, offsets, codes, originals, grouped, output, scratch, stamps, memoryLimit, zero, one,
    two, three, four, five, six, matrixWords, queryOffset, wantedEnd, bandEnd, catalogue}

/-- Preserve the protocol through operations on any of the other caller work registers. -/
public theorem Parameters.of_frame {L m N Q : ℕ} {x y : Data 160}
    (hx : Parameters L m N Q x) (h : ∀ i ∈ parameterRegisters, y.regs i = x.regs i) :
    Parameters L m N Q y := by
  constructor
  · exact (h _ (by decide)).trans hx.depth
  · exact (h _ (by decide)).trans hx.inner
  · exact (h _ (by decide)).trans hx.rows
  · exact (h _ (by decide)).trans hx.queryCount
  · exact (h _ (by decide)).trans hx.columns
  · exact (h _ (by decide)).trans hx.masks
  · exact (h _ (by decide)).trans hx.cells
  · exact (h _ (by decide)).trans hx.leaves
  · exact (h _ (by decide)).trans hx.bands
  · exact (h _ (by decide)).trans hx.tiles
  · exact (h _ (by decide)).trans hx.inputSize
  · exact (h _ (by decide)).trans hx.snapshot
  · exact (h _ (by decide)).trans hx.offsets
  · exact (h _ (by decide)).trans hx.codes
  · exact (h _ (by decide)).trans hx.originals
  · exact (h _ (by decide)).trans hx.grouped
  · exact (h _ (by decide)).trans hx.output
  · exact (h _ (by decide)).trans hx.scratch
  · exact (h _ (by decide)).trans hx.stamps
  · exact (h _ (by decide)).trans hx.memoryLimit
  · exact (h _ (by decide)).trans hx.zero
  · exact (h _ (by decide)).trans hx.one
  · exact (h _ (by decide)).trans hx.two
  · exact (h _ (by decide)).trans hx.three
  · exact (h _ (by decide)).trans hx.four
  · exact (h _ (by decide)).trans hx.five
  · exact (h _ (by decide)).trans hx.six
  · exact (h _ (by decide)).trans hx.matrixWords
  · exact (h _ (by decide)).trans hx.queryOffset
  · exact (h _ (by decide)).trans hx.wantedEnd
  · exact (h _ (by decide)).trans hx.bandEnd
  · exact (h _ (by decide)).trans hx.catalogue

set_option maxRecDepth 2048 in
-- Simplifying the fixed 32-member register set unfolds its finite membership expressions.
/-- Existing native callees operate below register 96, leaving this caller protocol intact. -/
public theorem Parameters.reframe {L m N Q : ℕ} {x y : Data 160}
    (hx : Parameters L m N Q x) (h : ∀ i, 96 ≤ i.val → y.regs i = x.regs i) :
    Parameters L m N Q y := hx.of_frame (by
  intro i hi
  have hs : ∀ i ∈ parameterRegisters, 96 ≤ i.val := by decide
  exact h i (hs i hi))

/-- Assigning a working register does not change any persistent parameter. -/
public theorem Parameters.set_work {L m N Q : ℕ} {x : Data 160}
    (hx : Parameters L m N Q x) (i : Fin 160) (hi : i ∉ parameterRegisters) (v : ℕ) :
    Parameters L m N Q (x.set i v) := hx.of_frame (by
  intro j hj
  have hji : j ≠ i := fun heq => hi (heq ▸ hj)
  simp only [Data.set_regs, Function.update_of_ne hji])

/-- Memory writes preserve the scalar protocol. -/
public theorem Parameters.write {L m N Q : ℕ} {x : Data 160}
    (hx : Parameters L m N Q x) (a v : ℕ) : Parameters L m N Q (x.write a v) :=
  hx.of_frame (by intro i _; rfl)

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct
