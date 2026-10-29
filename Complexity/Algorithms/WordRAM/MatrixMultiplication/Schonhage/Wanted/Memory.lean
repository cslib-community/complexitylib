/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted.Route
public import Complexity.Algorithms.Sorting.Counting

/-!
# Concrete memory layout of native wanted-query grouping

## Main definitions

* `Wanted.tableAddress`: computed selected-mask table after the readonly query input.
* `Wanted.Parameters`: scalar register equalities used by all three grouping passes.
* `Wanted.wordBudget`: an original-input-derived sufficient bound for unsigned words.

All layout definitions are numeric specifications of actual address instructions. Neither
the layout nor the parameter record contains a run, time bound or assumed solver.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- The original length word, four headers and two words per wanted position. -/
def inputLimit (Q : ℕ) : ℕ := Q * 2 + 5

/-- The forward table follows a complete `2^L`-word inverse table. -/
def tableAddress (L Q : ℕ) : ℕ := inputLimit Q + 2 ^ L

/-- Tile counts follow both computed tables. -/
def countAddress (L Q : ℕ) : ℕ := tableAddress L Q + 2 ^ L

/-- One immutable prefix offset per tile, followed by one terminal offset. -/
def offsetAddress (L m N Q : ℕ) : ℕ := countAddress L Q + numBands L m N ^ 2

/-- Mutable stable-scatter cursors follow the immutable prefix offsets. -/
def cursorAddressBase (L m N Q : ℕ) : ℕ := offsetAddress L m N Q + numBands L m N ^ 2 + 1

/-- One actual query code per original occurrence. -/
def codeAddress (L m N Q : ℕ) : ℕ := cursorAddressBase L m N Q + numBands L m N ^ 2

/-- Every code retains its original input position in the adjacent array. -/
def originalAddress (L m N Q : ℕ) : ℕ := codeAddress L m N Q + Q

/-- One past both grouped output arrays. -/
def memoryLimit (L m N Q : ℕ) : ℕ := originalAddress L m N Q + Q

/-- This sufficient budget covers the reused parameter kernels as well as all routing
and grouping arithmetic. It depends only on the original four scalar parameters. -/
def wordBudget (L m N Q : ℕ) : ℕ :=
  256 * (BandPreparation.wordBudget L m N + routeBudget L m N (tableAddress L Q) +
    memoryLimit L m N Q + L + N + Q + numBands L m N ^ 2 + 10 ^ L + 2 ^ L + 16)

/-- Persistent scalar register values after actual table relocation and allocation. -/
structure Parameters (L m N Q : ℕ) (x : Data 96) : Prop where
  /-- The reused table kernel's actual scalar contents. -/
  tables : BandPreparation.TableParameters L m (inputLimit Q) (tableAddress L Q) x
  /-- The one-query router's actual scalar contents. -/
  route : RouteParameters L m N (tableAddress L Q) x
  /-- Original query input starts after its four scalar headers. -/
  queries : x.regs queries = 5
  /-- Number of positions, retaining repetitions. -/
  queryCount : x.regs queryCount = Q
  /-- Allocated tile counts. -/
  counts : x.regs counts = countAddress L Q
  /-- Immutable prefix offsets. -/
  offsets : x.regs offsets = offsetAddress L m N Q
  /-- Mutable cursor addresses. -/
  cursors : x.regs cursors = cursorAddressBase L m N Q
  /-- Grouped query codes. -/
  codes : x.regs codes = codeAddress L m N Q
  /-- Original-position permutation. -/
  originals : x.regs originals = originalAddress L m N Q
  /-- Actual tile count. -/
  tileCount : x.regs tileCount = numBands L m N ^ 2
  /-- The entire readonly original prefix. -/
  inputEnd : x.regs inputEnd = inputLimit Q
  /-- One past the allocated arrays. -/
  memoryEnd : x.regs memoryEnd = memoryLimit L m N Q

/-- The exact scalar register footprint shared by the grouping passes. -/
def parameterRegisters : Finset (Fin 96) :=
  {queries, queryCount, counts, offsets, cursors, codes, originals, tileCount,
    bandWidth, inputEnd, memoryEnd, BandPreparation.levels, BandPreparation.inner,
    BandPreparation.outerSize, BandPreparation.masks, BandPreparation.inverse,
    BandPreparation.table, BandPreparation.root, BandPreparation.square,
    BandPreparation.bands, BandPreparation.zero, BandPreparation.one, BandPreparation.two}

/-- Persistent scalar contracts survive preservation of their concrete registers. -/
theorem Parameters.reframe {L m N Q : ℕ} {x y : Data 96} (hx : Parameters L m N Q x)
    (h : ∀ i ∈ parameterRegisters, y.regs i = x.regs i) : Parameters L m N Q y := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨(h _ (by decide)).trans hx.tables.levels,
      (h _ (by decide)).trans hx.tables.inner, (h _ (by decide)).trans hx.tables.masks,
      (h _ (by decide)).trans hx.tables.inverse, (h _ (by decide)).trans hx.tables.table,
      (h _ (by decide)).trans hx.tables.square, (h _ (by decide)).trans hx.tables.zero,
      (h _ (by decide)).trans hx.tables.one, (h _ (by decide)).trans hx.tables.two⟩
  · exact ⟨(h _ (by decide)).trans hx.route.levels,
      (h _ (by decide)).trans hx.route.outerSize, (h _ (by decide)).trans hx.route.root,
      (h _ (by decide)).trans hx.route.bandWidth, (h _ (by decide)).trans hx.route.bands,
      (h _ (by decide)).trans hx.route.table⟩
  all_goals first
    | exact (h _ (by decide)).trans hx.queries
    | exact (h _ (by decide)).trans hx.queryCount
    | exact (h _ (by decide)).trans hx.counts
    | exact (h _ (by decide)).trans hx.offsets
    | exact (h _ (by decide)).trans hx.cursors
    | exact (h _ (by decide)).trans hx.codes
    | exact (h _ (by decide)).trans hx.originals
    | exact (h _ (by decide)).trans hx.tileCount
    | exact (h _ (by decide)).trans hx.inputEnd
    | exact (h _ (by decide)).trans hx.memoryEnd

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted
