/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted.PackProgram
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandTables
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandParameters

/-!
# Native routing and stable grouping of wanted positions

The initialized input contains only `L,m,N,Q` and `Q` ordinary row/column pairs. The code
computes the valid-mask tables, band parameters, tile counts, prefix offsets and scatter
positions. Each scatter writes the unchanged pruned-query code and its original position.
No sorted request list, layout certificate or dispatch decision is supplied as input.

## Main definitions

* `Wanted.routeCode`: compute one tile and one query code using the computed table.
* `Wanted.program`: computed tables followed by counting, prefix and stable scatter passes.

These programs use only the existing standard unsigned instructions. Correctness, width,
frame and resource theorems are separate from the definitions. Supporting `exec_*` lemmas
are internal implementation APIs exported across proof modules; consumers use `runs`,
`runs_grouped` or the generic-memory `exec_program` when composing a caller.

## References

The routing goal comes from [AlmanWilliams2026, Section 2.4.4] and Anthropic's pinned
[Wanted/Codes.lean](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Programs/Sec2/Theorem5/Wanted/Codes.lean) at revision
`16a5ce41304fcdaea4e0be7c132e1c361dc26da5`. This is original native code with its own charged
proofs, using the existing finite output-string definitions. It does not import the source
Light machine, its sorting procedure or its instruction counts.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Register embedding for the unchanged sixteen-register digit packer. -/
def packRegisters (i : Fin 16) : Fin 96 := ⟨i.val, by omega⟩

/-- Original row of the current query. -/
abbrev queryRow : Fin 96 := 16
/-- Original column of the current query. -/
abbrev queryCol : Fin 96 := 17
/-- Computed row band. -/
abbrev rowBand : Fin 96 := 18
/-- Computed column band. -/
abbrev colBand : Fin 96 := 19
/-- Row-major tile key. -/
abbrev tile : Fin 96 := 20
/-- Address of the first original row/column pair. -/
abbrev queries : Fin 96 := 21
/-- Number of original query positions, including duplicates. -/
abbrev queryCount : Fin 96 := 22
/-- Current original query position or tile position. -/
abbrev index : Fin 96 := 23
/-- Tile-count array base. -/
abbrev counts : Fin 96 := 24
/-- Prefix-offset array base, with one additional terminal cell. -/
abbrev offsets : Fin 96 := 25
/-- Current stable-scatter cursor array base. -/
abbrev cursors : Fin 96 := 26
/-- Grouped query-code array base. -/
abbrev codes : Fin 96 := 27
/-- Grouped original-position array base. -/
abbrev originals : Fin 96 := 28
/-- Current tile's query count. -/
abbrev count : Fin 96 := 29
/-- Running prefix sum. -/
abbrev total : Fin 96 := 30
/-- Number of tiles. -/
abbrev tileCount : Fin 96 := 31
/-- Number of original positions in one band. -/
abbrev bandWidth : Fin 96 := 85
/-- One past the readonly initialized query input. -/
abbrev inputEnd : Fin 96 := 86
/-- One past the grouping arrays. -/
abbrev memoryEnd : Fin 96 := 87
/-- Address scratch. -/
abbrev pointer : Fin 96 := 88
/-- Saved address of the current scatter cursor. -/
abbrev cursorAddress : Fin 96 := 89
/-- Current grouped output position. -/
abbrev position : Fin 96 := 90

/-- Compute just the row-major tile key. No memory is touched. -/
def tileCode : Code .standard 96 := ram[
  rowBand ← queryRow / bandWidth; colBand ← queryCol / bandWidth;
  tile ← rowBand * BandPreparation.bands; tile ← tile + colBand
]

/-- Compute the selected subset rank and load its actual mask from the computed table. -/
def routeHead : Code .standard 96 := ram[
  ⟪tileCode⟫;
  ⟪.op (.copy (packRegisters depth) BandPreparation.levels)⟫;
  ⟪.op (.bin .mod (packRegisters row) queryRow BandPreparation.outerSize)⟫;
  ⟪.op (.bin .mod (packRegisters col) queryCol BandPreparation.outerSize)⟫;
  ⟪.op (.bin .div (packRegisters mask) queryRow BandPreparation.outerSize)⟫;
  ⟪.op (.bin .mod (packRegisters mask) (packRegisters mask) BandPreparation.root)⟫;
  ⟪.op (.bin .mul (packRegisters mask) (packRegisters mask) BandPreparation.root)⟫;
  ⟪.op (.bin .div (packRegisters temporary) queryCol BandPreparation.outerSize)⟫;
  ⟪.op (.bin .mod (packRegisters temporary) (packRegisters temporary) BandPreparation.root)⟫;
  ⟪.op (.bin .add (packRegisters mask) (packRegisters mask) (packRegisters temporary))⟫;
  ⟪.op (.bin .add (packRegisters temporary) BandPreparation.table (packRegisters mask))⟫;
  ⟪.op (.load (packRegisters mask) (packRegisters temporary))⟫
]

/-- Compute a tile key and its output code, with actual digit decisions and table load. -/
def routeCode : Code .standard 96 := .seq routeHead (packCode.rename packRegisters)

/-- Relocate the computed tables and every grouping array after the initialized input. -/
def setup : Code .standard 96 := ram[
  pointer ← #4; queryCount ← *pointer; queries ← #5;
  inputEnd ← queryCount * BandPreparation.two; inputEnd ← inputEnd + queries;
  BandPreparation.inverse ← inputEnd;
  BandPreparation.table ← BandPreparation.inverse + BandPreparation.masks;
  counts ← BandPreparation.table + BandPreparation.masks;
  bandWidth ← BandPreparation.root * BandPreparation.outerSize;
  tileCount ← BandPreparation.bands * BandPreparation.bands;
  offsets ← counts + tileCount; cursors ← offsets + tileCount;
  cursors ← cursors + BandPreparation.one; codes ← cursors + tileCount;
  originals ← codes + queryCount; memoryEnd ← originals + queryCount
]

/-- Zero each tile count once. -/
def clearCounts : Code .standard 96 := ram[
  index ← #0;
  while index < tileCount do [
    pointer ← counts + index; *pointer ← BandPreparation.zero;
    index ← index + BandPreparation.one
  ]
]

/-- Load one original pair without changing its input words. -/
def loadQuery : Code .standard 96 := ram[
  pointer ← index * BandPreparation.two; pointer ← pointer + queries;
  queryRow ← *pointer; pointer ← pointer + BandPreparation.one; queryCol ← *pointer
]

/-- Count one input position in its actual tile, retaining duplicates. -/
def countStep : Code .standard 96 := ram[
  ⟪loadQuery⟫; ⟪tileCode⟫; pointer ← counts + tile; count ← *pointer;
  count ← count + BandPreparation.one; *pointer ← count;
  index ← index + BandPreparation.one
]

/-- Scan the original list once to obtain tile counts. -/
def countQueries : Code .standard 96 :=
  .seq (ram[index ← #0]) (.loop (.lt index queryCount) countStep)

/-- Store both the immutable prefix offset and the initial scatter cursor of one tile. -/
def prefixStep : Code .standard 96 := ram[
  pointer ← counts + index; count ← *pointer;
  pointer ← offsets + index; *pointer ← total;
  pointer ← cursors + index; *pointer ← total;
  total ← total + count; index ← index + BandPreparation.one
]

/-- Compute exact tile spans, including the terminal offset after the last tile. -/
def prefixCode : Code .standard 96 := ram[
  index ← #0; total ← #0;
  while index < tileCount do [ ⟪prefixStep⟫ ];
  pointer ← offsets + tileCount; *pointer ← total
]

/-- Append one code and original position to its tile, advancing the actual cursor. -/
def scatterWrite : Code .standard 96 := ram[
  cursorAddress ← cursors + tile; position ← *cursorAddress;
  pointer ← codes + position; ⟪.op (.store pointer (packRegisters code))⟫;
  pointer ← originals + position; *pointer ← index;
  position ← position + BandPreparation.one; *cursorAddress ← position;
  index ← index + BandPreparation.one
]

/-- Recompute one query's code and scatter it stably into its counted tile. -/
def scatterStep : Code .standard 96 :=
  .seq loadQuery (.seq routeCode scatterWrite)

/-- The second original-order scan retains every occurrence and its original position. -/
def scatter : Code .standard 96 :=
  .seq (ram[index ← #0]) (.loop (.lt index queryCount) scatterStep)

/-- Complete initialized native routing; no mathematical layout is an input word. -/
def program : Code .standard 96 :=
  .seq (.seq BandPreparation.header (.seq BandPreparation.countCode
    (.seq setup BandPreparation.tablesCode)))
    (.seq clearCounts (.seq countQueries (.seq prefixCode scatter)))

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted
