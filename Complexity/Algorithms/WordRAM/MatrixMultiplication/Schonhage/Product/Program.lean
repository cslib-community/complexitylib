/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Product.Layout

/-!
# Actual producer, tile-kernel and reconstruction code

## Main definitions

* `QueriedProduct.program`: fixed native composition, with signed or raw nonnegative matrices.
* `QueriedProduct.tileStep`: actual offset loads, catalogue pointers, epoch call and update.
* `QueriedProduct.reconstruct`: restore the original request order from actual stored indices.

All three existing 96-register callees use the low bank. The caller's 64 additional
registers (`QueriedProduct.Reg`) retain its scalar layout and counters without colliding with
finite `Schonhage` names. Copying, initial directory clearing,
header adaptation, raw-entry doubling, dispatch, reporting and restoration are real instructions.
Supporting code definitions are exposed for execution proofs; they are implementation APIs.
-/

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct

open Cslib.WordRAM

/-- Reuse each existing native program in the same low 96-register bank. -/
@[expose] public def bank (i : Fin 96) : Fin 160 := ⟨i.val, by omega⟩
/-- The unchanged copy routine uses the first seven low registers. -/
@[expose] public def copyBank (i : Fin 7) : Fin 160 := ⟨i.val, by omega⟩

namespace Reg

/-- Persistent caller depth. -/
public abbrev depth : Fin 160 := 96
/-- Original inner depth, determining the shared dimension `4^m`. -/
public abbrev inner : Fin 160 := 97
/-- Original outer matrix dimension. -/
public abbrev rows : Fin 160 := 98
/-- Number of original request occurrences, including duplicates. -/
public abbrev queryCount : Fin 160 := 99
/-- Computed shared dimension `4^m`. -/
public abbrev columns : Fin 160 := 100
/-- Number of masks visited by the actual subset-table scan. -/
public abbrev masks : Fin 160 := 101
/-- Number of cells in each padded band array. -/
public abbrev cells : Fin 160 := 102
/-- Number of leaf entries in each shared encoding. -/
public abbrev leaves : Fin 160 := 103
/-- Computed number of row bands, also used for column bands. -/
public abbrev bands : Fin 160 := 104
/-- Number of tile calls, the square of the band count. -/
public abbrev tiles : Fin 160 := 105
/-- Length of the complete original memory prefix, including word zero. -/
public abbrev inputSize : Fin 160 := 106
/-- Protected snapshot pointer used to restore the original input. -/
public abbrev snapshot : Fin 160 := 107
/-- Protected copy of the router's immutable prefix offsets. -/
public abbrev offsets : Fin 160 := 108
/-- Protected copy of the actual grouped query codes. -/
public abbrev codes : Fin 160 := 109
/-- Protected permutation from grouped positions to original occurrence indices. -/
public abbrev originals : Fin 160 := 110
/-- Base of the grouped answers written by tile calls. -/
public abbrev grouped : Fin 160 := 111
/-- Base of the reconstructed original-order answers, returned by halt. -/
public abbrev output : Fin 160 := 112
/-- Base of reusable pruned-kernel stack and cache space. -/
public abbrev scratch : Fin 160 := 113
/-- Base of the timestamp directory shared by all tiles. -/
public abbrev stamps : Fin 160 := 114
/-- One past the complete caller and kernel allocation. -/
public abbrev memoryLimit : Fin 160 := 115
/-- Returned kernel epoch propagated to the next tile. -/
public abbrev epoch : Fin 160 := 116
/-- Current tile, directory-entry or reporting-loop index. -/
public abbrev index : Fin 160 := 117
/-- First grouped position of the current tile's actual span. -/
public abbrev first : Fin 160 := 118
/-- One past the last grouped position of the current tile. -/
public abbrev stop : Fin 160 := 119
/-- Row band computed by division of the current tile key. -/
public abbrev rowBand : Fin 160 := 120
/-- Column band computed by remainder of the current tile key. -/
public abbrev colBand : Fin 160 := 121
/-- Actual shared left-encoding pointer for the current tile. -/
public abbrev leftPointer : Fin 160 := 122
/-- Actual shared right-encoding pointer for the current tile. -/
public abbrev rightPointer : Fin 160 := 123
/-- Actual grouped-query pointer passed to the kernel. -/
public abbrev queryPointer : Fin 160 := 124
/-- Current grouped-answer pointer passed to the kernel. -/
public abbrev answerPointer : Fin 160 := 125
/-- Source pointer supplied to a real native copy. -/
public abbrev source : Fin 160 := 126
/-- Destination pointer supplied to a real native copy. -/
public abbrev destination : Fin 160 := 127
/-- Number of words supplied to a real native copy. -/
public abbrev length : Fin 160 := 128
/-- Temporary address for scalar loads, stores and reporting. -/
public abbrev address : Fin 160 := 129
/-- Temporary loaded matrix value, answer or original-position index. -/
public abbrev value : Fin 160 := 130
/-- Persistent unsigned zero. -/
public abbrev zero : Fin 160 := 131
/-- Persistent loop-increment constant one. -/
public abbrev one : Fin 160 := 132
/-- Persistent multiplier two for raw-to-signed conversion. -/
public abbrev two : Fin 160 := 133
/-- Persistent constant four for header offsets and kernel stack sizing. -/
public abbrev four : Fin 160 := 134
/-- First original matrix-payload address, immediately after the four headers. -/
public abbrev five : Fin 160 := 135
/-- Persistent constant six used in the computed router allocation. -/
public abbrev six : Fin 160 := 136
/-- Total word count of both original matrix payloads. -/
public abbrev matrixWords : Fin 160 := 137
/-- Original coordinate-pair block address. -/
public abbrev queryOffset : Fin 160 := 138
/-- One past the actual router allocation. -/
public abbrev wantedEnd : Fin 160 := 139
/-- One past the shared-band producer allocation. -/
public abbrev bandEnd : Fin 160 := 140
/-- Temporary product used while computing separated buffer addresses. -/
public abbrev temporary : Fin 160 := 141
/-- Base of the producer's shared two-sided encoding catalogue. -/
public abbrev catalogue : Fin 160 := 145
/-- Persistent constant three used in the router allocation. -/
public abbrev three : Fin 160 := 146

end Reg

/-- Compute genuine band scalars before selecting a protected caller area. No memory writes. -/
@[expose] public def parameters : Code .standard 160 :=
  .seq (BandPreparation.header.rename bank) (BandPreparation.countCode.rename bank)

/-- Preserve the computed original parameters and calculate every caller buffer address. -/
@[expose] public def layout : Code .standard 160 :=
  let bLevels := bank BandPreparation.levels
  let bInner := bank BandPreparation.inner
  let bRows := bank BandPreparation.rows
  let bColumns := bank BandPreparation.columns
  let bMasks := bank BandPreparation.masks
  let bCells := bank BandPreparation.cells
  let bLeaves := bank BandPreparation.leaves
  let bBands := bank BandPreparation.bands
  let bCatalogue := bank BandPreparation.catalogue
  ram[
  Reg.depth ← bLevels; Reg.inner ← bInner; Reg.rows ← bRows;
  Reg.address ← #4; Reg.queryCount ← *Reg.address;
  Reg.columns ← bColumns; Reg.masks ← bMasks; Reg.cells ← bCells; Reg.leaves ← bLeaves;
  Reg.bands ← bBands; Reg.catalogue ← bCatalogue;
  Reg.zero ← #0; Reg.one ← #1; Reg.two ← #2; Reg.three ← #3; Reg.four ← #4; Reg.five ← #5;
  Reg.six ← #6;
  Reg.tiles ← Reg.bands * Reg.bands;
  Reg.matrixWords ← Reg.rows * Reg.columns; Reg.matrixWords ← Reg.matrixWords * Reg.two;
  Reg.queryOffset ← Reg.matrixWords + Reg.five;
  Reg.inputSize ← Reg.queryCount * Reg.two; Reg.inputSize ← Reg.inputSize + Reg.queryOffset;
  Reg.bandEnd ← Reg.bands * Reg.leaves; Reg.bandEnd ← Reg.bandEnd * Reg.two;
  Reg.bandEnd ← Reg.bandEnd + Reg.catalogue;
  Reg.wantedEnd ← Reg.queryCount * Reg.four; Reg.wantedEnd ← Reg.wantedEnd + Reg.six;
  Reg.temporary ← Reg.masks * Reg.two; Reg.wantedEnd ← Reg.wantedEnd + Reg.temporary;
  Reg.temporary ← Reg.tiles * Reg.three; Reg.wantedEnd ← Reg.wantedEnd + Reg.temporary;
  Reg.snapshot ← Reg.bandEnd + Reg.wantedEnd; Reg.snapshot ← Reg.snapshot + Reg.inputSize;
  Reg.offsets ← Reg.snapshot + Reg.inputSize;
  Reg.codes ← Reg.offsets + Reg.tiles; Reg.codes ← Reg.codes + Reg.one;
  Reg.originals ← Reg.codes + Reg.queryCount; Reg.grouped ← Reg.originals + Reg.queryCount;
  Reg.output ← Reg.grouped + Reg.queryCount; Reg.scratch ← Reg.output + Reg.queryCount;
  Reg.temporary ← Reg.depth + Reg.one; Reg.temporary ← Reg.temporary * Reg.four;
  Reg.stamps ← Reg.scratch + Reg.temporary;
  Reg.temporary ← Reg.depth + Reg.one; Reg.temporary ← Reg.temporary * Reg.leaves;
  Reg.temporary ← Reg.temporary * Reg.two; Reg.stamps ← Reg.stamps + Reg.temporary;
  Reg.memoryLimit ← Reg.stamps + Reg.leaves ]

/-- Real argument setup followed by the unchanged dynamic-length native copy. -/
@[expose] public def copyCall : Code .standard 160 :=
  let copySrc : Fin 160 := 0
  let copyDst : Fin 160 := 1
  let copyLen : Fin 160 := 2
  ram[
  copySrc ← Reg.source; copyDst ← Reg.destination; copyLen ← Reg.length;
  ⟪ArrayCopy.program.rename copyBank⟫ ]

/-- Save the entire ordinary input, including its length word and coordinate list. -/
@[expose] public def saveInput : Code .standard 160 :=
  .seq (ram[ Reg.source ← Reg.zero; Reg.destination ← Reg.snapshot; Reg.length ← Reg.inputSize ])
    copyCall

/-- Put the original raw coordinate pairs in the actual Wanted input convention. -/
@[expose] public def prepareQueries : Code .standard 160 :=
  .seq (ram[ Reg.source ← Reg.snapshot + Reg.queryOffset; Reg.destination ← Reg.five;
    Reg.length ← Reg.queryCount * Reg.two ]) copyCall

/-- Save every computed tile offset, including the terminal offset. -/
@[expose] public def saveOffsets : Code .standard 160 :=
  let wOffsets := bank Wanted.offsets
  .seq (ram[ Reg.source ← wOffsets; Reg.destination ← Reg.offsets;
    Reg.length ← Reg.tiles + Reg.one ]) copyCall

/-- Save the actual grouped query codes. -/
@[expose] public def saveCodes : Code .standard 160 :=
  let wCodes := bank Wanted.codes
  .seq (ram[ Reg.source ← wCodes; Reg.destination ← Reg.codes; Reg.length ← Reg.queryCount ])
    copyCall

/-- Save the actual original-position permutation. -/
@[expose] public def saveOriginals : Code .standard 160 :=
  let wOriginals := bank Wanted.originals
  .seq (ram[ Reg.source ← wOriginals; Reg.destination ← Reg.originals;
    Reg.length ← Reg.queryCount ]) copyCall

/-- Preserve the computed arrays before the band producer reuses the low work area. -/
@[expose] public def saveGroups : Code .standard 160 :=
  .seq saveOffsets (.seq saveCodes saveOriginals)

/-- One actual load, unsigned doubling and store converts a raw 0/1 matrix entry. -/
@[expose] public def bitCopyStep : Code .standard 160 := ram[
  Reg.address ← Reg.source + Reg.index; Reg.value ← *Reg.address; Reg.value ← Reg.value * Reg.two;
  Reg.address ← Reg.four + Reg.index; *Reg.address ← Reg.value; Reg.index ← Reg.index + Reg.one ]

/-- Copy real matrix words into the band producer's adjacent front input blocks.
The bit-input variant executes the conversion instruction at every entry. -/
@[expose] public def prepareMatrices (bits : Bool) : Code .standard 160 :=
  if bits then
    .seq (ram[ Reg.source ← Reg.snapshot + Reg.five; Reg.index ← #0 ])
      (.loop (.lt Reg.index Reg.matrixWords) bitCopyStep)
  else
    .seq (ram[ Reg.source ← Reg.snapshot + Reg.five; Reg.destination ← Reg.four;
      Reg.length ← Reg.matrixWords ]) copyCall

/-- Initialize the one timestamp directory by actual stores, once for the entire product. -/
@[expose] public def initializeDirectory : Code .standard 160 := ram[
  Reg.index ← #0;
  while Reg.index < Reg.leaves do [
    Reg.address ← Reg.stamps + Reg.index; *Reg.address ← Reg.zero;
    Reg.index ← Reg.index + Reg.one ];
  Reg.epoch ← #0; Reg.index ← #0 ]

/-- Load actual group endpoints and compute both shared catalogue pointers and kernel ABI. -/
@[expose] public def tileArguments : Code .standard 160 :=
  let kDepth := bank PrunedQuery.inputDepth
  let kLeft := bank PrunedQuery.arrayA
  let kRight := bank PrunedQuery.arrayB
  let kQueries := bank PrunedQuery.queries
  let kCount := bank PrunedQuery.queryCount
  let kOutput := bank PrunedQuery.output
  let kScratch := bank PrunedQuery.scratch
  let kEpoch := bank PrunedQuery.epoch
  ram[
  Reg.address ← Reg.offsets + Reg.index; Reg.first ← *Reg.address;
  Reg.address ← Reg.address + Reg.one; Reg.stop ← *Reg.address;
  Reg.rowBand ← Reg.index / Reg.bands; Reg.colBand ← Reg.index % Reg.bands;
  Reg.leftPointer ← Reg.rowBand * Reg.leaves; Reg.leftPointer ← Reg.leftPointer + Reg.catalogue;
  Reg.rightPointer ← Reg.colBand + Reg.bands; Reg.rightPointer ← Reg.rightPointer * Reg.leaves;
  Reg.rightPointer ← Reg.rightPointer + Reg.catalogue;
  Reg.queryPointer ← Reg.codes + Reg.first; Reg.answerPointer ← Reg.grouped + Reg.first;
  kDepth ← Reg.depth; kLeft ← Reg.leftPointer; kRight ← Reg.rightPointer;
  kQueries ← Reg.queryPointer; kCount ← Reg.stop - Reg.first; kOutput ← Reg.answerPointer;
  kScratch ← Reg.scratch; kEpoch ← Reg.epoch ]

/-- One real pruned-kernel call, with the returned epoch propagated to the next tile. -/
@[expose] public def tileStep : Code .standard 160 :=
  let kEpoch := bank PrunedQuery.epoch
  .seq tileArguments (.seq (PrunedQuery.kernel.rename bank)
    (ram[ Reg.epoch ← kEpoch; Reg.index ← Reg.index + Reg.one ]))

/-- Compute all tiles from the actual group arrays; the zero-tile case never divides by zero. -/
@[expose] public def evaluateTiles : Code .standard 160 :=
  .loop (.lt Reg.index Reg.tiles) tileStep

/-- Read one actual original index and scatter its computed answer into request order. -/
@[expose] public def reconstructStep : Code .standard 160 := ram[
  Reg.address ← Reg.originals + Reg.index; Reg.temporary ← *Reg.address;
  Reg.address ← Reg.grouped + Reg.index; Reg.value ← *Reg.address;
  Reg.address ← Reg.output + Reg.temporary; *Reg.address ← Reg.value;
  Reg.index ← Reg.index + Reg.one ]

/-- Every original occurrence is reconstructed by charged native reads and stores. -/
@[expose] public def reconstruct : Code .standard 160 := ram[
  Reg.index ← #0; while Reg.index < Reg.queryCount do [ ⟪reconstructStep⟫ ] ]

/-- Restore the complete actual input after all private low-memory reuse has finished. -/
@[expose] public def restoreInput : Code .standard 160 :=
  .seq (ram[ Reg.source ← Reg.snapshot; Reg.destination ← Reg.zero; Reg.length ← Reg.inputSize ])
    copyCall

/-- Complete actual routing preparation and protected preservation of the original input. -/
@[expose] public def prepareRouting : Code .standard 160 :=
  .seq parameters (.seq layout (.seq saveInput (.seq prepareQueries
    (.seq (Wanted.program.rename bank) saveGroups))))

/-- The complete fixed producer/consumer program. `bits=false` takes canonical signed matrix
words; `bits=true` takes raw unsigned 0/1 words and performs actual per-entry doubling. -/
@[expose] public def program (bits : Bool) : Code .standard 160 :=
  .seq prepareRouting (.seq (prepareMatrices bits)
    (.seq (BandPreparation.program.rename bank) (.seq initializeDirectory
      (.seq evaluateTiles (.seq reconstruct restoreInput)))))

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct
