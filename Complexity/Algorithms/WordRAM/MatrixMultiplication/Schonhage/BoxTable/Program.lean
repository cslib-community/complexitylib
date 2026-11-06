/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Power
public import Complexity.Computability.WordRAM.Signed.Arithmetic

/-!
# Native shared box geometry and compact value tables

The geometry stage assigns every slot of a shared `(m-t+1) * 10^L` directory,
including invalid slots. It emits only valid canonical boxes into a compact three-word
catalogue: completed leaf code, number of stars, and highest-star place value.
The catalogue is ordered by star count. Each tile writes one signed value per catalogue
entry, reading only values for smaller star counts. No scratch region must start zero.

Level zero is the least significant decimal digit, as in the existing native encodings;
the P0 digit is nine. The per-tile stage does not rebuild or clear the geometry.
This is an original representation alternative to the trie in [AlmanWilliams2026, Section 4.3].
Its one-time geometry charge and allocation must remain separate from per-tile work.
Definitions here are code only; execution and resource proofs belong to the stage modules.

## Main definitions

* `BoxTable.geometry`: compute the shared directory and compact catalogue.
* `BoxTable.tile`: compute the compact value table from two encoded leaf arrays.
* `BoxTable.lookup`: read a cube's actual stored value after checking its raw digit form.
* `BoxTable.program`: ordinary initialized-input constructor for one tile.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable

open Cslib.WordRAM

/-- A fixed bank containing the existing nine-register signed-arithmetic workspace. -/
abbrev registers : ℕ := 64

namespace Reg

/-- Original depth. -/
abbrev levels : Fin registers := 9
/-- Original inner-level count. -/
abbrev inner : Fin registers := 10
/-- Original order threshold. -/
abbrev threshold : Fin registers := 11
/-- Computed maximum combined P0/star count. -/
abbrev height : Fin registers := 12
/-- Computed encoding length, ten to the depth. -/
abbrev span : Fin registers := 13
/-- Shared directory base. -/
abbrev directory : Fin registers := 14
/-- Three-word catalogue base. -/
abbrev records : Fin registers := 15
/-- Compact signed value-table base. -/
abbrev values : Fin registers := 16
/-- Left canonical signed encoding-array base. -/
abbrev arrayA : Fin registers := 17
/-- Right canonical signed encoding-array base. -/
abbrev arrayB : Fin registers := 18
/-- Number of directory slots. -/
abbrev slots : Fin registers := 19
/-- Current directory slot. -/
abbrev slot : Fin registers := 20
/-- Number of emitted catalogue records. -/
abbrev count : Fin registers := 21
/-- Star count of the current record. -/
abbrev stars : Fin registers := 22
/-- Completed leaf code of the current record. -/
abbrev completion : Fin registers := 23
/-- Unprocessed decimal suffix. -/
abbrev suffix : Fin registers := 24
/-- Current level in a digit scan. -/
abbrev level : Fin registers := 25
/-- P0 population of the processed prefix. -/
abbrev population : Fin registers := 26
/-- Place value of the current level. -/
abbrev power : Fin registers := 27
/-- Place value of the highest star, or zero when there are no stars. -/
abbrev starPower : Fin registers := 28
/-- Raw digit temporary. -/
abbrev digit : Fin registers := 29
/-- Load/store address temporary. -/
abbrev address : Fin registers := 30
/-- Scalar arithmetic temporary. -/
abbrev temporary : Fin registers := 31
/-- Constant one. -/
abbrev one : Fin registers := 32
/-- Constant ten. -/
abbrev ten : Fin registers := 33
/-- Constant nine, the P0 digit. -/
abbrev nine : Fin registers := 34
/-- Constant three, the catalogue record width. -/
abbrev three : Fin registers := 35
/-- Current compact record index. -/
abbrev current : Fin registers := 36
/-- Canonical signed partial sum. -/
abbrev accumulator : Fin registers := 37
/-- Current replacement term, from zero through nine. -/
abbrev term : Fin registers := 38
/-- Completed leaf code after replacing the highest star. -/
abbrev childCode : Fin registers := 39
/-- Child's shared directory slot. -/
abbrev childSlot : Fin registers := 40
/-- Child's compact value-table index, initially stored with offset one. -/
abbrev childRank : Fin registers := 41
/-- Constant zero outside the signed workspace. -/
abbrev nil : Fin registers := 42
/-- Input pointer to a raw cube's digits for lookup. -/
abbrev cube : Fin registers := 43
/-- Lookup-invalid flag. -/
abbrev invalid : Fin registers := 44
/-- A fixed P0 term has already appeared below this level. -/
abbrev fixedSeen : Fin registers := 45
/-- Lookup-found flag. -/
abbrev found : Fin registers := 46
/-- Lookup's canonical signed returned value. -/
abbrev answer : Fin registers := 47

end Reg

open Reg

/-- Initialize every reused scalar constant explicitly. -/
@[expose] def constants : Code .standard registers := ram[
  nil ← #0; one ← #1; ten ← #10; nine ← #9; three ← #3 ]

/-- Reuse the existing power routine without introducing a second exponentiation loop. -/
@[expose] def powerRegisters : Fin 5 → Fin registers := ![span, level, ten, levels, one]

/-- Count a P0 digit and remember precisely the requested occurrence's place value. -/
@[expose] def countDigit : Code .standard registers := ram[
  digit ← suffix % ten; suffix ← suffix / ten;
  if digit = nine then [
    population ← population + one;
    if population = stars then [ starPower ← power ] else [ temporary ← temporary ]
  ] else [ temporary ← temporary ];
  power ← power * ten; level ← level + one ]

/-- Initialize a scan from the current raw directory slot. -/
@[expose] def inspectSetup : Code .standard registers := ram[
  stars ← slot / span; completion ← slot % span; suffix ← completion;
  level ← #0; population ← #0; power ← #1; starPower ← #0 ]

/-- Complete one actual digit scan; the loop is over the original depth. -/
@[expose] def inspect : Code .standard registers :=
  .seq inspectSetup (.loop (.lt level levels) countDigit)

/-- Write one compact record and its offset-one directory entry. -/
@[expose] def emit : Code .standard registers := ram[
  temporary ← count + one; *address ← temporary;
  address ← count * three; address ← records + address; *address ← completion;
  address ← address + one; *address ← stars;
  address ← address + one; *address ← starPower;
  count ← count + one ]

/-- Assign one directory slot and emit a compact record when both tests succeed. -/
@[expose] def writeSlot : Code .standard registers := ram[
  address ← directory + slot; *address ← nil;
  if height < population then [ temporary ← temporary ] else [
    if population < stars then [ temporary ← temporary ] else [ ⟪emit⟫ ] ];
  slot ← slot + one ]

/-- Every directory slot is assigned, including slots rejected by either population test. -/
@[expose] def catalogueStep : Code .standard registers := .seq inspect writeSlot

/-- Compute the slot range and initialize the actual compact count. -/
@[expose] def geometrySetup : Code .standard registers := ram[
  height ← inner - threshold; slots ← height + one; slots ← slots * span;
  records ← directory + slots; slot ← #0; count ← #0 ]

/-- Place the value table immediately after the actual compact records. -/
@[expose] def geometryFinish : Code .standard registers := ram[
  temporary ← count * three; values ← records + temporary ]

/-- Compute the shared geometry, returning its actual compact count and value-table base. -/
@[expose] def geometry : Code .standard registers :=
  .seq constants <| .seq (Power.program.rename powerRegisters) <|
    .seq geometrySetup <| .seq (.loop (.lt slot slots) catalogueStep) geometryFinish

/-- Load the three actual catalogue words. -/
@[expose] def loadRecord : Code .standard registers := ram[
  address ← current * three; address ← records + address; completion ← *address;
  address ← address + one; stars ← *address;
  address ← address + one; starPower ← *address ]

/-- Read both encoded leaf operands from their actual array positions. -/
@[expose] def leafLoad : Code .standard registers := ram[
  address ← arrayA + completion; Signed.left ← *address;
  address ← arrayB + completion; Signed.right ← *address ]

/-- Retain the actual signed arithmetic result outside its scratch bank. -/
@[expose] def leafFinish : Code .standard registers := ram[ accumulator ← Signed.result ]

/-- Multiply the two encoded words of a fully fixed cube. -/
@[expose] def leafProduct : Code .standard registers :=
  .seq leafLoad (.seq Signed.multiply leafFinish)

/-- Compute a child's directory index and load its already written signed value. -/
@[expose] def childLoad : Code .standard registers := ram[
  temporary ← nine - term; temporary ← temporary * starPower;
  childCode ← completion - temporary;
  childSlot ← stars - one; childSlot ← childSlot * span; childSlot ← childSlot + childCode;
  address ← directory + childSlot; childRank ← *address; childRank ← childRank - one;
  address ← values + childRank; Signed.right ← *address; Signed.left ← accumulator ]

/-- Save the signed partial sum and advance the actual ten-child loop. -/
@[expose] def childFinish : Code .standard registers := ram[
  accumulator ← Signed.result; term ← term + one ]

/-- Compute one child's actual directory index, read its stored value, and add it. -/
@[expose] def addChild : Code .standard registers :=
  .seq childLoad (.seq Signed.add childFinish)

/-- Reset the accumulator and term counter before the ten-child loop. -/
@[expose] def childrenStart : Code .standard registers := ram[
  accumulator ← #0; term ← #0 ]

/-- Accumulate all ten earlier child values. -/
@[expose] def children : Code .standard registers :=
  .seq childrenStart (.loop (.lt term ten) addChild)

/-- Evaluate a leaf product or the sum of its ten earlier children. -/
@[expose] def tileValue : Code .standard registers :=
  .branch (.eq stars nil) leafProduct children

/-- Store the completed signed value and advance its compact index. -/
@[expose] def tileStore : Code .standard registers := ram[
  address ← values + current; *address ← accumulator; current ← current + one ]

/-- Evaluate one compact box and store it before advancing the compact index. -/
@[expose] def tileStep : Code .standard registers :=
  .seq loadRecord (.seq tileValue tileStore)

/-- Initialize every per-tile scalar that is read before being written. -/
@[expose] def tileSetup : Code .standard registers := ram[ ⟪constants⟫; current ← #0 ]

/-- Fill exactly one compact value table, reusing the shared geometry. -/
@[expose] def tile : Code .standard registers :=
  .seq tileSetup (.loop (.lt current count) tileStep)

/-- Read one cube digit, rejecting out-of-alphabet and star-after-fixed-P0 forms. -/
@[expose] def lookupDigit : Code .standard registers := ram[
  address ← cube + level; digit ← *address;
  if ten < digit then [ invalid ← #1; digit ← #0 ] else [ temporary ← temporary ];
  if digit = ten then [
    if nil < fixedSeen then [ invalid ← #1 ] else [ temporary ← temporary ];
    stars ← stars + one; population ← population + one; digit ← nine
  ] else [
    if digit = nine then [ fixedSeen ← #1; population ← population + one ]
    else [ temporary ← temporary ] ];
  temporary ← digit * power; completion ← completion + temporary;
  power ← power * ten; level ← level + one ]

/-- Initialize the raw lookup prefix and both returned flags explicitly. -/
@[expose] def lookupSetup : Code .standard registers := ram[
  ⟪constants⟫; level ← #0; stars ← #0; population ← #0; fixedSeen ← #0;
  invalid ← #0; completion ← #0; power ← #1; found ← #0; answer ← #0 ]

/-- Validate the completed population and read the actual compact-table word. -/
@[expose] def lookupFinish : Code .standard registers := ram[
  if height < population then [ invalid ← #1 ] else [ temporary ← temporary ];
  if invalid = nil then [
    childSlot ← stars * span; childSlot ← childSlot + completion;
    address ← directory + childSlot; childRank ← *address;
    if childRank = nil then [ temporary ← temporary ] else [
      childRank ← childRank - one; address ← values + childRank;
      answer ← *address; found ← #1 ]
  ] else [ temporary ← temporary ] ]

/-- Read the actual table entry for a valid canonical cube; return raw found and signed answer. -/
@[expose] def lookup : Code .standard registers :=
  .seq lookupSetup (.seq (.loop (.lt level levels) lookupDigit) lookupFinish)

/-- Read the three original scalar input headers. -/
@[expose] def inputHeaders : Code .standard registers := ram[
  address ← #1; levels ← *address; address ← #2; inner ← *address;
  address ← #3; threshold ← *address ]

/-- Locate both leaf arrays and the shared directory after the original input. -/
@[expose] def inputPointers : Code .standard registers := ram[
  arrayA ← #4; arrayB ← arrayA + span; directory ← arrayB + span ]

/-- Original scalar headers followed by both leaf arrays; address zero is State.init's header. -/
@[expose] def loadInput : Code .standard registers :=
  .seq inputHeaders (.seq constants (.seq (Power.program.rename powerRegisters) inputPointers))

/-- Complete one-tile constructor, retaining separate shared-geometry and per-tile routines. -/
@[expose] def program : Code .standard registers := ram[
  ⟪loadInput⟫; ⟪geometry⟫; ⟪tile⟫ ]

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable
