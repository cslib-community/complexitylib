/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Flat
public import Complexity.Algorithms.MatrixMultiplication.Schonhage.ThinProduct
public import Complexity.Computability.WordRAM.Power

/-!
# Native preparation and encoding of shared matrix bands

The input is `L :: m :: N :: X ++ Y`, with both matrices in row-major order and their
signed entries encoded by `Signed.encode`. The native length header occupies address zero.
The program snapshots the complete initialized input before using the encoder's low workspace,
computes its subset tables, prepares and encodes each band once, and restores the input.

The dense inverse table uses zero for an unselected mask and rank plus one for a selected mask.
The forward table lists the first `K0²` masks of cardinality `m` in increasing numeric order.
The shared output catalogue consists of all left bands followed by all right bands, with
`10^L` consecutive cells per band. A tile refers to its two band entries in this catalogue.

`LeftVar.equiv` and `RightVar.equiv` identify the mathematical alphabets with
`Fin 3 ⊕ (Fin 2 × Fin 2)`, and `Term.equiv` identifies terms with `Option (Fin 3 × Fin 3)`.
The existing native `Encoding.leftDigits`, `Encoding.rightDigits` and `Encoding.termDigits`
also fix the executable flat `Fin 7`/`Fin 10` order: the nine product terms are row-major,
with digit `3*i+j`, and `P0` has digit 9. This preparation retains that numbering unchanged.

## Main definitions

* `BandPreparation.program`: fixed native code, including the actual shared encoders.
* `BandPreparation.input`: flat header and matrix input for `State.init`.
* `BandPreparation.catalogueAddress`: the location of a band's encoding leaf.

## References

Selective adaptation of the band preparation in [AlmanWilliams2026, Section 2.4.1] and
Anthropic's formal-math revision `16a5ce41304fcdaea4e0be7c132e1c361dc26da5`,
[band-array preparation](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Programs/Sec2/Theorem5/Encode/BandArray.lean)
and [all-band encoding](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Programs/Sec2/Theorem5/Encode/AllBands.lean).
The mask scans, dense inverse table, native control and memory layout here are new;
the source's Light machine and execution semantics are not used.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandPreparation

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Original initialized input prefix, including the native length header and three parameters. -/
def inputEnd (m N : ℕ) : ℕ := 4 + 2 * (N * D m)

/-- The encoder's low workspace and the original input are both below the snapshot. -/
def snapshotBase (L m N : ℕ) : ℕ := inputEnd m N + Encoding.scratchBase L + 10 ^ L

/-- Dense mask-to-rank inverse table. -/
def inverseBase (L m N : ℕ) : ℕ := snapshotBase L m N + inputEnd m N

/-- Forward selected-mask table; `2^L` cells are reserved. -/
def tableBase (L m N : ℕ) : ℕ := inverseBase L m N + 2 ^ L

/-- Shared encoding catalogue, after the snapshot and both tables. -/
def catalogueBase (L m N : ℕ) : ℕ := tableBase L m N + 2 ^ L

/-- Every left band, then every right band, occupies one block of `10^L` words. -/
def catalogueAddress (L m N : ℕ) (rightSide : Bool) (β leaf : ℕ) : ℕ :=
  catalogueBase L m N + ((if rightSide then numBands L m N else 0) + β) * 10 ^ L + leaf

/-- One past all allocated memory. -/
def memoryEnd (L m N : ℕ) : ℕ := catalogueBase L m N + 2 * numBands L m N * 10 ^ L

/-- Explicit input-parameter bound used to derive every unsigned arithmetic/address fit.
The signed magnitude condition is separate. This is an ordinary numerical inequality,
without quantification over executions or intermediate states. -/
def wordBudget (L m N : ℕ) : ℕ :=
  256 * (L + N + N * D m + 2 ^ L + 10 ^ L + 2 * numBands L m N * 10 ^ L + 1)

/-- Row-major signed matrix input; no table, power or encoded band is supplied by the caller. -/
def input (L m N : ℕ) (X : Matrix (Fin N) (Fin (D m)) ℤ)
    (Y : Matrix (Fin (D m)) (Fin N) ℤ) : List ℕ :=
  [L, m, N] ++
    (List.finRange N).flatMap (fun i => List.ofFn fun k => Signed.encode (X i k)) ++
    (List.finRange (D m)).flatMap (fun k => List.ofFn fun j => Signed.encode (Y k j))

/-- Low registers are reserved for the existing encoder and copy routines. Persistent
parameters and preparation counters occupy registers 32 through 84 of a fixed bank of 96. -/
abbrev levels : Fin 96 := 32
@[inherit_doc levels] abbrev copySrc : Fin 96 := 0
@[inherit_doc levels] abbrev copyDst : Fin 96 := 1
@[inherit_doc levels] abbrev copyLen : Fin 96 := 2
@[inherit_doc levels] abbrev inner : Fin 96 := 33
@[inherit_doc levels] abbrev rows : Fin 96 := 34
@[inherit_doc levels] abbrev columns : Fin 96 := 35
@[inherit_doc levels] abbrev outerSize : Fin 96 := 36
@[inherit_doc levels] abbrev masks : Fin 96 := 37
@[inherit_doc levels] abbrev cells : Fin 96 := 38
@[inherit_doc levels] abbrev leaves : Fin 96 := 39
@[inherit_doc levels] abbrev prefixSize : Fin 96 := 40
@[inherit_doc levels] abbrev snapshot : Fin 96 := 41
@[inherit_doc levels] abbrev inverse : Fin 96 := 42
@[inherit_doc levels] abbrev table : Fin 96 := 43
@[inherit_doc levels] abbrev catalogue : Fin 96 := 44
@[inherit_doc levels] abbrev bands : Fin 96 := 45
@[inherit_doc levels] abbrev count : Fin 96 := 46
@[inherit_doc levels] abbrev root : Fin 96 := 47
@[inherit_doc levels] abbrev square : Fin 96 := 48
@[inherit_doc levels] abbrev temporary : Fin 96 := 49
@[inherit_doc levels] abbrev one : Fin 96 := 50
@[inherit_doc levels] abbrev two : Fin 96 := 51
@[inherit_doc levels] abbrev three : Fin 96 := 52
@[inherit_doc levels] abbrev four : Fin 96 := 53
@[inherit_doc levels] abbrev seven : Fin 96 := 54
@[inherit_doc levels] abbrev ten : Fin 96 := 55
@[inherit_doc levels] abbrev counter : Fin 96 := 56
@[inherit_doc levels] abbrev mask : Fin 96 := 57
@[inherit_doc levels] abbrev population : Fin 96 := 58
@[inherit_doc levels] abbrev residue : Fin 96 := 59
@[inherit_doc levels] abbrev digit : Fin 96 := 60
@[inherit_doc levels] abbrev limit : Fin 96 := 61
@[inherit_doc levels] abbrev rank : Fin 96 := 62
@[inherit_doc levels] abbrev address : Fin 96 := 63
@[inherit_doc levels] abbrev band : Fin 96 := 64
@[inherit_doc levels] abbrev index : Fin 96 := 66
@[inherit_doc levels] abbrev maskAcc : Fin 96 := 67
@[inherit_doc levels] abbrev outerAcc : Fin 96 := 68
@[inherit_doc levels] abbrev innerAcc : Fin 96 := 69
@[inherit_doc levels] abbrev maskPower : Fin 96 := 70
@[inherit_doc levels] abbrev outerPower : Fin 96 := 71
@[inherit_doc levels] abbrev innerPower : Fin 96 := 72
@[inherit_doc levels] abbrev level : Fin 96 := 73
@[inherit_doc levels] abbrev block : Fin 96 := 75
@[inherit_doc levels] abbrev row : Fin 96 := 77
@[inherit_doc levels] abbrev source : Fin 96 := 79
@[inherit_doc levels] abbrev value : Fin 96 := 80
@[inherit_doc levels] abbrev zero : Fin 96 := 84

/-- Register embedding for the unchanged shared encoders. -/
def encoderRegisters (i : Fin 32) : Fin 96 := ⟨i.val, by omega⟩

/-- Register embedding for the unchanged seven-register copy program. -/
def copyRegisters (i : Fin 7) : Fin 96 := ⟨i.val, by omega⟩

/-- Embed the five-register native power routine in the caller's chosen scalar registers. -/
def powerRegisters (v b n : Fin 96) : Fin 5 → Fin 96 := ![v, counter, b, n, one]

/-- The actual native power routine, with register renaming only. -/
def powerCode (v b n : Fin 96) : Code .standard 96 :=
  Power.program.rename (powerRegisters v b n)

/-- Popcount is computed by an explicit fixed-depth loop of divisions and remainders. -/
def populationCode : Code .standard 96 := ram[
  residue ← mask; population ← #0; counter ← #0;
  while counter < levels do [
    digit ← residue % two; population ← population + digit;
    residue ← residue / two; counter ← counter + one ] ]

/-- Load the three actual header parameters and the small constants. -/
def headerLoads : Code .standard 96 := ram[
  address ← #1; levels ← *address; address ← #2; inner ← *address;
  address ← #3; rows ← *address;
  zero ← #0; one ← #1; two ← #2; three ← #3; four ← #4; seven ← #7; ten ← #10 ]

/-- Compute all five powers with actual renamed native routines. -/
def headerPowers : Code .standard 96 :=
  .seq (powerCode columns four inner) (.seq (ram[ temporary ← levels - inner ])
    (.seq (powerCode outerSize three temporary) (.seq (powerCode masks two levels)
      (.seq (powerCode cells seven levels) (powerCode leaves ten levels)))))

/-- Compute concrete snapshot, table and catalogue addresses. -/
def headerLayout : Code .standard 96 := ram[
  prefixSize ← rows * columns; prefixSize ← prefixSize * two;
  prefixSize ← prefixSize + four;
  snapshot ← leaves * two; snapshot ← snapshot + cells; snapshot ← snapshot + two;
  snapshot ← snapshot + prefixSize;
  inverse ← snapshot + prefixSize; table ← inverse + masks; catalogue ← table + masks ]

/-- Compute the three header parameters, powers and addresses with charged native code. -/
def header : Code .standard 96 := .seq headerLoads (.seq headerPowers headerLayout)

/-- Save every original input word, including the actual length header. -/
def saveInput : Code .standard 96 := ram[
  copySrc ← #0; copyDst ← snapshot; copyLen ← prefixSize;
  ⟪ArrayCopy.program.rename copyRegisters⟫ ]

/-- Visit one mask and update the number of accepted masks. -/
def countBody : Code .standard 96 :=
  .seq populationCode (ram[
    if population = inner then [ count ← count + one ] else [ count ← count ];
    mask ← mask + one ])

/-- Count every size-`m` mask. -/
def countMasks : Code .standard 96 :=
  .seq (ram[ mask ← #0; count ← #0 ]) (.loop (.lt mask masks) countBody)

/-- One explicitly squared trial in the integer square-root search. -/
def rootBody : Code .standard 96 := ram[
  root ← root + one; temporary ← root + one; square ← temporary * temporary ]

/-- Compute the integer square root by squared comparisons. No square-root instruction
is added to the native basis. -/
def rootCode : Code .standard 96 :=
  .seq (ram[
  root ← #0; square ← #1; limit ← count + one
  ]) (.seq (.loop (.lt square limit) rootBody) (ram[ square ← root * root ]))

/-- Compute the ceiling quotient giving the number of bands. -/
def bandCount : Code .standard 96 := ram[
  temporary ← root * outerSize;
  bands ← rows + temporary; bands ← bands - one; bands ← bands / temporary ]

/-- Complete scalar band parameters from native mask counting and root computation. -/
def countCode : Code .standard 96 := .seq countMasks (.seq rootCode bandCount)

/-- Store the two table entries belonging to the current mask and advance both counters. -/
def tableWrite : Code .standard 96 := ram[
    address ← inverse + mask; *address ← zero;
    if population = inner then [
      if rank < square then [
        temporary ← rank + one; *address ← temporary;
        address ← table + rank; *address ← mask ] else [ rank ← rank ];
      rank ← rank + one ] else [ rank ← rank ];
    mask ← mask + one ]

/-- One complete table iteration, including the actual population scan. -/
def tableBody : Code .standard 96 := .seq populationCode tableWrite

/-- Materialize both tables, explicitly initializing every inverse-table cell. -/
def tablesCode : Code .standard 96 :=
  .seq (ram[ mask ← #0; rank ← #0 ]) (.loop (.lt mask masks) tableBody)

/-- Initialize the three digit accumulators and their positional weights. -/
def splitHead : Code .standard 96 := ram[
  residue ← index; maskAcc ← #0; outerAcc ← #0; innerAcc ← #0;
  maskPower ← #1; outerPower ← #1; innerPower ← #1; level ← #0 ]

/-- One base-seven digit, with only ordinary native arithmetic and control. -/
def splitBody : Code .standard 96 := ram[
    digit ← residue % seven; residue ← residue / seven;
    if digit < three then [
      temporary ← digit * outerPower; outerAcc ← outerAcc + temporary;
      outerPower ← outerPower * three ] else [
      digit ← digit - three; temporary ← digit * innerPower;
      innerAcc ← innerAcc + temporary; innerPower ← innerPower * four;
      maskAcc ← maskAcc + maskPower ];
    maskPower ← maskPower * two; level ← level + one ]

/-- Decode a base-seven string into its inner mask and compressed base-three/base-four
offsets, in increasing level order. Every division, remainder, product and increment is native. -/
def splitCode : Code .standard 96 := .seq splitHead (.loop (.lt level levels) splitBody)

/-- Read a real matrix cell only after checking the padded row/column against `N`.
In particular, the potentially oversized row-major product is inside the guard. -/
def readCell (rightSide : Bool) : Code .standard 96 :=
  .seq (ram[
    address ← inverse + maskAcc; rank ← *address; value ← #0 ])
    (.branch (.lt zero rank)
      (.seq (ram[ rank ← rank - one ])
        (.seq (if rightSide then ram[ block ← rank % root ] else ram[ block ← rank / root ])
          (ram[
            temporary ← band * root; block ← temporary + block;
            row ← block * outerSize; row ← row + outerAcc;
            if row < rows then [
              ⟪if rightSide then ram[
                  address ← innerAcc * rows; address ← address + row;
                  temporary ← rows * columns; address ← address + temporary ]
                else ram[ address ← row * columns; address ← address + innerAcc ]⟫;
              address ← address + four; address ← snapshot + address; value ← *address
            ] else [ value ← value ] ])))
      (ram[ value ← value ]))

/-- Actual header and counter initialization for each band. -/
def prepareHead : Code .standard 96 := ram[
  address ← #1; *address ← levels; index ← #0 ]

/-- Decode, guard, load and store one band-array entry. -/
def prepareBody (rightSide : Bool) : Code .standard 96 := ram[
  ⟪splitCode⟫; ⟪readCell rightSide⟫;
  address ← index + two; *address ← value; index ← index + one ]

/-- Prepare every entry of one low-workspace band array, including all zero padding. -/
def prepareBand (rightSide : Bool) : Code .standard 96 :=
  .seq prepareHead (.loop (.lt index cells) (prepareBody rightSide))

/-- Set up the actual encoder-output copy, including its catalogue address arithmetic. -/
def collectHead (rightSide : Bool) : Code .standard 96 := ram[
  copySrc ← cells + two;
  ⟪if rightSide then ram[ temporary ← bands + band ] else ram[ temporary ← band ]⟫;
  temporary ← temporary * leaves; temporary ← catalogue + temporary;
  copyDst ← temporary; copyLen ← leaves ]

/-- Copy the actual encoder output to this band's shared catalogue entry. -/
def collectBand (rightSide : Bool) : Code .standard 96 :=
  .seq (collectHead rightSide) (ArrayCopy.program.rename copyRegisters)

/-- Prepare, encode and collect one shared band, then advance its counter. -/
def bandBody (rightSide : Bool) : Code .standard 96 :=
  .seq (.seq (prepareBand rightSide)
    (.seq ((Encoding.program rightSide).rename encoderRegisters) (collectBand rightSide)))
    (ram[ band ← band + one ])

/-- Each row/column band calls the actual unchanged finite native encoder exactly once. -/
def encodeBands (rightSide : Bool) : Code .standard 96 :=
  .seq (ram[ band ← #0 ]) (.loop (.lt band bands) (bandBody rightSide))

/-- Restore the complete original initialized input after all low-workspace calls. -/
def restoreInput : Code .standard 96 := ram[
  copySrc ← snapshot; copyDst ← #0; copyLen ← prefixSize;
  ⟪ArrayCopy.program.rename copyRegisters⟫ ]

/-- One fixed finite native program for the entire band-preparation component. Halt returns
`catalogue`, the base address of the shared encodings; it is appended by `Code.program`. -/
def program : Code .standard 96 :=
  .seq header (.seq saveInput (.seq countCode (.seq tablesCode
    (.seq (encodeBands false) (.seq (encodeBands true) restoreInput)))))

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandPreparation
