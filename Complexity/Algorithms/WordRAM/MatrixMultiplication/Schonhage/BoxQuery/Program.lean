/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Codes

/-!
# Native sparse box-query controller

Each pending prefix occupies five actual words: depth, completed decimal prefix,
number of non-P0 inner terms, initial inner-P0 count, and power of ten. At an outer
coordinate only the private term is pushed. At an inner coordinate P0 is always
pushed, with the nine other terms only while the threshold permits them. The stack
therefore visits the contributing prefixes of order at most the threshold directly.

Low-order leaves read and multiply actual encoding words. Exact-threshold leaves
read the previously constructed compact box table, with key `stars*10^L+completion`.
Every signed arithmetic operation is the existing native unsigned implementation.
The shared geometry/table are constructed once, outside the reusable query routine.

This worklist implementation is original. It realizes the finite query expression of
[AlmanWilliams2026, Section 4.2] using the existing boxes and native term numbering;
it does not copy the primary source's bounded-nine-string successor or trie machine.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery

open Cslib.WordRAM

/-- The same fixed bank as the shared box-table constructor. -/
abbrev registers : ℕ := BoxTable.registers

namespace Reg

/-- Original output code in the existing least-significant-first numbering. -/
abbrev query : Fin registers := 48
/-- Computed work-stack base, after the retained compact table. -/
abbrev stack : Fin registers := 49
/-- Number of occupied native stack records. -/
abbrev top : Fin registers := 50
/-- Current stack-record address. -/
abbrev cursor : Fin registers := 51
/-- Depth of the popped prefix, incremented before producing children. -/
abbrev depth : Fin registers := 52
/-- Existing native decimal index of the popped prefix. -/
abbrev code : Fin registers := 53
/-- Number of indexed inner terms already chosen. -/
abbrev used : Fin registers := 54
/-- Initial inner P0 count, the canonical box's eventual star count. -/
abbrev stars : Fin registers := 55
/-- Power of ten at the popped prefix's depth. -/
abbrev power : Fin registers := 56
/-- Current output digit, before fixed finite child dispatch. -/
abbrev digit : Fin registers := 57
/-- Completed child decimal prefix. -/
abbrev childCode : Fin registers := 58
/-- Child's indexed-inner count. -/
abbrev childUsed : Fin registers := 59
/-- Child's initial-P0 count. -/
abbrev childStars : Fin registers := 60
/-- Arithmetic temporary outside the signed workspace. -/
abbrev temporary : Fin registers := 61
/-- Canonical signed query accumulator and returned result. -/
abbrev answer : Fin registers := 62
/-- Native stack record width, reusing a finished table-stage temporary. -/
abbrev five : Fin registers := 36
/-- Child power, reusing the finished table-stage stride register. -/
abbrev childPower : Fin registers := 28

end Reg

open Reg

/-- Store every word of one newly occupied stack record before it can be read. -/
@[expose] def push : Code .standard registers := ram[
  cursor ← top * five; cursor ← stack + cursor;
  *cursor ← depth; cursor ← cursor + BoxTable.Reg.one;
  *cursor ← childCode; cursor ← cursor + BoxTable.Reg.one;
  *cursor ← childUsed; cursor ← cursor + BoxTable.Reg.one;
  *cursor ← childStars; cursor ← cursor + BoxTable.Reg.one;
  *cursor ← childPower; top ← top + BoxTable.Reg.one ]

/-- Pop and read one actual complete five-word task. -/
@[expose] def pop : Code .standard registers := ram[
  top ← top - BoxTable.Reg.one; cursor ← top * five; cursor ← stack + cursor;
  depth ← *cursor; cursor ← cursor + BoxTable.Reg.one;
  code ← *cursor; cursor ← cursor + BoxTable.Reg.one;
  used ← *cursor; cursor ← cursor + BoxTable.Reg.one;
  stars ← *cursor; cursor ← cursor + BoxTable.Reg.one;
  power ← *cursor ]

/-- One fixed indexed term; code generation unrolls nine terms, not the input depth. -/
@[expose] def indexedSetup (d : Fin 9) : Code .standard registers := ram[
  temporary ← #d.val; temporary ← temporary * power;
  childCode ← code + temporary; childUsed ← used + BoxTable.Reg.one;
  childStars ← stars ]

/-- Compute and store one indexed child. -/
@[expose] def indexedChild (d : Fin 9) : Code .standard registers :=
  .seq (indexedSetup d) push

/-- Fixed finite dispatch, preserving the genuine constant register count. -/
@[expose] def indexedChildren : List (Fin 9) → Code .standard registers
  | [] => ram[ temporary ← temporary ]
  | d :: ds => .seq (indexedChild d) (indexedChildren ds)

/-- Indexed children are pushed in reverse order, so P0 then digits zero through eight pop first. -/
@[expose] def nineChildren : Code .standard registers :=
  indexedChildren (List.ofFn fun i : Fin 9 => ⟨8 - i.val, by omega⟩)

/-- Compute the P0 child and its exact initial-P0 count. -/
@[expose] def p0Setup : Code .standard registers := ram[
  temporary ← BoxTable.Reg.nine * power; childCode ← code + temporary;
  childUsed ← used;
  if used = BoxTable.Reg.nil then [ childStars ← stars + BoxTable.Reg.one ]
  else [ childStars ← stars ] ]

/-- P0 is the final pushed child and the first visited one. -/
@[expose] def p0Child : Code .standard registers := .seq p0Setup push

/-- Compute the only child at an outer output coordinate. -/
@[expose] def privateSetup : Code .standard registers := ram[
  temporary ← digit * power; childCode ← code + temporary;
  childUsed ← used; childStars ← stars ]

/-- Fixed outer terms introduce no additional query branching. -/
@[expose] def privateChild : Code .standard registers := .seq privateSetup push

/-- Decode the real next output digit and calculate the child depth and power once. -/
@[expose] def expandSetup : Code .standard registers := ram[
  digit ← query / power; digit ← digit % BoxTable.Reg.ten;
  depth ← depth + BoxTable.Reg.one; childPower ← power * BoxTable.Reg.ten ]

/-- Branch only on the original output digit and already used non-P0 inner count. -/
@[expose] def expand : Code .standard registers := .seq expandSetup (ram[
  if digit = BoxTable.Reg.nine then [
    if used < BoxTable.Reg.threshold then [ ⟪nineChildren⟫ ]
    else [ temporary ← temporary ];
    ⟪p0Child⟫ ]
  else [ ⟪privateChild⟫ ] ])

/-- Load and multiply the actual low-order leaf entries. -/
@[expose] def lowProduct : Code .standard registers :=
  .seq (ram[ BoxTable.Reg.completion ← code ]) BoxTable.leafProduct

/-- Deliver the real leaf product as the right signed addend. -/
@[expose] def lowAddend : Code .standard registers :=
  .seq lowProduct (ram[ Signed.right ← BoxTable.Reg.accumulator ])

/-- Compute the canonical box key, actual directory rank, and stored signed addend. -/
@[expose] def boxAddend : Code .standard registers := ram[
  temporary ← stars * BoxTable.Reg.span; temporary ← temporary + code;
  BoxTable.Reg.address ← BoxTable.Reg.directory + temporary;
  BoxTable.Reg.childRank ← *BoxTable.Reg.address;
  BoxTable.Reg.childRank ← BoxTable.Reg.childRank - BoxTable.Reg.one;
  BoxTable.Reg.address ← BoxTable.Reg.values + BoxTable.Reg.childRank;
  Signed.right ← *BoxTable.Reg.address ]

/-- Add one real low product or stored box value to the canonical signed accumulator. -/
@[expose] def addAnswer : Code .standard registers :=
  .seq (ram[ Signed.left ← answer ]) (.seq Signed.add (ram[ answer ← Signed.result ]))

/-- Low-order leaves multiply; exact-threshold leaves use one canonical stored box. -/
@[expose] def leaf : Code .standard registers :=
  .seq (.branch (.lt used BoxTable.Reg.threshold) lowAddend boxAddend) addAnswer

/-- Pop one genuine task, then either expand it or consume its complete-leaf value. -/
@[expose] def body : Code .standard registers :=
  .seq pop (.branch (.lt depth BoxTable.Reg.levels) expand leaf)

/-- Compute the stack base and initialize all five actual root fields. -/
@[expose] def setupScalars : Code .standard registers := ram[
  five ← #5; answer ← #0;
  stack ← BoxTable.Reg.values + BoxTable.Reg.count;
  top ← #0; depth ← #0; childCode ← #0; childUsed ← #0; childStars ← #0; childPower ← #1 ]

/-- Initialize every scalar read by the stack controller, including all five root words. -/
@[expose] def setup : Code .standard registers :=
  .seq BoxTable.constants (.seq setupScalars push)

/-- Reusable query from already constructed geometry and one retained actual value table. -/
@[expose] def queryProgram : Code .standard registers :=
  .seq setup (.loop (.lt BoxTable.Reg.nil top) body)

/-- Read the ordinary depth, order/threshold headers and original output code. -/
@[expose] def inputHeaders : Code .standard registers := ram[
  BoxTable.Reg.address ← #1; BoxTable.Reg.levels ← *BoxTable.Reg.address;
  BoxTable.Reg.address ← #2; BoxTable.Reg.inner ← *BoxTable.Reg.address;
  BoxTable.Reg.address ← #3; BoxTable.Reg.threshold ← *BoxTable.Reg.address;
  BoxTable.Reg.address ← #4; query ← *BoxTable.Reg.address ]

/-- The fourth header shifts the two original arrays by one word relative to table-only input. -/
@[expose] def inputPointers : Code .standard registers := ram[
  BoxTable.Reg.arrayA ← #5; BoxTable.Reg.arrayB ← BoxTable.Reg.arrayA + BoxTable.Reg.span;
  BoxTable.Reg.directory ← BoxTable.Reg.arrayB + BoxTable.Reg.span ]

/-- Actual original-input adaptation, using the existing power code. -/
@[expose] def loadInput : Code .standard registers :=
  .seq inputHeaders (.seq BoxTable.constants
    (.seq (Power.program.rename BoxTable.powerRegisters) inputPointers))

/-- Complete original-input adaptation and actual shared geometry/value construction. -/
@[expose] def prepare : Code .standard registers :=
  .seq loadInput (.seq BoxTable.geometry BoxTable.tile)

/-- Complete constructor and one query: no supplied table, catalogue or execution certificate. -/
@[expose] def program : Code .standard registers := .seq prepare queryProgram

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery
