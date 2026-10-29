/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.RecordProduct
public import Complexity.Algorithms.WordRAM.ExactTriangle.RecordProduct.QueryValues
public import Complexity.Algorithms.WordRAM.ExactTriangle.WitnessScan.Exec
public import Complexity.Algorithms.WordRAM.NatSqrt

/-!
# Native consumption of one prepared record's product answers

The existing 320-register producer/product bank stays in place. A disjoint controller reads
the actual record, derives the original piece interval with charged square-root/ceiling code,
and reads nonzero encoded product answers and their raw interleaved coordinates. Each accepted
pair invokes the real original-weight verifier. Once a witness is found, later scans are skipped.
All memory is read-only in this phase; no result, catalogue or window snapshot is needed.

The consumer adapts the control of the pinned `ScanPairs.lean` procedure in the
proof of Theorem 17 at `anthropics/formal-math@16a5ce41304fcdaea4e0be7c132e1c361dc26da5`.
The native ABI, code and charged constants are original. These stage definitions are internal
implementation interfaces. The outer instance loop and prime/global parameter choice are separate.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.RecordWitness

open Cslib.WordRAM

namespace Reg

/-- Absolute product-answer pointer. -/
abbrev output : Fin 400 := 320
/-- Protected interleaved query-pair pointer. -/
abbrev queries : Fin 400 := 321
/-- Actual number of query occurrences. -/
abbrev count : Fin 400 := 322
/-- Original outer dimension. -/
abbrev size : Fin 400 := 323
/-- First original vertex of this piece. -/
abbrev first : Fin 400 := 324
/-- Actual number of original vertices in this piece. -/
abbrev length : Fin 400 := 325
/-- Number of query occurrences already treated. -/
abbrev index : Fin 400 := 326
/-- Constant one. -/
abbrev one : Fin 400 := 327
/-- Actual memory-address temporary. -/
abbrev address : Fin 400 := 328
/-- Loaded canonical-signed product answer. -/
abbrev answer : Fin 400 := 329
/-- Actual piece ordinal read from the prepared record. -/
abbrev piece : Fin 400 := 332
/-- Computed maximum piece length. -/
abbrev blockLength : Fin 400 := 333
/-- Original positive piece divisor. -/
abbrev divisor : Fin 400 := 334
/-- Index/product temporary. -/
abbrev temp : Fin 400 := 335
/-- Raw unsigned success flag. -/
abbrev found : Fin 400 := 392
/-- Original first coordinate of a verified triangle. -/
abbrev witnessA : Fin 400 := 393
/-- Original second coordinate of a verified triangle. -/
abbrev witnessB : Fin 400 := 394
/-- Original third coordinate of a verified triangle. -/
abbrev witnessC : Fin 400 := 395
/-- Actual number of original-weight interval scans performed. -/
abbrev scans : Fin 400 := 396
/-- Constant zero, disjoint from both procedure banks. -/
abbrev zero : Fin 400 := 399

end Reg

/-- Preserve the complete existing producer/product register bank. -/
@[expose] def productBank : Fin 320 → Fin 400 := Fin.castLE (by decide)

/-- The entire thirty-two-register original-weight verifier moves together. -/
@[expose] def scanBank (i : Fin 32) : Fin 400 := ⟨336 + i.val, by omega⟩

/-- The root computation temporarily reuses the first six verifier registers. -/
@[expose] def sqrtBank (i : Fin 6) : Fin 400 := ⟨336 + i.val, by omega⟩

/-- Actual charged square root for the local piece-size decoder. -/
@[expose] def squareRoot : Code .standard 400 := NatSqrt.program.rename sqrtBank

open Reg in
/-- Read original scalar words and the selected record's piece/query fields. -/
@[expose] def readRecord : Code .standard 400 :=
  let sqrtArg := sqrtBank NatSqrt.arg
  let productResult := productBank RecordProduct.Reg.result
  let ordinal := productBank RecordProduct.Reg.ordinal
  let records := productBank (RecordProduct.producerBank Instances.output)
  ram[
  one ← #1; zero ← #0; address ← #3; size ← *address;
  address ← #1; temp ← *address; sqrtArg ← temp;
  address ← #2; divisor ← *address; output ← productResult;
  temp ← size * temp; temp ← temp + temp; piece ← #6; temp ← temp + piece;
  address ← ordinal * temp;
  address ← records + address; address ← address + one; piece ← *address;
  address ← address + one; queries ← *address; address ← address + one; count ← *address;
  found ← #0; witnessA ← #0; witnessB ← #0; witnessC ← #0; scans ← #0; index ← #0 ]

open Reg in
/-- Compute the original interval and deliver the unchanged signed-array pointers once. -/
@[expose] def finishHeader : Code .standard 400 :=
  let root := sqrtBank NatSqrt.root
  let scanAB := scanBank WitnessScan.Reg.ab
  let scanBC := scanBank WitnessScan.Reg.bc
  let scanAC := scanBank WitnessScan.Reg.ac
  let scanN := scanBank WitnessScan.Reg.size
  let scanFirst := scanBank WitnessScan.Reg.first
  let scanLength := scanBank WitnessScan.Reg.length
  ram[
  blockLength ← root + divisor; blockLength ← blockLength - one;
  blockLength ← blockLength / divisor; first ← piece * blockLength; length ← size - first;
  if blockLength < length then [ length ← blockLength ] else [ length ← length ];
  scanAB ← #5; temp ← size * size;
  scanBC ← scanAB + temp;
  scanAC ← scanBC + temp;
  scanN ← size; scanFirst ← first;
  scanLength ← length ]

/-- Complete actual local descriptor and interval decoding. -/
@[expose] def header : Code .standard 400 :=
  .seq readRecord (.seq squareRoot finishHeader)

/-- Actual original signed-weight scan, with the complete bank renamed together. -/
@[expose] def scan : Code .standard 400 := WitnessScan.program.rename scanBank

open Reg in
/-- Load the real original coordinate pair and charge this invocation in the native counter. -/
@[expose] def deliverPair : Code .standard 400 :=
  let scanA := scanBank WitnessScan.Reg.a
  let scanB := scanBank WitnessScan.Reg.b
  ram[
  address ← index + index; address ← address + queries;
  scanA ← *address; address ← address + one;
  scanB ← *address; scans ← scans + one ]

open Reg in
/-- A verifier success returns its original vertex together with the actual pair that was read. -/
@[expose] def receiveWitness : Code .standard 400 :=
  let scanFound := scanBank WitnessScan.Reg.found
  let scanA := scanBank WitnessScan.Reg.a
  let scanB := scanBank WitnessScan.Reg.b
  let scanC := scanBank WitnessScan.Reg.witness
  ram[
  if scanFound = one then [
    found ← one; witnessA ← scanA; witnessB ← scanB;
    witnessC ← scanC ] else [ found ← found ] ]

/-- The accepted-candidate branch contains the real verifier, not a supplied witness routine. -/
@[expose] def scanPair : Code .standard 400 :=
  .seq deliverPair (.seq scan receiveWitness)

open Reg in
/-- Read a product answer only while searching, and skip all later scans after a success. -/
@[expose] def step : Code .standard 400 :=
  .seq (.branch (.eq found zero)
    (.seq (ram[ address ← output + index; answer ← *address ])
      (.branch (.eq answer zero) (.op (.copy answer answer)) scanPair))
    (.op (.copy answer answer))) (.op (.bin .add index index one))

/-- Consume one actual product-answer slice without modifying any memory. -/
@[expose] def consume : Code .standard 400 :=
  .seq header (.loop (.lt Reg.index Reg.count) step)

/-- Actual product calculation followed immediately by original-weight verification. -/
@[expose] def program : Code .standard 400 :=
  .seq (RecordProduct.program.rename productBank) consume

/-- The real producer occupies the existing low bank of the larger caller. -/
@[expose] def produce : Code .standard 400 := RecordProduct.produce.rename productBank

/-- Original initialized producer, actual first-record selection and actual product/verifier.
The selected ordinal is preserved by the real product, so no later reset is needed. -/
@[expose] def entryProgram : Code .standard 400 :=
  .seq produce (.seq (.op (.const (productBank RecordProduct.Reg.ordinal) 0)) program)

/-- The consumer is one fixed finite instruction graph and never reads the physical width. -/
theorem consume_fixed : consume.size ≤ 512 ∧ ¬consume.ReadsWidth := by decide

end Cslib.Algorithms.WordRAM.ExactTriangle.RecordWitness
