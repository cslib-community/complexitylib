/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.RecordWitness

/-!
# Native traversal of the occupied ExactTriangle catalogue

The producer runs once. The controller visits actual occupied ordinals and invokes the complete
400-register record-product/witness code. A success closes the loop immediately; no later
product or original-weight scan is called. Five disjoint controller registers are used,
and no catalogue/window snapshot or clearing operation is introduced.

The control adapts the fixed-prime part of `Host.Loop` at
`anthropics/formal-math@16a5ce41304fcdaea4e0be7c132e1c361dc26da5`. The existing native producer
uses chunk-major order and prepares all matrices first; the source uses piece-major rounds and
writes each pair of matrices in its round. The code and native charges here are original.
These stage definitions are implementation interfaces, not a parameter/prime-selection host.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.FixedPrime

open Cslib.WordRAM

/-- The complete record-product/witness bank moves together, including both internal banks. -/
@[expose] def recordBank : Fin 400 → Fin 416 := Fin.castLE (by decide)

namespace Reg

/-- Number of actual occupied records visited. -/
abbrev index : Fin 416 := 400
/-- Original occupied count, shortened to the visited prefix only after success. -/
abbrev limit : Fin 416 := 401
/-- Raw unsigned original-witness verdict. -/
abbrev found : Fin 416 := 402
/-- Total actual original-weight scans across all visited records. -/
abbrev scans : Fin 416 := 403
/-- Constant one outside the callee bank. -/
abbrev one : Fin 416 := 404
end Reg

/-- Execute the actual producer once, without changing its finite instruction graph. -/
@[expose] def produce : Code .standard 416 := RecordWitness.produce.rename recordBank

open Reg in
/-- Read the actual producer count and initialize the native controller. -/
@[expose] def setup : Code .standard 416 :=
  let count := recordBank
    (RecordWitness.productBank (RecordProduct.producerBank Instances.produced))
  ram[ index ← #0; limit ← count; found ← #0; scans ← #0; one ← #1 ]

open Reg in
/-- Deliver the actual ordinal to the concrete callee. -/
@[expose] def select : Code .standard 416 :=
  .op (.copy (recordBank (RecordWitness.productBank RecordProduct.Reg.ordinal)) index)

/-- Actual product computation, descriptor reading and original signed-weight verification. -/
@[expose] def record : Code .standard 416 := RecordWitness.program.rename recordBank

open Reg in
/-- Accumulate the actual scan counter and close the loop exactly on a successful return. -/
@[expose] def receive : Code .standard 416 :=
  let returned := recordBank RecordWitness.Reg.found
  let performed := recordBank RecordWitness.Reg.scans
  ram[ scans ← scans + performed; found ← returned; index ← index + one;
    if found = one then [ limit ← index ] else [ limit ← limit ] ]

/-- One actual occupied record, with all argument/return/controller work in native code. -/
@[expose] def step : Code .standard 416 := .seq select (.seq record receive)

/-- Traverse the computed catalogue from a genuine prepared state. -/
@[expose] def traverse : Code .standard 416 :=
  .seq setup (.loop (.lt Reg.index Reg.limit) step)

/-- Complete original-input fixed-prime solver: one preparation and the actual native loop. -/
@[expose] def program : Code .standard 416 := .seq produce traverse

/-- The whole fixed-prime controller is one standard-native program, with a fixed register
bank and at most 133152 flat slots including halt. It never reads the physical word width. -/
theorem program_fixed : (program.program Reg.found).length ≤ 133152 ∧
    ¬(program.program Reg.found).ReadsWidth := by
  constructor
  · simp only [Code.program, List.length_append, Code.length_assemble,
      List.length_singleton, program, produce, traverse, setup, step, select, record,
      receive, RecordWitness.produce, RecordProduct.produce, RecordWitness.program,
      Code.size, Code.size_rename]
    have hp := Instances.program_fixed.1
    have hr := RecordProduct.program_fixed.1
    have hc := RecordWitness.consume_fixed.1
    omega
  · apply Code.not_readsWidth_program
    simp only [program, produce, traverse, setup, step, select, record, receive,
      RecordWitness.produce, RecordProduct.produce, RecordWitness.program,
      Code.ReadsWidth, Code.readsWidth_rename, Op.ReadsWidth, Op.bin, reduceCtorEq,
      false_or, or_false]
    exact not_or.mpr ⟨Instances.program_fixed.2,
      not_or.mpr ⟨RecordProduct.program_fixed.2, RecordWitness.consume_fixed.2⟩⟩

end Cslib.Algorithms.WordRAM.ExactTriangle.FixedPrime
