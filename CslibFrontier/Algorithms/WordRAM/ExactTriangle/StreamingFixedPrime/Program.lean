/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.FixedPrime.Controller

/-!
# One-slot fixed-prime ExactTriangle program

Only the catalogue is computed before traversal. Each iteration writes the next logical
chunk/piece into the same physical slot, runs the complete box product and original-weight
verifier at physical ordinal zero, and resets the heap by a charged copy. The controller
preserves chunk-major/piece-major order and stops immediately after success. No matrix, query or
solver scratch window is cleared between iterations.

The loop initialization and early-stop traversal control (together with `FixedPrime.receive`)
adapt `Host.Loop` at `anthropics/formal-math@16a5ce41304fcdaea4e0be7c132e1c361dc26da5`; one-slot
construction, heap reset and native charges are original.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.StreamingFixedPrime

open Cslib.WordRAM
open FixedPrime (recordBank)

/-- The existing producer occupies the low sixty-four registers throughout the stream. -/
@[expose] def producerBank (i : Fin 64) : Fin 416 :=
  recordBank (RecordWitness.productBank (RecordProduct.producerBank i))

/-- Compute the actual catalogue and producer metadata, without materializing any record. -/
@[expose] def prepare : Code .standard 416 :=
  (Code.seq Instances.catalogue Instances.setup).rename producerBank

/-- Read the total logical count, not the initially zero produced counter. -/
@[expose] def setup : Code .standard 416 :=
  let count := producerBank Instances.total
  open FixedPrime.Reg in
  ram[ index ← #0; limit ← count; found ← #0; scans ← #0; one ← #1 ]

/-- Produce the next logical chunk/piece at the current heap and advance logical progress. -/
@[expose] def construct : Code .standard 416 := Instances.visit.rename producerBank

/-- The complete backend always reads physical slot zero. -/
@[expose] def select : Code .standard 416 :=
  .op (.const (recordBank (RecordWitness.productBank RecordProduct.Reg.ordinal)) 0)

/-- Reclaim the single record only after its answers and original weights have been consumed. -/
@[expose] def reset : Code .standard 416 :=
  .op (.copy (producerBank Instances.heap) (producerBank Instances.output))

/-- Every production, argument, solver, reset and return instruction is executed natively. -/
@[expose] def step : Code .standard 416 :=
  .seq construct (.seq select (.seq FixedPrime.record (.seq reset FixedPrime.receive)))

/-- The existing early-stop controller around immediate construction and consumption. -/
@[expose] def traverse : Code .standard 416 :=
  .seq setup (.loop (.lt FixedPrime.Reg.index FixedPrime.Reg.limit) step)

/-- Initialized one-slot solver over the original header and signed weight arrays. -/
@[expose] def program : Code .standard 416 := .seq prepare traverse

/-- The complete one-slot solver never reads its physical word width. -/
theorem program_not_readsWidth : ¬program.ReadsWidth := by
  simp only [program, prepare, traverse, setup, step, construct, select, reset,
    FixedPrime.record, FixedPrime.receive, BoxRecordWitness.program,
    Code.ReadsWidth, Code.readsWidth_rename, Op.ReadsWidth, Op.bin, reduceCtorEq,
    false_or, or_false]
  have hp := Instances.program_fixed.2
  simp only [Instances.program, Code.ReadsWidth] at hp
  have hr := RecordBoxProduct.program_fixed.2
  have hc := RecordWitness.consume_fixed.2
  tauto

/-- The one-slot solver fits the retained fixed finite code envelope. -/
theorem program_fixed : (program.program FixedPrime.Reg.found).length ≤ 133152 ∧
    ¬(program.program FixedPrime.Reg.found).ReadsWidth := by
  constructor
  · simp only [Code.program, List.length_append, Code.length_assemble,
      List.length_singleton, program, prepare, traverse, setup, step, construct, select,
      reset, FixedPrime.record, FixedPrime.receive, BoxRecordWitness.program,
      Code.size, Code.size_rename]
    have hp := Instances.program_fixed.1
    have hr := RecordBoxProduct.program_fixed.1
    have hc := RecordWitness.consume_fixed.1
    simp only [Instances.program, Code.size] at hp
    omega
  · exact Code.not_readsWidth_program program_not_readsWidth _

end Cslib.Algorithms.WordRAM.ExactTriangle.StreamingFixedPrime
