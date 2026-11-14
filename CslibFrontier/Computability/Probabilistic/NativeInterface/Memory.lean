/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.NativeInterface
public import CslibFrontier.Computability.Probabilistic.NativeOpenExecution.Memory

/-!
# Native instruction selection is blind to oracle-private memory

Selecting an instruction uses the actual configuration and private instruction
coin. Mapping oracle memory therefore commutes with preparation, even when the
private oracle-state type changes. Ready and pending phases carry the same map,
and their world readback commutes with it. Selecting any instruction preserves
the entire oracle memory, including prior receipts. Dispatch may depend on that
memory and is not asserted to commute with an arbitrary map.

## Main results

* `worldOf_mapMemory`: reading back a mapped phase gives the mapped world.
* `instruction_memory`: actual instruction selection preserves all oracle memory.
* `prepare_mapMemory`: the private-coin instruction law commutes with memory replacement.
-/

public section
namespace Cslib.Probability.NativeInterface
open NativeOpenExecution Turing
variable {Operation Private Other Control : Type} {k : ℕ} {input : List Bool}

/-- Change the memory carried by the selected instruction, preserving its operation,
continuation control and complete native configuration. -/
@[expose] def Instruction.mapMemory (f : Memory Operation Private → Memory Operation Other) :
    Instruction k Control Operation Private input → Instruction k Control Operation Other input
  | .halted world => .halted (world.mapMemory f)
  | .local world => .local (world.mapMemory f)
  | .query world op next => .query (world.mapMemory f) op next

/-- Replace oracle memory at either side of the private instruction-selection phase. -/
@[expose] def Phase.mapMemory (f : Memory Operation Private → Memory Operation Other) :
    Phase k Control Operation Private input → Phase k Control Operation Other input
  | .ready world => .ready (world.mapMemory f)
  | .pending chosen => .pending (chosen.mapMemory f)

/-- Readback retains the same configuration and mapped memory in every phase. -/
theorem worldOf_mapMemory (f : Memory Operation Private → Memory Operation Other)
    (phase : Phase k Control Operation Private input) :
    worldOf (phase.mapMemory f) = (worldOf phase).mapMemory f := by
  cases phase with
  | ready world => rfl
  | pending chosen => cases chosen <;> rfl

/-- Selecting an actual native instruction preserves the complete oracle memory,
including its private state and all previously accrued receipts. -/
theorem instruction_memory (machine : MultiTapePTM k Bool Control Operation)
    (world : World k Control Operation Private input) (bit : Bool) :
    (worldOf (.pending (instruction machine world bit))).memory = world.memory := by
  cases hs : world.config.tapes.state with
  | none => simp [instruction, hs, worldOf]
  | some control =>
    simp only [instruction, hs]
    cases machine.tr control world.config.tapes.inputSymbol world.config.tapes.workTapeSymbols
      world.config.answerSymbols bit <;> rfl

/-- Actual instruction selection cannot inspect or branch on oracle-private memory. -/
theorem instruction_mapMemory (machine : MultiTapePTM k Bool Control Operation)
    (f : Memory Operation Private → Memory Operation Other)
    (world : World k Control Operation Private input) (bit : Bool) :
    instruction machine (world.mapMemory f) bit = (instruction machine world bit).mapMemory f := by
  cases hs : world.config.tapes.state with
  | none => simp [instruction, World.mapMemory, hs, Instruction.mapMemory]
  | some c =>
    simp only [instruction, World.mapMemory_config, hs]
    cases machine.tr c world.config.tapes.inputSymbol world.config.tapes.workTapeSymbols
      world.config.answerSymbols bit <;> rfl

/-- The actual private-coin pre-response law preserves arbitrary memory replacement. -/
theorem prepare_mapMemory (machine : MultiTapePTM k Bool Control Operation)
    (f : Memory Operation Private → Memory Operation Other)
    (world : World k Control Operation Private input) :
    prepare machine (world.mapMemory f) =
      (prepare machine world).map (Instruction.mapMemory f) := by
  simp only [prepare, PMF.map_comp, Function.comp_def]
  congr 1
  funext bit
  exact instruction_mapMemory machine f world bit

end Cslib.Probability.NativeInterface
