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
private oracle-state type changes. Dispatch may depend on that memory and is
not asserted to commute with an arbitrary map.
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
