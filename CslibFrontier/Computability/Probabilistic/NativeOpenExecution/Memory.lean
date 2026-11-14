/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.NativeOpenExecution

/-!
# Mapping native oracle memory while preserving configuration

The complete native configuration, including channels and all tape heads, is
unchanged when oracle memory is mapped to another private-state type. Mapping
only the private component retains the complete raw event log and commutes with
recording a new reply.

## Main definitions

* `Memory.mapPrivate`: replace private state while retaining every raw event.
* `World.mapMemory`: replace memory while retaining the actual native configuration.

## Main results

* `Memory.record_mapPrivate`: private-state mapping commutes with recording a reply.
-/

public section
namespace Cslib.Probability.NativeOpenExecution
variable {Operation Private Other Control : Type} {k : ℕ} {input : List Bool}

/-- Map only private state, retaining all previous raw replies and their resource charges. -/
@[expose, simps privateState events] def Memory.mapPrivate (f : Private → Other)
    (memory : Memory Operation Private) : Memory Operation Other :=
  ⟨f memory.privateState, memory.events⟩

/-- Recording the same observed reply commutes with private-state replacement. -/
@[simp] theorem Memory.record_mapPrivate (f : Private → Other)
    (memory : Memory Operation Private) (query : Operation × List Bool)
    (reply : Reply) (privateState : Private) :
    (memory.record query reply privateState).mapPrivate f =
      (memory.mapPrivate f).record query reply (f privateState) := rfl

/-- Map only oracle memory, preserving the entire actual native configuration. -/
@[expose, simps config memory] def World.mapMemory
    (f : Memory Operation Private → Memory Operation Other)
    (world : World k Control Operation Private input) : World k Control Operation Other input :=
  ⟨world.config, f world.memory⟩

end Cslib.Probability.NativeOpenExecution
