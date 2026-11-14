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
unchanged when oracle memory is mapped to another private-state type.
-/

public section
namespace Cslib.Probability.NativeOpenExecution
variable {Operation Private Other Control : Type} {k : ℕ} {input : List Bool}

/-- Map only oracle memory, preserving the entire actual native configuration. -/
@[expose, simps config memory] def World.mapMemory
    (f : Memory Operation Private → Memory Operation Other)
    (world : World k Control Operation Private input) : World k Control Operation Other input :=
  ⟨world.config, f world.memory⟩

end Cslib.Probability.NativeOpenExecution
