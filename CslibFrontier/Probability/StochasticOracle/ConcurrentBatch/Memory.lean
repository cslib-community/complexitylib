/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.ConcurrentBatch.Protocol

/-!
# Mapping private state in the accepted-batch protocol

Replacing source-private state preserves the complete accepted receipt history,
used opportunities and elapsed duration. Admission depends only on these retained
fields. Committing the same actual receipt commutes with private-state replacement.

## Main definitions

* `ServerState.mapPrivate`: map private state without changing the accepted ledger.

## Main results

* `admit_mapPrivate`: private-state replacement leaves the batch guard unchanged.
* `commit_mapPrivate`: the actual receipt update commutes with private-state mapping.
-/

public section
namespace Cslib.Probability.StochasticOracle.ConcurrentBatch
open NativeOpenExecution
variable {n : ℕ} {Private Other : Type}

/-- Map source-private state while retaining every accepted receipt and public meter. -/
@[expose, simps privateState used elapsed history] def ServerState.mapPrivate (f : Private → Other)
    (state : ServerState n Private) : ServerState n Other :=
  ⟨f state.privateState, state.used, state.elapsed, state.history⟩

/-- Admission inspects only the retained accepted-history and resource fields. -/
@[simp] theorem admit_mapPrivate (limits : Limits n) (f : Private → Other)
    (state : ServerState n Private) (word : Word) :
    admit limits (state.mapPrivate f) word = admit limits state word := rfl

/-- Mapping source-private state commutes with committing the same actual receipt. -/
@[simp] theorem commit_mapPrivate (f : Private → Other) (state : ServerState n Private)
    (receipt : Exchange n) (privateState : Private) :
    (commit state receipt privateState).mapPrivate f =
      commit (state.mapPrivate f) receipt (f privateState) := rfl

end Cslib.Probability.StochasticOracle.ConcurrentBatch
