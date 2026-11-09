/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ThreeSum.Decision.Program
public import CslibFrontier.Computability.WordRAM.Call

/-!
# Disjoint ordinary-host register banks

## Main results

* `preprocessing_injective`, `host_injective`, `controller_injective`: actual bank embeddings.
* `controller_ne_host`, `controller_ne_preprocessing`: the two callee banks miss outer controls.
* `preprocessing_ne_host`: solver calls cannot alias live traversal registers.

These finite bank proofs are original.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.Decision

open Cslib.WordRAM

/-- Preprocessing occupies its original first 128 registers. -/
theorem preprocessing_injective (r : ℕ) : (preprocessingRegisters r).Injective :=
  (Fin.castAdd_injective _ _).comp (Fin.castAdd_injective _ _)

/-- The host/callee bank retains every original register separately. -/
theorem host_injective (r : ℕ) : (hostRegisters r).Injective :=
  (Fin.castAdd_injective _ _).comp (Fin.natAdd_injective _ _)

/-- The outer controls occupy sixteen distinct registers after both callees. -/
theorem controller_injective (r : ℕ) : (controllerRegisters r).Injective :=
  Fin.natAdd_injective _ _

/-- No live traversal register aliases a host or solver register. -/
theorem preprocessing_ne_host {r : ℕ} (i : Fin 128) (j : Fin (64 + (r + 7))) :
    preprocessingRegisters r i ≠ hostRegisters r j := by
  intro h
  have hv := congrArg Fin.val h
  have hi := i.isLt
  simp only [preprocessingRegisters, hostRegisters, Fin.val_natAdd, Fin.val_castAdd] at hv
  omega

/-- No outer control aliases a host or solver register. -/
theorem controller_ne_host {r : ℕ} (i : Fin 16) (j : Fin (64 + (r + 7))) :
    controllerRegisters r i ≠ hostRegisters r j := by
  intro h
  have hv := congrArg Fin.val h
  have hj := j.isLt
  simp only [controllerRegisters, hostRegisters, Fin.val_natAdd, Fin.val_castAdd] at hv
  omega

/-- No outer control aliases a preprocessing register. -/
theorem controller_ne_preprocessing {r : ℕ} (i : Fin 16) (j : Fin 128) :
    controllerRegisters r i ≠ preprocessingRegisters r j := by
  intro h
  have hv := congrArg Fin.val h
  have hj := j.isLt
  simp only [controllerRegisters, preprocessingRegisters, Fin.val_natAdd, Fin.val_castAdd] at hv
  omega

end Cslib.Algorithms.WordRAM.ThreeSum.Decision
