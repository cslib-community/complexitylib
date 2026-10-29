/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.Decision.Program

/-!
# Disjoint ordinary-host register banks

## Main results

* `preprocessing_injective`, `host_injective`, `controller_injective`: actual bank embeddings.
* `extend_controller`, `extend_host_controller`, `extend_preprocessing_controller`: register
  readback and frames used by the complete controller.

These finite bank proofs are original.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.Decision

open Cslib.WordRAM

/-- Preprocessing occupies its original first 128 registers. -/
theorem preprocessing_injective (r : ℕ) : (preprocessingRegisters r).Injective := by
  intro i j h
  have hv := congrArg Fin.val h
  exact Fin.ext hv

/-- The host/callee bank retains every original register separately. -/
theorem host_injective (r : ℕ) : (hostRegisters r).Injective := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  dsimp only [hostRegisters] at this
  omega

/-- The outer controls occupy sixteen distinct registers after both callees. -/
theorem controller_injective (r : ℕ) : (controllerRegisters r).Injective := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  dsimp only [controllerRegisters] at this
  omega

/-- No outer control aliases a host or solver register. -/
theorem controller_ne_host {r : ℕ} (i : Fin 16) (j : Fin (64 + (r + 7))) :
    controllerRegisters r i ≠ hostRegisters r j := by
  intro h
  have hv := congrArg Fin.val h
  have hj := j.isLt
  dsimp only [controllerRegisters, hostRegisters] at hv
  omega

/-- Read an embedded controller result. -/
theorem extend_controller {r : ℕ} (a : Data 16) (x : Data (registerCount r)) (i : Fin 16) :
    (a.extend (controllerRegisters r) x).regs (controllerRegisters r i) = a.regs i :=
  (controller_injective r).extend_apply _ _ i

/-- A host call cannot overwrite any outer control. -/
theorem extend_host_controller {r : ℕ} (a : Data (64 + (r + 7)))
    (x : Data (registerCount r)) (i : Fin 16) :
    (a.extend (hostRegisters r) x).regs (controllerRegisters r i) =
      x.regs (controllerRegisters r i) := by
  change Function.extend _ _ _ _ = _
  apply Function.extend_apply'
  rintro ⟨j, hj⟩
  have := congrArg Fin.val hj
  have := j.isLt
  dsimp only [hostRegisters, controllerRegisters] at *
  omega

/-- Preprocessing cannot overwrite the saved length or outer controls. -/
theorem extend_preprocessing_controller {r : ℕ} (a : Data 128)
    (x : Data (registerCount r)) (i : Fin 16) :
    (a.extend (preprocessingRegisters r) x).regs (controllerRegisters r i) =
      x.regs (controllerRegisters r i) := by
  change Function.extend _ _ _ _ = _
  apply Function.extend_apply'
  rintro ⟨j, hj⟩
  have := congrArg Fin.val hj
  have := j.isLt
  dsimp only [preprocessingRegisters, controllerRegisters] at *
  omega

/-- Reading the preprocessing bank after a controller-only operation sees the old registers. -/
theorem extend_controller_preprocessing {r : ℕ} (a : Data 16)
    (x : Data (registerCount r)) (i : Fin 128) :
    (a.extend (controllerRegisters r) x).regs (preprocessingRegisters r i) =
      x.regs (preprocessingRegisters r i) := by
  change Function.extend _ _ _ _ = _
  apply Function.extend_apply'
  rintro ⟨j, hj⟩
  have := congrArg Fin.val hj
  have := i.isLt
  dsimp only [preprocessingRegisters, controllerRegisters] at *
  omega

end Cslib.Algorithms.WordRAM.ThreeSum.Decision
