/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.Decision.Controls

/-!
# Actual catalogue-pointer calls

Pointer loads, argument copies, the complete native Convolution call and Boolean accumulation
are charged separately. The callee bank cannot overwrite outer controls; its memory frame keeps
every remaining pointer and packed input below the reserved workspace.

## Main results

* `exec_loadSetup`: actual pointer-table load and all four callee argument copies.
* `exec_finish`: exact native Boolean accumulation and loop increment.

These native composition proofs are original.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.Decision

open Cslib.WordRAM

/-- Load a pointer from actual memory and pass its raw runtime arguments to the host. -/
theorem exec_loadSetup {r w tab num N V k : ℕ} (x : Data (registerCount r))
    (hc : Controls tab num N V x) (hk : x.regs (controllerRegisters r current) = k)
    (ha : Fits w (tab + k)) :
    ∃ y, ExecWithin w (.seq (loadSource.rename (controllerRegisters r)) callSetup) x y 6 ∧
      (y.comap (hostRegisters r)).regs (Host.hostRegisters Host.len) = N ∧
      (y.comap (hostRegisters r)).regs (Host.hostRegisters Host.upper) = V ∧
      (y.comap (hostRegisters r)).regs (Host.hostRegisters Host.base) = x.mem (tab + k) ∧
      (y.comap (hostRegisters r)).regs (Host.hostRegisters Host.matAB) = 2 * V ∧
      Controls tab num N V y ∧
      y.regs (controllerRegisters r current) = k ∧
      y.regs (controllerRegisters r answer) = x.regs (controllerRegisters r answer) ∧
      y.mem = x.mem := by
  let m := controllerRegisters r
  let h := fun i => hostRegisters r (Host.hostRegisters (r := r + 7) i)
  let y := x.set (m address) (tab + k) |>.set (m source) (x.mem (tab + k))
    |>.set (h Host.len) N |>.set (h Host.upper) V
    |>.set (h Host.base) (x.mem (tab + k)) |>.set (h Host.matAB) (2 * V)
  have hm (i j : Fin 16) : m i = m j ↔ i = j := (controller_injective r).eq_iff
  have hh (i j : Fin 64) : h i = h j ↔ i = j :=
    ((host_injective r).comp Host.hostRegisters_injective).eq_iff
  have hmh (i : Fin 16) (j : Fin 64) : m i ≠ h j := controller_ne_host i _
  have hhm (i : Fin 64) (j : Fin 16) : h i ≠ m j := (hmh j i).symm
  have he : ExecWithin w (.seq (loadSource.rename (controllerRegisters r)) callSetup) x y 6 := by
    simp only [loadSource, Code.rename, Op.rename_bin]
    ram_eval [callSetup, Op.rename, y, m, h,
      hc.table, hc.length, hc.envelope, hc.workspace, hk, ha, hm, hh, hmh, hhm,
      address, source, table, current, length, envelope, workspace,
      Host.len, Host.upper, Host.base, Host.matAB, Fin.mk.injEq]
  have hframe (i : Fin 16) (hi : i ≠ address) (hj : i ≠ source) :
      y.regs (m i) = x.regs (m i) := by
    simp only [y, Data.set_regs, Function.update_apply, hm, hj, hi, hmh, ↓reduceIte]
  refine ⟨y, he, ?_, ?_, ?_, ?_, ?_, (hframe _ (by decide) (by decide)).trans hk,
    hframe _ (by decide) (by decide), rfl⟩
  · simp +decide [y, Data.comap_regs, h, hh, Host.len, Host.upper, Host.base, Host.matAB]
  · simp +decide [y, Data.comap_regs, h, hh, Host.upper, Host.base, Host.matAB]
  · simp +decide [y, Data.comap_regs, h, hh, Host.base, Host.matAB]
  · simp [y, Data.comap_regs, h]
  · exact hc.congr (fun i _ _ hi hj => hframe i hi hj)

/-- Boolean accumulation and the next index are actual native instructions. -/
theorem exec_finish {r w k b v : ℕ} (x : Data (registerCount r))
    (ho : x.regs (controllerRegisters r one) = 1)
    (hk : x.regs (controllerRegisters r current) = k)
    (hb : x.regs (controllerRegisters r answer) = b)
    (hv : x.regs (hostRegisters r (Host.hostRegisters Host.found)) = v)
    (hfit : Fits w (k + 1)) :
    ∃ y, ExecWithin w finish x y 4 ∧
      y.regs (controllerRegisters r current) = k + 1 ∧
      y.regs (controllerRegisters r answer) = (if v = 1 then 1 else b) ∧
      (∀ i : Fin 16, i ≠ current → i ≠ answer →
        y.regs (controllerRegisters r i) = x.regs (controllerRegisters r i)) ∧
      y.mem = x.mem := by
  let m := controllerRegisters r
  let y := x.set (m answer) (if v = 1 then 1 else b) |>.set (m current) (k + 1)
  have hm (i j : Fin 16) : m i = m j ↔ i = j := (controller_injective r).eq_iff
  have hmh (i : Fin 16) (j : Fin 64) :
      m i ≠ hostRegisters r (Host.hostRegisters j) := controller_ne_host i _
  have he : ExecWithin w finish x y 4 := by
    by_cases h : v = 1 <;>
      ram_eval [finish, y, m, ho, hk, hb, hv, hfit, hm, hmh, h,
        one, current, answer, Fin.mk.injEq]
  refine ⟨y, he, ?_, ?_, ?_, rfl⟩
  · simp [y, m]
  · simp +decide [y, m, hm, current, answer]
  · intro i hi hj
    change y.regs (m i) = x.regs (m i)
    simp only [y, Data.set_regs, Function.update_apply, hm, hi, hj, ↓reduceIte]

end Cslib.Algorithms.WordRAM.ThreeSum.Decision
