/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

-- upstream: local-only (tests)

import CslibFrontier.Computability.WordRAM.RegisterFrame

set_option linter.hashCommand false

/-!
# Contiguous register banks and dirty caller frames

A two-register routine copies its input in an interior bank. The theorem applies the shared
interval frame to the actual one-instruction execution; dirty caller registers and memory
remain unrestricted. Registers inside the bank can change, as the negative control checks.
-/

namespace ComplexityTests.WordRAMRegisterFrames

open Cslib.WordRAM

private def bank (i : Fin 2) : Fin 6 := ⟨2 + i.val, by omega⟩

private def copy : Code .standard 2 := .op (.copy 0 1)

/-- Both sides of an interior bank are framed by the actual charged execution. -/
theorem copy_frame (w : ℕ) (x : Data 6) :
    ∃ y, ExecWithin w (copy.rename bank) x y 1 ∧ y.regs 2 = x.regs 3 ∧
      y.mem = x.mem ∧ ∀ i, i.val < 2 ∨ 4 ≤ i.val → y.regs i = x.regs i := by
  let y := x.set 2 (x.regs 3)
  have he : ExecWithin w (copy.rename bank) x y 1 := ExecWithin.copy
  exact ⟨y, he, by simp only [y, Data.set_regs, Function.update_self], rfl,
    fun i hi => he.regs_eq (copy.preserves_rename_of_offset bank (fun _ => rfl) i hi)⟩

private def dirty : Data 6 := (Data.init [999]).set 0 717 |>.set 2 4 |>.set 3 7 |>.set 5 991

#guard match (copy.rename bank).eval 3 1 dirty with
  | some (y, _) => y.regs 2 == 7 && y.regs 0 == 717 && y.regs 5 == 991 && y.mem 1 == 999
  | none => false

-- An owned destination is writable; it cannot satisfy the outside-interval premise.
example : ¬(copy.rename bank).Preserves 2 := by decide
example : ¬((2 : Fin 6).val < 2 ∨ 4 ≤ (2 : Fin 6).val) := by decide

end ComplexityTests.WordRAMRegisterFrames
