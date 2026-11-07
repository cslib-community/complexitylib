/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Strassen.Program

/-!
# Charged quadrant-pointer computation

The controller's matrix-pointer fields are in the high bank, and the computed helper
arguments are in the low bank. The static quadrant number selects finite code; its runtime
offset multiplication and address addition are ordinary charged instructions.
-/

public section

namespace Cslib.Algorithms.WordRAM.Strassen

open Cslib.WordRAM

/-- Compute one of the four actual contiguous-quadrant pointers, preserving memory and
every register except the chosen low argument and the offset temporary. -/
theorem exec_quadrant {w t : ℕ} (base dst : Fin 64) (x : Data 64)
    (hbt : base ≠ Reg.temporary) (ht : t < 4)
    (hw : Fits w (x.regs base + 4 * x.regs Reg.quarter + 4)) :
    ∃ y, ExecWithin w (quadrant base dst t) x y 3 ∧ y.mem = x.mem ∧
      y.regs dst = x.regs base + t * x.regs Reg.quarter ∧
      ∀ i, i ≠ dst → i ≠ Reg.temporary → y.regs i = x.regs i := by
  have hqt : Reg.quarter ≠ Reg.temporary := by decide
  have hprod : Fits w (t * x.regs Reg.quarter) := hw.of_le (by
    have hmul := Nat.mul_le_mul_right (x.regs Reg.quarter) (show t ≤ 3 by omega)
    omega)
  have hsum : Fits w (x.regs base + t * x.regs Reg.quarter) := hw.of_le (by
    have hmul := Nat.mul_le_mul_right (x.regs Reg.quarter) (show t ≤ 3 by omega)
    omega)
  have htag : Fits w t := hw.of_le (by omega)
  by_cases ht0 : t = 0
  · let y := x.set dst (x.regs base)
    have he : ExecWithin w (quadrant base dst t) x y 1 := by
      simpa only [quadrant, ht0, ite_true, y] using
        (ExecWithin.copy (B := .standard) (w := w) (d := dst) (s := base) (x := x))
    refine ⟨y, he.mono (by decide), rfl, ?_, ?_⟩
    · simp only [y, Data.set, Function.update_self, ht0, Nat.zero_mul, Nat.add_zero]
    · intro i hi htemp
      exact Function.update_of_ne hi _ _
  · let y := ((x.set Reg.temporary t).set Reg.temporary
      (t * x.regs Reg.quarter)).set dst (x.regs base + t * x.regs Reg.quarter)
    have he : ExecWithin w (quadrant base dst t) x y 3 := by
      ram_eval [quadrant, ht0, y, htag, hprod, hsum, hbt, hqt, Reg.temporary, Reg.quarter]
    refine ⟨y, he, rfl, ?_, ?_⟩
    · simp only [y, Data.set, Function.update_self]
    · intro i hi htemp
      simp only [y, Data.set, Function.update_of_ne hi, Function.update_of_ne htemp]

end Cslib.Algorithms.WordRAM.Strassen
