/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Strassen.Frame

/-!
# Native Strassen clearing and stack returns

These internal execution lemmas reuse the existing `zeroFill_exec` implementation. The
clearing footprint is one current output matrix, never a whole caller catalogue or window.
-/

public section

namespace Cslib.Algorithms.WordRAM.Strassen

open Cslib.WordRAM

/-- Clear the actual current output, deriving its end pointer and charging every store.
Only the two cursor registers change. -/
theorem exec_clear {w : ℕ} (x : Data 64) (h0 : x.regs Reg.zero = 0)
    (h1 : x.regs Reg.one = 1) (hw : Fits w (x.regs Reg.output + x.regs Reg.size)) :
    ∃ y, ExecWithin w clear x y (4 * x.regs Reg.size + 4) ∧
      y.mem = WordRAM.clear x.mem (x.regs Reg.output) (x.regs Reg.size) ∧
      ∀ i, i ≠ Reg.address → i ≠ Reg.index → y.regs i = x.regs i := by
  let z := (x.set Reg.address (x.regs Reg.output)).set Reg.index
    (x.regs Reg.output + x.regs Reg.size)
  have hsetup : ExecWithin w
      (ram[ Reg.address ← Reg.output; Reg.index ← Reg.output + Reg.size ]) x z 2 := by
    ram_eval [z, hw, Reg.address, Reg.index, Reg.output, Reg.size]
  have he := zeroFill_exec (x := z) (w := w)
    (cur := Reg.address) (stop := Reg.index) (zero := Reg.zero) (one := Reg.one)
    (by decide) (by decide) (by decide)
    (by simpa +decide [z, Reg.address, Reg.index, Reg.zero] using h0)
    (by simpa +decide [z, Reg.address, Reg.index, Reg.one] using h1)
    (by simp +decide [z, Reg.address, Reg.index])
    (by simpa +decide [z, Reg.address, Reg.index] using hw)
  have hcount : z.regs Reg.index - z.regs Reg.address = x.regs Reg.size := by
    simp +decide [z, Reg.index, Reg.address]
  let y : Data 64 := ⟨Function.update z.regs Reg.address (z.regs Reg.index),
    WordRAM.clear z.mem (z.regs Reg.address) (z.regs Reg.index - z.regs Reg.address)⟩
  refine ⟨y, ?_, ?_, ?_⟩
  · exact (hsetup.seq he.within).mono (by rw [hcount]; omega)
  · dsimp only [y]
    rw [hcount]
    rfl
  · intro i ha hi
    simp only [y, z, Data.set, Function.update_of_ne ha, Function.update_of_ne hi]

/-- Return to the parent or finish the root in three instructions.
The subtraction is charged, and its fit follows from the actual frame pointer. -/
theorem exec_pop {w : ℕ} (x : Data 64) (h7 : x.regs Reg.frameWidth = 7)
    (hw : Fits w (x.regs Reg.frame)) :
    ∃ y, ExecWithin w pop x y 3 ∧ y.mem = x.mem ∧
      y.regs Reg.frame =
        (if x.regs Reg.frames < x.regs Reg.frame then x.regs Reg.frame - 7
          else x.regs Reg.frame) ∧
      y.regs Reg.active =
        (if x.regs Reg.frames < x.regs Reg.frame then x.regs Reg.active else 0) ∧
      ∀ i, i ≠ Reg.frame → i ≠ Reg.active → y.regs i = x.regs i := by
  by_cases hc : x.regs Reg.frames < x.regs Reg.frame
  · have hd : Fits w (x.regs Reg.frame - 7) := hw.of_le (by omega)
    let y := x.set Reg.frame (x.regs Reg.frame - 7)
    have he : ExecWithin w pop x y 3 := by ram_eval [pop, y, hc, h7, hd]
    refine ⟨y, he, rfl, ?_, ?_, ?_⟩
    · simp +decide [y, hc, Reg.frame]
    · simp +decide [y, hc, Reg.frame, Reg.active]
    · intro i hf ha
      simp only [y, Data.set, Function.update_of_ne hf]
  · let y := x.set Reg.active 0
    have he : ExecWithin w pop x y 3 :=
      .branch_neg (by simpa only [Cond.holds_lt] using hc) (.const (fits_zero w))
    refine ⟨y, he, rfl, ?_, ?_, ?_⟩
    · simp +decide [y, hc, Reg.frame, Reg.active]
    · simp +decide [y, hc, Reg.frame, Reg.active]
    · intro i hf ha
      simp only [y, Data.set, Function.update_of_ne ha]

end Cslib.Algorithms.WordRAM.Strassen
