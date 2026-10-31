/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.PrimeSelection.Program

/-!
# Charged strict-minimum updates

The selector's actual comparison code retains its first minimum, including ties. This local
execution rule does not assume that the input count was computed by a counter; that separate
composition obligation belongs to the full prime-selection controller.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.PrimeSelection

open Cslib.WordRAM

/-- Update a first strict minimum in at most five actual instructions, without touching memory
or any register outside the three result registers. The `found` input is a Boolean word. -/
theorem exec_keep {w : ℕ} (x : Data 160) (hz : x.regs Reg.zero = 0)
    (ho : x.regs Reg.one = 1) (hf : x.regs Reg.found = 0 ∨ x.regs Reg.found = 1) :
    ∃ y, ExecWithin w keep x y 5 ∧
      y.regs Reg.best =
        (if x.regs Reg.found = 0 ∨ x.regs Reg.countResult < x.regs Reg.bestCount then
          x.regs Reg.cursor else x.regs Reg.best) ∧
      y.regs Reg.bestCount =
        (if x.regs Reg.found = 0 ∨ x.regs Reg.countResult < x.regs Reg.bestCount then
          x.regs Reg.countResult else x.regs Reg.bestCount) ∧
      y.regs Reg.found = 1 ∧ y.mem = x.mem ∧
      ∀ i, i ≠ Reg.best → i ≠ Reg.bestCount → i ≠ Reg.found → y.regs i = x.regs i := by
  by_cases h0 : x.regs Reg.found = 0
  · let y := ((x.set Reg.best (x.regs Reg.cursor)).set Reg.bestCount
      (x.regs Reg.countResult)).set Reg.found 1
    have he : ExecWithin w keep x y 5 := by
      ram_eval [keep, y, hz, ho, h0, Reg.best, Reg.bestCount, Reg.found,
        Reg.zero, Reg.one, Reg.countResult, Reg.cursor, Fin.mk.injEq]
    refine ⟨y, he, ?_, ?_, ?_, rfl, ?_⟩
    · simp +decide [y, h0, Reg.best, Reg.bestCount, Reg.found]
    · simp +decide [y, h0, Reg.best, Reg.bestCount, Reg.found]
    · simp +decide [y, Reg.best, Reg.bestCount, Reg.found]
    · intro i hb hc hf
      simp only [y, Data.set_regs, Function.update_of_ne hf, Function.update_of_ne hc,
        Function.update_of_ne hb]
  · have h1 : x.regs Reg.found = 1 := hf.resolve_left h0
    by_cases hlt : x.regs Reg.countResult < x.regs Reg.bestCount
    · let y := (x.set Reg.best (x.regs Reg.cursor)).set Reg.bestCount
        (x.regs Reg.countResult)
      have he : ExecWithin w keep x y 5 := by
        ram_eval [keep, y, hz, ho, h0, hlt, Reg.best, Reg.bestCount, Reg.found,
          Reg.zero, Reg.one, Reg.countResult, Reg.cursor, Fin.mk.injEq]
      refine ⟨y, he, ?_, ?_, ?_, rfl, ?_⟩
      · simp +decide [y, h0, hlt, Reg.best, Reg.bestCount]
      · simp +decide [y, h0, hlt, Reg.best, Reg.bestCount]
      · simpa +decide [y, Function.update_apply, Reg.best, Reg.bestCount, Reg.found] using h1
      · intro i hb hc _
        simp only [y, Data.set_regs, Function.update_of_ne hc, Function.update_of_ne hb]
    · have he : ExecWithin w keep x x 5 := by
        have hself : x.set Reg.best (x.regs Reg.best) = x := by
          apply Data.ext
          · exact Function.update_eq_self _ _
          · rfl
        have hcopy : ExecWithin (B := .standard) w (ram[ Reg.best ← Reg.best ]) x x 1 := by
          simpa only [hself] using
            (ExecWithin.copy (w := w) (x := x) (d := Reg.best) (s := Reg.best))
        exact ExecWithin.branch_neg (by simpa only [Cond.holds_eq, hz] using h0)
          (ExecWithin.branch_neg hlt hcopy)
      exact ⟨x, he, by simp [h0, hlt], by simp [h0, hlt], h1, rfl,
        fun _ _ _ _ => rfl⟩

end Cslib.Algorithms.WordRAM.ExactTriangle.PrimeSelection
