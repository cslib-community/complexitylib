/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.WordRAM.Call
import Complexity.Computability.WordRAM.Notation

/-!
# A framed call with argument delivery and a memory write

The callee increments its argument and writes the result to memory address one. The caller
delivers the argument, retrieves the result, and retains its unrelated control register and
all other memory cells. Unused registers and memory may exceed the word bound. All five actual
instructions are included in the budget.
-/

namespace ComplexityTests.WordRAMCall

open Cslib.WordRAM

private def bank : Fin 2 → Fin 4 := ![1, 2]

private def increment : Code .standard 2 :=
  .seq (.op (.const 1 1)) (.seq (.op (.bin .add 0 0 1)) (.op (.store 1 0)))

private theorem exec_increment {w : ℕ} (x : Data 2) (hfit : Fits w (x.regs 0 + 1)) :
    ∃ y, ExecWithin w increment x y 3 ∧
      y.regs 0 = x.regs 0 + 1 ∧ y.mem 1 = x.regs 0 + 1 ∧
      ∀ p ≠ 1, y.mem p = x.mem p := by
  let y := x.set 1 1 |>.set 0 (x.regs 0 + 1) |>.write 1 (x.regs 0 + 1)
  refine ⟨y, ?_, ?_, ?_, ?_⟩
  · have h1 : Fits w 1 := hfit.of_le (by omega)
    ram_eval [increment, y, h1, hfit]
  · simp [y]
  · simp [y]
  · intro p hp
    simp [y, hp]

private def caller : Code .standard 4 :=
  .seq (.op (.copy 1 0)) (.seq (increment.rename bank) (.op (.copy 0 1)))

private theorem exec_caller {w : ℕ} (x : Data 4) (hfit : Fits w (x.regs 0 + 1)) :
    ∃ y, ExecWithin w caller x y 5 ∧
      y.regs 0 = x.regs 0 + 1 ∧ y.regs 3 = x.regs 3 ∧
      y.mem 1 = x.regs 0 + 1 ∧ ∀ p ≠ 1, y.mem p = x.mem p := by
  have hcall := exec_increment ((x.set 1 (x.regs 0)).comap bank)
    (by simpa [bank] using hfit)
  unfold caller
  apply ExecWithin.call (tCont := 1) (show bank.Injective by decide) ExecWithin.copy hcall
  intro y ⟨hy, hm, hframe⟩ hregs
  have hresult : y.regs 1 = x.regs 0 + 1 := by simpa [bank] using hy
  have hcontrol : y.regs 3 = x.regs 3 := by
    simpa using hregs 3 (by decide)
  refine ⟨y.set 0 (y.regs 1), ExecWithin.copy, ?_, ?_, ?_, ?_⟩
  · simpa using hresult
  · simpa using hcontrol
  · simpa [bank] using hm
  · simpa using hframe

-- The call succeeds although the untouched register and the unused memory do not fit width four.
example :
    let x : Data 4 := ⟨![5, 99, 99, 99], fun p => 16 + p⟩
    ¬x.Bounded 4 ∧ ∃ y, ExecWithin 4 caller x y 5 ∧
      y.regs 0 = 6 ∧ y.regs 3 = 99 ∧ y.mem 1 = 6 ∧ y.mem 2 = 18 := by
  dsimp only
  constructor
  · intro hx
    exact (by decide : ¬Fits 4 99) (hx.1 3)
  · obtain ⟨y, hy, hr, hc, hm, hframe⟩ :=
      exec_caller (w := 4) ⟨![5, 99, 99, 99], fun p => 16 + p⟩ (by decide)
    exact ⟨y, hy, hr, hc, hm, hframe 2 (by decide)⟩

end ComplexityTests.WordRAMCall
