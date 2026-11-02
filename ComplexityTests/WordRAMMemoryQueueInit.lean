/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Computability.WordRAM.Realization.Client.MemoryQueueInit

/-!
# Runtime queue initialization clients

The same two fixed kernels initialize capacities zero and two, including a nonzero base after
an existing input prefix. The examples retain the complete original memory and a caller register
outside the ABI. They certify register setup only: no dirty-memory clearing or queue invariant
is supplied by these kernels.
-/

@[expose] public section

namespace ComplexityTests.WordRAMMemoryQueueInit

open Cslib.WordRAM Cslib.WordRAM.Realization.MemoryQueueInit

/-- Embed the ABI in a register file with four extra caller registers. -/
def registers : Fin 16 ↪ Fin 20 :=
  ⟨Fin.castLE (by decide), Fin.castLE_injective _⟩

/-- The three original input words and the caller's extra register are independent of the
runtime base and capacity. -/
def input (base C : ℕ) : Data 20 :=
  (((Data.init [83, 99, 31]).set 3 C).set 11 base).set 19 77

private theorem input_bounded {base C : ℕ} (hb : Fits 8 base) (hC : Fits 8 C) :
    (input base C).Bounded 8 :=
  (((Data.Bounded.init (by decide : InputFits 8 [83, 99, 31])).set hC).set hb).set (by decide)

private theorem initialized (base C : ℕ) (hb : Fits 8 base) (hC : Fits 8 C)
    (hfit : Fits 8 (base + 2 * (C + 1))) :
    ∃ y, ExecWithin 8 (.seq (spanCode registers) (setupCode registers)) (input base C) y 13 ∧
      y.mem = (input base C).mem ∧ y.regs 11 = base + 2 * (C + 1) ∧
      (∀ i : Fin 8, y.regs (Fin.castLE (by decide) i) =
        ![base, 1, base + 1, C, base + 1 + C, 1, base + 1 + C + 1, C] i) ∧ y.regs 19 = 77 := by
  obtain ⟨s, hs, hsm, hsb, hbase, hfront, hcap, -, hframe⟩ :=
    span_exec registers 8 base C (input base C) (input_bounded hb hC)
      (by simp [input, registers]) (by simp [input, registers]) hfit
  obtain ⟨y, hy, hym, -, hfields, hyfront, -, -, hyframe⟩ :=
    setup_exec registers 8 base C s hsb hbase hcap hfit
  refine ⟨y, hs.seq hy, hym.trans hsm, ?_, ?_, ?_⟩
  · exact hyfront.trans hfront
  · intro i
    exact hfields i
  · have hs19 := hframe 19 (by decide)
    have hy19 := hyframe 19 (by decide)
    exact (hy19.trans hs19).trans (by simp [input])

/-- Capacity zero still reserves two count cells. The original input remains untouched. -/
theorem zero_capacity :
    ∃ y, ExecWithin 8 (.seq (spanCode registers) (setupCode registers)) (input 0 0) y 13 ∧
    y.regs 11 = 2 ∧
    (∀ i : Fin 8, y.regs (Fin.castLE (by decide) i) = ![0, 1, 1, 0, 1, 1, 2, 0] i) ∧
    y.mem 1 = 83 ∧ y.regs 19 = 77 := by
  obtain ⟨y, hy, hm, hf, hl, hc⟩ := initialized 0 0 (by decide) (by decide) (by decide)
  exact ⟨y, hy, hf, hl, by rw [hm]; rfl, hc⟩

/-- The same code initializes capacity two, with all eight runtime layout words checked. -/
example : ∃ y, ExecWithin 8 (.seq (spanCode registers) (setupCode registers)) (input 0 2) y 13 ∧
    y.regs 11 = 6 ∧
    (∀ i : Fin 8, y.regs (Fin.castLE (by decide) i) = ![0, 1, 1, 2, 3, 1, 4, 2] i) ∧
    y.mem 2 = 99 ∧ y.regs 19 = 77 := by
  obtain ⟨y, hy, hm, hf, hl, hc⟩ := initialized 0 2 (by decide) (by decide) (by decide)
  exact ⟨y, hy, hf, hl, by rw [hm]; rfl, hc⟩

/-- A nonzero runtime base lies beyond the input prefix; setup preserves every prefix cell. -/
example : ∃ y, ExecWithin 8 (.seq (spanCode registers) (setupCode registers)) (input 5 2) y 13 ∧
    y.regs 11 = 11 ∧
    (∀ i : Fin 8, y.regs (Fin.castLE (by decide) i) = ![5, 1, 6, 2, 8, 1, 9, 2] i) ∧
    (∀ a < 5, y.mem a = (input 5 2).mem a) ∧ y.regs 19 = 77 := by
  obtain ⟨y, hy, hm, hf, hl, hc⟩ := initialized 5 2 (by decide) (by decide) (by decide)
  exact ⟨y, hy, hf, hl, fun _ _ => congrFun hm _, hc⟩

/-- Too narrow a word cannot admit even the zero-capacity span at base zero. -/
example : ¬Fits 1 (0 + 2 * (0 + 1)) := by decide

end ComplexityTests.WordRAMMemoryQueueInit
