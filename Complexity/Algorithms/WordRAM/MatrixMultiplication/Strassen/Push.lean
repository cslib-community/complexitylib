/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Strassen.Frame
import Mathlib.Tactic.FinCases

/-!
# Native Strassen child layout and explicit frame push

The six buffer calculations and the parent/child frame stores are actual native execution.
The frame readback is proved from those stores; it is not supplied as an algorithm input.
Only one parent phase cell and seven newly pushed frame words change memory.
-/

public section

namespace Cslib.Algorithms.WordRAM.Strassen

open Cslib.WordRAM

/-- Six native arithmetic/copy instructions derive every child buffer and depth. -/
theorem exec_locateChild {w : ℕ} (x : Data 64) (h1 : x.regs Reg.one = 1)
    (h4 : x.regs Reg.four = 4)
    (hw : Fits w (x.regs Reg.scratch + x.regs Reg.size + x.regs Reg.depth + 4)) :
    ∃ y, ExecWithin w locateChild x y 6 ∧ y.mem = x.mem ∧
      y.regs Reg.quarter = x.regs Reg.size / 4 ∧
      y.regs Reg.formA = x.regs Reg.scratch ∧
      y.regs Reg.formB = x.regs Reg.scratch + x.regs Reg.size / 4 ∧
      y.regs Reg.product = x.regs Reg.scratch + 2 * (x.regs Reg.size / 4) ∧
      y.regs Reg.childScratch = x.regs Reg.scratch + 3 * (x.regs Reg.size / 4) ∧
      y.regs Reg.childDepth = x.regs Reg.depth - 1 ∧
      ∀ i, i ≠ Reg.quarter → i ≠ Reg.formA → i ≠ Reg.formB → i ≠ Reg.product →
        i ≠ Reg.childScratch → i ≠ Reg.childDepth → y.regs i = x.regs i := by
  have hq : Fits w (x.regs Reg.size / 4) := hw.of_le (by omega)
  have hf : Fits w (x.regs Reg.scratch + x.regs Reg.size / 4) := hw.of_le (by omega)
  have hp : Fits w (x.regs Reg.scratch + x.regs Reg.size / 4 + x.regs Reg.size / 4) :=
    hw.of_le (by omega)
  have hs : Fits w (x.regs Reg.scratch + x.regs Reg.size / 4 +
      x.regs Reg.size / 4 + x.regs Reg.size / 4) := hw.of_le (by omega)
  have hd : Fits w (x.regs Reg.depth - 1) := hw.of_le (by omega)
  refine ⟨?locatedState, ?locateRun, ?locateMem, ?locatedQuarter, ?locatedA, ?locatedB,
    ?locatedProduct, ?locatedScratch, ?locatedDepth, ?locatedRegs⟩
  case locateRun =>
    ram_eval [locateChild, h1, h4, hq, hf, hp, hs, hd, Reg.quarter, Reg.formA,
      Reg.formB, Reg.product, Reg.childScratch, Reg.childDepth, Reg.one, Reg.four,
      Reg.size, Reg.depth, Reg.scratch]
  case locateMem => rfl
  case locatedQuarter => rfl
  case locatedA => rfl
  case locatedB => rfl
  case locatedProduct =>
    change x.regs Reg.scratch + x.regs Reg.size / 4 + x.regs Reg.size / 4 =
      x.regs Reg.scratch + 2 * (x.regs Reg.size / 4)
    omega
  case locatedScratch =>
    change x.regs Reg.scratch + x.regs Reg.size / 4 + x.regs Reg.size / 4 +
      x.regs Reg.size / 4 = x.regs Reg.scratch + 3 * (x.regs Reg.size / 4)
    omega
  case locatedDepth => rfl
  case locatedRegs =>
    intro i hq ha hb hp hs hd
    simp only [Data.set, Function.update_of_ne hq, Function.update_of_ne ha,
      Function.update_of_ne hb, Function.update_of_ne hp, Function.update_of_ne hs,
      Function.update_of_ne hd]

/-- Only current frame fields, its pointer, address scratch and dispatch tag change on push. -/
@[expose] def PushLocal (i : Fin 64) : Prop :=
  (32 ≤ i.val ∧ i.val ≤ 39) ∨ i = Reg.address ∨ i = Reg.tag

instance (i : Fin 64) : Decidable (PushLocal i) :=
  inferInstanceAs (Decidable ((32 ≤ i.val ∧ i.val ≤ 39) ∨ i = Reg.address ∨ i = Reg.tag))

private theorem push_preserves (phase : Fin 8) (i : Fin 64) :
    ¬PushLocal i → (push phase.val).Preserves i := by decide +kernel +revert

/-- Push a real child in twenty-six instructions, preserving the old parent fields except
its phase and writing the entire new frame. All child fields come from actual controller words. -/
theorem exec_push {w : ℕ} (phase : Fin 8) (x : Data 64)
    (h1 : x.regs Reg.one = 1) (h7 : x.regs Reg.frameWidth = 7)
    (hw : Fits w (x.regs Reg.frame + 14)) :
    ∃ y, ExecWithin w (push phase.val) x y 26 ∧
      y.regs Reg.frame = x.regs Reg.frame + 7 ∧
      y.regs Reg.inputA = x.regs Reg.formA ∧ y.regs Reg.inputB = x.regs Reg.formB ∧
      y.regs Reg.output = x.regs Reg.product ∧ y.regs Reg.scratch = x.regs Reg.childScratch ∧
      y.regs Reg.depth = x.regs Reg.childDepth ∧ y.regs Reg.size = x.regs Reg.quarter ∧
      y.regs Reg.phase = 0 ∧
      (∀ j : Fin 7, y.mem (y.regs Reg.frame + j.val) = y.regs (field j)) ∧
      y.mem (x.regs Reg.frame + 6) = phase.val ∧
      (∀ a, a < x.regs Reg.frame + 6 ∨ x.regs Reg.frame + 14 ≤ a → y.mem a = x.mem a) ∧
      ∀ i, ¬PushLocal i → y.regs i = x.regs i := by
  have h6 : Fits w 6 := hw.of_le (by omega)
  have hphase : Fits w phase.val := hw.of_le (by omega)
  have hparent : Fits w (x.regs Reg.frame + 6) := hw.of_le (by omega)
  have hchild : Fits w (x.regs Reg.frame + 7) := hw.of_le (by omega)
  let r := x.write (x.regs Reg.frame + 6) phase.val
  let s := (((((((((((r.set Reg.tag 6).set Reg.address (x.regs Reg.frame + 6)).set
    Reg.phase phase.val).set Reg.frame (x.regs Reg.frame + 7)).set Reg.inputA
    (x.regs Reg.formA)).set Reg.inputB (x.regs Reg.formB)).set Reg.output
    (x.regs Reg.product)).set Reg.scratch (x.regs Reg.childScratch)).set Reg.depth
    (x.regs Reg.childDepth)).set Reg.size (x.regs Reg.quarter)).set Reg.phase 0)
  have hpre : ExecWithin w (pushArguments phase.val) x s 12 := by
    ram_eval [pushArguments, s, r, h1, h7, h6, hphase, hparent, hchild,
      Reg.tag, Reg.address, Reg.phase, Reg.frame, Reg.inputA, Reg.inputB,
      Reg.output, Reg.scratch, Reg.depth, Reg.size, Reg.formA, Reg.formB,
      Reg.product, Reg.childScratch, Reg.childDepth, Reg.quarter, Reg.frameWidth,
      Reg.one, Fin.mk.injEq]
  have hsframe : s.regs Reg.frame = x.regs Reg.frame + 7 := by
    simp +decide [s, r, Reg.tag, Reg.address, Reg.phase, Reg.frame, Reg.inputA, Reg.inputB,
      Reg.output, Reg.scratch, Reg.depth, Reg.size]
  obtain ⟨y, hy, values, frame, regs⟩ := exec_storeFrame s
    (by simpa +decide [s, r, Reg.tag, Reg.address, Reg.phase, Reg.frame,
      Reg.inputA, Reg.inputB, Reg.output, Reg.scratch, Reg.depth, Reg.size, Reg.one] using h1)
    (by simpa only [hsframe, Nat.add_assoc] using hw)
  have he : ExecWithin w (push phase.val) x y 26 := hpre.seq hy
  have hyframe : y.regs Reg.frame = x.regs Reg.frame + 7 :=
    (regs Reg.frame (by decide)).trans hsframe
  have hfields (j : Fin 7) : y.regs (field j) = s.regs (field j) := by
    apply regs
    fin_cases j <;> decide
  refine ⟨y, he, hyframe, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun i hi => he.regs_eq (push_preserves phase i hi)⟩
  · simpa +decide [field, s, r, Reg.tag, Reg.address, Reg.phase, Reg.frame, Reg.inputA, Reg.inputB,
      Reg.output, Reg.scratch, Reg.depth, Reg.size] using hfields 0
  · simpa +decide [field, s, r, Reg.tag, Reg.address, Reg.phase, Reg.frame, Reg.inputA, Reg.inputB,
      Reg.output, Reg.scratch, Reg.depth, Reg.size] using hfields 1
  · simpa +decide [field, s, r, Reg.tag, Reg.address, Reg.phase, Reg.frame, Reg.inputA, Reg.inputB,
      Reg.output, Reg.scratch, Reg.depth, Reg.size] using hfields 2
  · simpa +decide [field, s, r, Reg.tag, Reg.address, Reg.phase, Reg.frame, Reg.inputA, Reg.inputB,
      Reg.output, Reg.scratch, Reg.depth, Reg.size] using hfields 3
  · simpa +decide [field, s, r, Reg.tag, Reg.address, Reg.phase, Reg.frame, Reg.inputA, Reg.inputB,
      Reg.output, Reg.scratch, Reg.depth, Reg.size] using hfields 4
  · simpa +decide [field, s, r, Reg.tag, Reg.address, Reg.phase, Reg.frame, Reg.inputA, Reg.inputB,
      Reg.output, Reg.scratch, Reg.depth, Reg.size] using hfields 5
  · simpa +decide [field, s, r, Reg.tag, Reg.address, Reg.phase, Reg.frame, Reg.inputA, Reg.inputB,
      Reg.output, Reg.scratch, Reg.depth, Reg.size] using hfields 6
  · intro j
    rw [hyframe, ← hsframe, values j, hfields j]
  · rw [frame _ (Or.inl (by rw [hsframe]; omega))]
    exact Function.update_self _ _ _
  · intro a ha
    rw [frame _ (by rw [hsframe]; omega)]
    change Function.update x.mem (x.regs Reg.frame + 6) phase.val a = x.mem a
    exact Function.update_of_ne (by omega) _ _

end Cslib.Algorithms.WordRAM.Strassen
