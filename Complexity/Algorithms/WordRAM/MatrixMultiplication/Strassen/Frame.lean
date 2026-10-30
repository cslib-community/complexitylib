/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Strassen.Program
import Mathlib.Tactic.FinCases

/-!
# Actual seven-word Strassen stack access

The frame lemmas read and write actual memory. They expose only internal composition APIs
for the native controller proof; a caller does not supply a frame layout or execution oracle.
-/

public section

namespace Cslib.Algorithms.WordRAM.Strassen

open Cslib.WordRAM

/-- The fixed order of the seven register fields stored in an explicit frame. -/
@[expose] def field : Fin 7 → Fin 64
  | 0 => Reg.inputA
  | 1 => Reg.inputB
  | 2 => Reg.output
  | 3 => Reg.scratch
  | 4 => Reg.depth
  | 5 => Reg.size
  | 6 => Reg.phase

/-- Store every current field, charge all seven stores and all seven address instructions,
and preserve memory outside exactly this frame. -/
theorem exec_storeFrame {w : ℕ} (x : Data 64) (h1 : x.regs Reg.one = 1)
    (hfit : Fits w (x.regs Reg.frame + 7)) :
    ∃ y, ExecWithin w storeFrame x y 14 ∧
      (∀ j : Fin 7, y.mem (x.regs Reg.frame + j.val) = x.regs (field j)) ∧
      (∀ a, a < x.regs Reg.frame ∨ x.regs Reg.frame + 7 ≤ a → y.mem a = x.mem a) ∧
      ∀ i, i ≠ Reg.address → y.regs i = x.regs i := by
  have hf (k : ℕ) (hk : k ≤ 7) : Fits w (x.regs Reg.frame + k) := hfit.of_le (by omega)
  refine ⟨?y, ?run, ?values, ?frame, ?regs⟩
  case run =>
    ram_eval [storeFrame, h1, hf 1 (by decide), hf 2 (by decide), hf 3 (by decide),
      hf 4 (by decide), hf 5 (by decide), hf 6 (by decide),
      Reg.address, Reg.one, Reg.frame, Reg.inputA, Reg.inputB, Reg.output, Reg.scratch,
      Reg.depth, Reg.size, Reg.phase, Nat.add_assoc]
  case values =>
    intro j
    fin_cases j <;> simp +decide [field, Data.write, Data.set,
      Reg.frame, Reg.inputA, Reg.inputB, Reg.output, Reg.scratch,
      Reg.depth, Reg.size, Reg.phase]
  case frame =>
    intro a ha
    simp only [Data.write, Data.set]
    simp only [Function.update_of_ne (show a ≠ x.regs Reg.frame by omega),
      Function.update_of_ne (show a ≠ x.regs Reg.frame + 1 by omega),
      Function.update_of_ne (show a ≠ x.regs Reg.frame + 2 by omega),
      Function.update_of_ne (show a ≠ x.regs Reg.frame + 3 by omega),
      Function.update_of_ne (show a ≠ x.regs Reg.frame + 4 by omega),
      Function.update_of_ne (show a ≠ x.regs Reg.frame + 5 by omega),
      Function.update_of_ne (show a ≠ x.regs Reg.frame + 6 by omega)]
  case regs =>
    intro i hi
    simp only [Data.write, Data.set, Function.update_of_ne hi]

/-- Registers loaded by the actual frame-read block, including its address temporary. -/
@[expose] def LoadLocal (i : Fin 64) : Prop := i = Reg.address ∨ 32 ≤ i.val ∧ i.val ≤ 38

instance (i : Fin 64) : Decidable (LoadLocal i) :=
  inferInstanceAs (Decidable (i = Reg.address ∨ 32 ≤ i.val ∧ i.val ≤ 38))

/-- Read every field from the actual current frame in fourteen instructions, without stores. -/
theorem exec_loadFrame {w : ℕ} (x : Data 64) (h1 : x.regs Reg.one = 1)
    (hfit : Fits w (x.regs Reg.frame + 7)) :
    ∃ y, ExecWithin w loadFrame x y 14 ∧ y.mem = x.mem ∧
      (∀ j : Fin 7, y.regs (field j) = x.mem (x.regs Reg.frame + j.val)) ∧
      ∀ i, ¬LoadLocal i → y.regs i = x.regs i := by
  have hf (k : ℕ) (hk : k ≤ 7) : Fits w (x.regs Reg.frame + k) := hfit.of_le (by omega)
  refine ⟨?y, ?run, ?memory, ?values, ?regs⟩
  case run =>
    ram_eval [loadFrame, h1, hf 1 (by decide), hf 2 (by decide), hf 3 (by decide),
      hf 4 (by decide), hf 5 (by decide), hf 6 (by decide),
      Reg.address, Reg.one, Reg.frame, Reg.inputA, Reg.inputB, Reg.output, Reg.scratch,
      Reg.depth, Reg.size, Reg.phase, Nat.add_assoc]
  case memory => rfl
  case values =>
    intro j
    fin_cases j <;> simp +decide [field, Data.set,
      Reg.frame, Reg.inputA, Reg.inputB, Reg.output, Reg.scratch,
      Reg.depth, Reg.size, Reg.phase]
  case regs =>
    intro i hi
    have hn (j : Fin 64) (hj : 32 ≤ j.val ∧ j.val ≤ 38) : i ≠ j := by
      intro he
      subst i
      exact hi (Or.inr hj)
    have ha : i ≠ (48 : Fin 64) := fun he => hi (Or.inl he)
    simp only [Data.set, Function.update_of_ne ha, Function.update_of_ne (hn 32 (by decide)),
      Function.update_of_ne (hn 33 (by decide)), Function.update_of_ne (hn 34 (by decide)),
      Function.update_of_ne (hn 35 (by decide)), Function.update_of_ne (hn 36 (by decide)),
      Function.update_of_ne (hn 37 (by decide)), Function.update_of_ne (hn 38 (by decide))]

/-- Loading a frame just stored by the controller restores the same current parameters.
This assertion is produced by native setup/push and maintained by the node proof. -/
theorem exec_loadCurrent {w : ℕ} (x : Data 64) (h1 : x.regs Reg.one = 1)
    (hfit : Fits w (x.regs Reg.frame + 7))
    (hframe : ∀ j : Fin 7, x.mem (x.regs Reg.frame + j.val) = x.regs (field j)) :
    ∃ y, ExecWithin w loadFrame x y 14 ∧ y.mem = x.mem ∧
      ∀ i, i ≠ Reg.address → y.regs i = x.regs i := by
  obtain ⟨y, hy, hm, values, regs⟩ := exec_loadFrame x h1 hfit
  have hfields (j : Fin 7) : y.regs (field j) = x.regs (field j) :=
    (values j).trans (hframe j)
  refine ⟨y, hy, hm, ?_⟩
  intro i hi
  by_cases hc : LoadLocal i
  · have hcases : i = field 0 ∨ i = field 1 ∨ i = field 2 ∨ i = field 3 ∨
        i = field 4 ∨ i = field 5 ∨ i = field 6 := by
      simp only [LoadLocal, Reg.address, Fin.ext_iff] at hc hi
      simp only [field, Reg.inputA, Reg.inputB, Reg.output, Reg.scratch,
        Reg.depth, Reg.size, Reg.phase, Fin.ext_iff]
      omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfields 0
    · exact hfields 1
    · exact hfields 2
    · exact hfields 3
    · exact hfields 4
    · exact hfields 5
    · exact hfields 6
  · exact regs i hc

end Cslib.Algorithms.WordRAM.Strassen
