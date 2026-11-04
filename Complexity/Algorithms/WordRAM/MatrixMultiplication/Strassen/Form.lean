/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Strassen.CopyForm
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Strassen.ArithmeticForm

/-!
# Uniform execution of actual Strassen operand forms

The zero-sign branch executes the proved native copying loop; the other branches execute
the proved signed array arithmetic loop. This internal helper derives its execution from
those real programs. No form values, run or cost certificate is supplied by the caller.
-/

public section

namespace Cslib.Algorithms.WordRAM.Strassen

open Cslib.WordRAM Cslib.WordRAM.Signed

/-- The actual form code has one uniform bound for copying, addition and subtraction. -/
theorem exec_form {w q t₁ t₂ A : ℕ} (base dst : Fin 64) (sign : ℤ) (x : Data 64) (u : ℕ → ℤ)
    (hb : 32 ≤ base.val) (hd : 32 ≤ dst.val)
    (hbt : base ≠ Reg.temporary) (hdt : dst ≠ Reg.temporary)
    (hq : x.regs Reg.quarter = q) (ht₁ : t₁ < 4) (ht₂ : t₂ < 4)
    (hbound : GenericRAM.Signed.Fits w ((A + A : ℕ) : ℤ))
    (hu : ∀ j < 4 * q, (u j).natAbs ≤ A)
    (hinput : ∀ j < 4 * q, x.mem (x.regs base + j) = encode (u j))
    (hw : Fits (w + 2) (x.regs base + 4 * q + x.regs dst + q + 8))
    (hsep : x.regs base + 4 * q ≤ x.regs dst ∨ x.regs dst + q ≤ x.regs base) :
    ∃ y, ExecWithin (w + 2) (form base dst t₁ t₂ sign) x y (26 * q + 12) ∧
      (∀ j < q, y.mem (x.regs dst + j) = encode
        (if sign = 0 then u (t₁ * q + j) else if sign < 0 then
          u (t₁ * q + j) - u (t₂ * q + j) else u (t₁ * q + j) + u (t₂ * q + j))) ∧
      (∀ a, a < x.regs dst ∨ x.regs dst + q ≤ a → y.mem a = x.mem a) ∧
      ∀ i, 32 ≤ i.val → i ≠ Reg.temporary → y.regs i = x.regs i := by
  by_cases hs : sign = 0
  · obtain ⟨y, hy, values, frame, regs⟩ := exec_copyForm base dst x hd hbt hdt hq ht₁ hw hsep
    have he : ExecWithin (w + 2) (form base dst t₁ t₂ sign) x y (26 * q + 12) := by
      simpa only [form, hs, ite_true] using hy.mono (by omega : 7 * q + 9 ≤ 26 * q + 12)
    have hquarter : t₁ * q + q ≤ 4 * q := by
      have hm := Nat.mul_le_mul_right q (Nat.succ_le_of_lt ht₁)
      simpa only [Nat.succ_mul] using hm
    refine ⟨y, he, ?_, frame, regs⟩
    intro j hj
    rw [values j hj, Nat.add_assoc, hinput _ (by omega)]
    simp only [hs, ite_true]
  · obtain ⟨y, hy, values, frame, regs⟩ :=
      exec_arithmeticForm base dst sign x u hb hd hbt hdt hq ht₁ ht₂ hs hbound hu hinput hw hsep
    exact ⟨y, hy, by simpa only [ite_eq_right hs] using values, frame, regs⟩

end Cslib.Algorithms.WordRAM.Strassen
