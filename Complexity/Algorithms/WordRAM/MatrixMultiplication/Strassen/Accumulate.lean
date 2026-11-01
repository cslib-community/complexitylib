/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Strassen.Quadrant
public import Complexity.Computability.WordRAM.Signed.ArrayArithmetic.Exec

/-!
# Native in-place Strassen product accumulation

The actual selected output quarter is both the first input and destination of the existing
signed vector loop. Its exact-alias theorem is essential here. The child product buffer is
disjoint; dirty words outside this one output quarter retain their previous values.
-/

public section

namespace Cslib.Algorithms.WordRAM.Strassen

open Cslib.WordRAM Cslib.WordRAM.Signed

/-- Add/subtract one actual child result in place, charging the selected-quadrant address,
all three argument copies, and the complete signed vector loop. -/
theorem exec_accumulate {w q t A B : ℕ} (subtract : Bool) (x : Data 64) (u v : ℕ → ℤ)
    (hq : x.regs Reg.quarter = q) (ht : t < 4)
    (hbound : GenericRAM.Signed.Fits w ((A + B : ℕ) : ℤ))
    (hu : ∀ j < q, (u j).natAbs ≤ A) (hv : ∀ j < q, (v j).natAbs ≤ B)
    (hout : ∀ j < q, x.mem (x.regs Reg.output + t * q + j) = encode (u j))
    (hprod : ∀ j < q, x.mem (x.regs Reg.product + j) = encode (v j))
    (hw : Fits (w + 2) (x.regs Reg.output + 4 * q + x.regs Reg.product + q + 8))
    (hsep : x.regs Reg.product + q ≤ x.regs Reg.output ∨
      x.regs Reg.output + 4 * q ≤ x.regs Reg.product) :
    ∃ y, ExecWithin (w + 2) (accumulate t subtract) x y (26 * q + 10) ∧
      (∀ j < q, y.mem (x.regs Reg.output + t * q + j) =
        encode (if subtract then u j - v j else u j + v j)) ∧
      (∀ a, a < x.regs Reg.output + t * q ∨ x.regs Reg.output + t * q + q ≤ a →
        y.mem a = x.mem a) ∧
      ∀ i, 32 ≤ i.val → i ≠ Reg.temporary → y.regs i = x.regs i := by
  have hqfit : Fits (w + 2) (x.regs Reg.output + 4 * x.regs Reg.quarter + 4) := by
    rw [hq]
    exact hw.of_le (by omega)
  obtain ⟨s, hs, hsm, hsrc, hsr⟩ := exec_quadrant Reg.output Reg.operandA x (by decide) ht hqfit
  have hhigh (i : Fin 64) (hi : 32 ≤ i.val) (htemp : i ≠ Reg.temporary) :
      s.regs i = x.regs i := hsr i (by intro he; subst i; contradiction) htemp
  have hsq := (hhigh Reg.quarter (by decide) (by decide)).trans hq
  have hsp := hhigh Reg.product (by decide) (by decide)
  have hsa : s.regs Reg.operandA = x.regs Reg.output + t * q := by
    simpa only [hq] using hsrc
  let z := ((s.set Reg.operandB (x.regs Reg.product)).set Reg.target
    (x.regs Reg.output + t * q)).set Reg.length q
  have hargs : ExecWithin (B := .standard) (w + 2)
      (ram[ Reg.operandB ← Reg.product; Reg.target ← Reg.operandA; Reg.length ← Reg.quarter ])
      s z 3 := by
    ram_eval [z, hsp, hsa, hsq, Reg.operandB, Reg.target, Reg.operandA, Reg.length]
  let f : Fin 16 → Fin 64 := Fin.castLE (by decide)
  have hza : (z.comap f).regs Signed.ArrayArithmetic.Reg.inputA = x.regs Reg.output + t * q := by
    simpa +decide [z, f, Data.comap, Reg.operandA, Reg.operandB, Reg.target, Reg.length,
      Signed.ArrayArithmetic.Reg.inputA] using hsa
  have hzb : (z.comap f).regs Signed.ArrayArithmetic.Reg.inputB = x.regs Reg.product := by
    simp +decide [z, f, Data.comap, Reg.operandB, Reg.target, Reg.length,
      Signed.ArrayArithmetic.Reg.inputB]
  have hzo : (z.comap f).regs Signed.ArrayArithmetic.Reg.output = x.regs Reg.output + t * q := by
    simp +decide [z, f, Data.comap, Reg.operandB, Reg.target, Reg.length,
      Signed.ArrayArithmetic.Reg.output]
  have hzl : (z.comap f).regs Signed.ArrayArithmetic.Reg.length = q := by
    simp [z, f, Data.comap, Reg.length, Signed.ArrayArithmetic.Reg.length]
  have hzm : (z.comap f).mem = x.mem := hsm
  have hquarter : t * q + q ≤ 4 * q := by
    have hmul := Nat.mul_le_mul_right q (Nat.succ_le_of_lt ht)
    simpa only [Nat.succ_mul] using hmul
  obtain ⟨v', hv', values, frame, _⟩ := Signed.ArrayArithmetic.exec subtract (z.comap f) u v
    hzl hbound hu hv
    (by intro j hj; rw [hzm, hza]; exact hout j hj)
    (by intro j hj; rw [hzm, hzb]; exact hprod j hj)
    (by rw [hza]; exact hw.of_le (by omega))
    (by rw [hzb]; exact hw.of_le (by omega))
    (by rw [hzo]; exact hw.of_le (by omega))
    (Or.inr (Or.inr (hza.trans hzo.symm)))
    (by
      rw [hzb, hzo]
      rcases hsep with h | h
      · exact Or.inl (by omega)
      · exact Or.inr (Or.inl (by omega)))
  let y := v'.extend f z
  have hvector : ExecWithin (w + 2)
      ((Signed.ArrayArithmetic.program subtract).rename f) z y (26 * q + 4) :=
    hv'.rename (Fin.castLE_injective _)
  have he : ExecWithin (w + 2) (accumulate t subtract) x y (26 * q + 10) := by
    exact (hs.seq (hargs.seq hvector)).mono (by omega)
  refine ⟨y, he, ?_, ?_, ?_⟩
  · intro j hj
    simpa only [y, Data.extend, hzo] using values j hj
  · intro a ha
    simpa only [y, Data.extend, hzm] using frame a (by simpa only [hzo] using ha)
  · intro i hi htemp
    have hn : ¬∃ j, f j = i := by
      rintro ⟨j, hj⟩
      have hj' := congrArg Fin.val hj
      change j.val = i.val at hj'
      omega
    have hyi : y.regs i = z.regs i := Function.extend_apply' _ _ _ hn
    apply hyi.trans
    have hib : i ≠ Reg.operandB := by intro h; subst i; contradiction
    have hit : i ≠ Reg.target := by intro h; subst i; contradiction
    have hil : i ≠ Reg.length := by intro h; subst i; contradiction
    simpa only [z, Data.set, Function.update_of_ne hib, Function.update_of_ne hit,
      Function.update_of_ne hil] using hhigh i hi htemp

end Cslib.Algorithms.WordRAM.Strassen
