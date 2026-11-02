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
# Actual two-quadrant Strassen operand forms

Both source pointers are computed by native quadrant address blocks. The existing signed
array loop then reads, adds/subtracts and stores every coefficient. Original matrix bounds
imply operand fits; the output may be dirty. This internal composition lemma does not assume
the recursively computed matrix product or its execution/time contract.
-/

public section

namespace Cslib.Algorithms.WordRAM.Strassen

open Cslib.WordRAM Cslib.WordRAM.Signed

/-- Materialize a signed sum/difference of two actual matrix quarters in a disjoint buffer,
charging all address multiplication, argument copies and vector instructions. -/
theorem exec_arithmeticForm {w q t₁ t₂ A : ℕ} (base dst : Fin 64) (sign : ℤ)
    (x : Data 64) (u : ℕ → ℤ)
    (hb : 32 ≤ base.val) (hd : 32 ≤ dst.val)
    (hbt : base ≠ Reg.temporary) (hdt : dst ≠ Reg.temporary)
    (hq : x.regs Reg.quarter = q) (ht₁ : t₁ < 4) (ht₂ : t₂ < 4) (hsign : sign ≠ 0)
    (hbound : GenericRAM.Signed.Fits w ((A + A : ℕ) : ℤ))
    (hu : ∀ j < 4 * q, (u j).natAbs ≤ A)
    (hinput : ∀ j < 4 * q, x.mem (x.regs base + j) = encode (u j))
    (hw : Fits (w + 2) (x.regs base + 4 * q + x.regs dst + q + 8))
    (hsep : x.regs base + 4 * q ≤ x.regs dst ∨ x.regs dst + q ≤ x.regs base) :
    ∃ y, ExecWithin (w + 2) (form base dst t₁ t₂ sign) x y (26 * q + 12) ∧
      (∀ j < q, y.mem (x.regs dst + j) = encode
        (if sign < 0 then u (t₁ * q + j) - u (t₂ * q + j)
          else u (t₁ * q + j) + u (t₂ * q + j))) ∧
      (∀ a, a < x.regs dst ∨ x.regs dst + q ≤ a → y.mem a = x.mem a) ∧
      ∀ i, 32 ≤ i.val → i ≠ Reg.temporary → y.regs i = x.regs i := by
  have hqfit : Fits (w + 2) (x.regs base + 4 * x.regs Reg.quarter + 4) := by
    rw [hq]
    exact hw.of_le (by omega)
  obtain ⟨r, hr, hrmem, hra, hrr⟩ := exec_quadrant base Reg.operandA x hbt ht₁ hqfit
  have hrhigh (i : Fin 64) (hi : 32 ≤ i.val) (htemp : i ≠ Reg.temporary) :
      r.regs i = x.regs i := hrr i (by intro he; subst i; contradiction) htemp
  have hrq := (hrhigh Reg.quarter (by decide) (by decide)).trans hq
  have hrbase := hrhigh base hb hbt
  obtain ⟨s, hs, hsmem, hsb, hsr⟩ := exec_quadrant base Reg.operandB r hbt ht₂
    (by simpa only [hrbase, hrq, hq] using hqfit)
  have hshigh (i : Fin 64) (hi : 32 ≤ i.val) (htemp : i ≠ Reg.temporary) :
      s.regs i = x.regs i :=
    (hsr i (by intro he; subst i; contradiction) htemp).trans (hrhigh i hi htemp)
  have hsq := (hshigh Reg.quarter (by decide) (by decide)).trans hq
  have hsd := hshigh dst hd hdt
  have hsa : s.regs Reg.operandA = x.regs base + t₁ * q := by
    rw [hsr Reg.operandA (by decide) (by decide), hra, hq]
  have hsb' : s.regs Reg.operandB = x.regs base + t₂ * q := by
    simpa only [hrbase, hrq] using hsb
  have hmem : s.mem = x.mem := hsmem.trans hrmem
  let z := (s.set Reg.target (x.regs dst)).set Reg.length q
  have hargs : ExecWithin (B := .standard) (w + 2)
      (ram[ Reg.target ← dst; Reg.length ← Reg.quarter ]) s z 2 := by
    ram_eval [z, hsq, hsd, Reg.target, Reg.length]
  let f : Fin 16 → Fin 64 := Fin.castLE (by decide)
  have hza : (z.comap f).regs Signed.ArrayArithmetic.Reg.inputA = x.regs base + t₁ * q := by
    simpa +decide [z, f, Data.comap, Reg.target, Reg.length, Reg.operandA,
      Signed.ArrayArithmetic.Reg.inputA] using hsa
  have hzb : (z.comap f).regs Signed.ArrayArithmetic.Reg.inputB = x.regs base + t₂ * q := by
    simpa +decide [z, f, Data.comap, Reg.target, Reg.length, Reg.operandB,
      Signed.ArrayArithmetic.Reg.inputB] using hsb'
  have hzo : (z.comap f).regs Signed.ArrayArithmetic.Reg.output = x.regs dst := by
    simp +decide [z, f, Data.comap, Reg.target, Reg.length, Signed.ArrayArithmetic.Reg.output]
  have hzl : (z.comap f).regs Signed.ArrayArithmetic.Reg.length = q := by
    simp [z, f, Data.comap, Reg.length, Signed.ArrayArithmetic.Reg.length]
  have hzm : (z.comap f).mem = x.mem := hmem
  have hquarter (t : ℕ) (ht : t < 4) : t * q + q ≤ 4 * q := by
    have hmul := Nat.mul_le_mul_right q (Nat.succ_le_of_lt ht)
    simpa only [Nat.succ_mul] using hmul
  have hq₁ := hquarter t₁ ht₁
  have hq₂ := hquarter t₂ ht₂
  obtain ⟨v, hv, values, frame, _⟩ := Signed.ArrayArithmetic.exec
    (decide (sign < 0)) (z.comap f) (fun j => u (t₁ * q + j)) (fun j => u (t₂ * q + j))
    hzl hbound
    (fun j hj => hu _ (by omega)) (fun j hj => hu _ (by omega))
    (by intro j hj; rw [hzm, hza, Nat.add_assoc]; exact hinput _ (by omega))
    (by intro j hj; rw [hzm, hzb, Nat.add_assoc]; exact hinput _ (by omega))
    (by rw [hza]; exact hw.of_le (by omega))
    (by rw [hzb]; exact hw.of_le (by omega))
    (by rw [hzo]; exact hw.of_le (by omega))
    (by
      rw [hza, hzo]
      rcases hsep with h | h
      · exact Or.inl (by omega)
      · exact Or.inr (Or.inl (by omega)))
    (by
      rw [hzb, hzo]
      rcases hsep with h | h
      · exact Or.inl (by omega)
      · exact Or.inr (Or.inl (by omega)))
  let y := v.extend f z
  have hvector : ExecWithin (w + 2)
      ((Signed.ArrayArithmetic.program (decide (sign < 0))).rename f) z y (26 * q + 4) :=
    hv.rename (Fin.castLE_injective _)
  have he : ExecWithin (w + 2) (form base dst t₁ t₂ sign) x y (26 * q + 12) := by
    simpa only [form, ite_eq_right hsign, f] using
      (hr.seq (hs.seq (hargs.seq hvector))).mono
        (by omega : 3 + (3 + (2 + (26 * q + 4))) ≤ 26 * q + 12)
  refine ⟨y, he, ?_, ?_, ?_⟩
  · intro j hj
    simpa only [y, Data.extend, hzo, decide_eq_true_eq] using values j hj
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
    have hit : i ≠ Reg.target := by intro h; subst i; contradiction
    have hil : i ≠ Reg.length := by intro h; subst i; contradiction
    simpa only [z, Data.set, Function.update_of_ne hit, Function.update_of_ne hil] using
      hshigh i hi htemp

end Cslib.Algorithms.WordRAM.Strassen
