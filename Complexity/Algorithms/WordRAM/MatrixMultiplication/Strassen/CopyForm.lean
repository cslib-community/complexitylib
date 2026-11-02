/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Strassen.Quadrant

/-!
# Actual single-quadrant Strassen operand forms

The zero-sign form is a real call to the existing copying loop, not a pointer or layout
oracle. Both disjoint address orders are admitted. The source is one of the current matrix
quarters and the destination is the actual caller-provided child operand buffer.
These are internal stage interfaces for composing the full explicit-stack proof.
-/

public section

namespace Cslib.Algorithms.WordRAM.Strassen

open Cslib.WordRAM

/-- Copy one real quadrant, including its computed source pointer, argument setup and every
native copy-loop instruction. All high controller fields except the offset temporary survive. -/
theorem exec_copyForm {w q t : ℕ} (base dst : Fin 64) (x : Data 64)
    (hd : 32 ≤ dst.val)
    (hbt : base ≠ Reg.temporary) (hdt : dst ≠ Reg.temporary)
    (hq : x.regs Reg.quarter = q) (ht : t < 4)
    (hw : Fits w (x.regs base + 4 * q + x.regs dst + q + 8))
    (hsep : x.regs base + 4 * q ≤ x.regs dst ∨ x.regs dst + q ≤ x.regs base) :
    ∃ y, ExecWithin w (form base dst t 0 0) x y (7 * q + 9) ∧
      (∀ j < q, y.mem (x.regs dst + j) = x.mem (x.regs base + t * q + j)) ∧
      (∀ a, a < x.regs dst ∨ x.regs dst + q ≤ a → y.mem a = x.mem a) ∧
      ∀ i, 32 ≤ i.val → i ≠ Reg.temporary → y.regs i = x.regs i := by
  have hqfit : Fits w (x.regs base + 4 * x.regs Reg.quarter + 4) := by
    rw [hq]
    exact hw.of_le (by omega)
  obtain ⟨s, hs, hsm, hsrc, hsr⟩ := exec_quadrant base Reg.copySource x hbt ht hqfit
  have hhigh (i : Fin 64) (hi : 32 ≤ i.val) (htemp : i ≠ Reg.temporary) :
      s.regs i = x.regs i := hsr i (by intro he; subst i; contradiction) htemp
  have hsq := (hhigh Reg.quarter (by decide) (by decide)).trans hq
  have hsd := hhigh dst hd hdt
  have hss : s.regs Reg.copySource = x.regs base + t * q := by simpa only [hq] using hsrc
  let z := (s.set Reg.copyTarget (x.regs dst)).set Reg.copyLength q
  have hargs : ExecWithin (B := .standard) w
      (ram[ Reg.copyTarget ← dst; Reg.copyLength ← Reg.quarter ]) s z 2 := by
    ram_eval [z, hsq, hsd, Reg.copyTarget, Reg.copyLength]
  let f : Fin 7 → Fin 64 := Fin.castLE (by decide)
  have hzs : (z.comap f).regs ArrayCopy.src = x.regs base + t * q := by
    simpa +decide [z, f, Data.comap, Reg.copyTarget, Reg.copyLength,
      Reg.copySource, ArrayCopy.src] using hss
  have hzd : (z.comap f).regs ArrayCopy.dst = x.regs dst := by
    simp +decide [z, f, Data.comap, Reg.copyTarget, Reg.copyLength, ArrayCopy.dst]
  have hzl : (z.comap f).regs ArrayCopy.len = q := by
    simp [z, f, Data.comap, Reg.copyLength, ArrayCopy.len]
  have hquarter : t * q + q ≤ 4 * q := by
    have hmul := Nat.mul_le_mul_right q (Nat.succ_le_of_lt ht)
    simpa only [Nat.succ_mul] using hmul
  obtain ⟨u, hu, hum, _, _, _⟩ := ArrayCopy.exec_of_separated_or_eq (z.comap f)
    (hw.of_le (by omega))
    (by rw [hzs, hzl]; exact hw.of_le (by omega))
    (by rw [hzd, hzl]; exact hw.of_le (by omega))
    (by
      rw [hzs, hzd, hzl]
      rcases hsep with h | h
      · exact Or.inl (by omega)
      · exact Or.inr (Or.inl (by omega)))
  let y := u.extend f z
  have hcopy : ExecWithin w (ArrayCopy.program.rename f) z y (7 * q + 4) := by
    simpa only [hzl] using hu.rename (Fin.castLE_injective _)
  have he : ExecWithin w (form base dst t 0 0) x y (7 * q + 9) := by
    simpa only [form, ite_true, f] using
      (hs.seq (hargs.seq hcopy)).mono (by omega : 3 + (2 + (7 * q + 4)) ≤ 7 * q + 9)
  have hym : y.mem = ArrayCopy.copyPrefix x.mem (x.regs base + t * q) (x.regs dst) q := by
    rw [hzs, hzd, hzl] at hum
    have hzm : z.mem = x.mem := hsm
    simpa only [y, Data.extend, Data.comap_mem, hzm] using hum
  refine ⟨y, he, ?_, ?_, ?_⟩
  · intro j hj
    rw [hym]
    simpa only [Nat.add_assoc] using ArrayCopy.copyPrefix_read (mem := x.mem)
      (src := x.regs base + t * q) (dst := x.regs dst) hj
  · intro a ha
    rw [hym]
    exact ArrayCopy.copyPrefix_outside (by omega)
  · intro i hi htemp
    have hn : ¬∃ j, f j = i := by
      rintro ⟨j, hj⟩
      have hv := congrArg Fin.val hj
      change j.val = i.val at hv
      omega
    have hyi : y.regs i = z.regs i := Function.extend_apply' _ _ _ hn
    apply hyi.trans
    have hi1 : i ≠ Reg.copyTarget := by intro h; subst i; contradiction
    have hi2 : i ≠ Reg.copyLength := by intro h; subst i; contradiction
    simpa only [z, Data.set, Function.update_of_ne hi1, Function.update_of_ne hi2] using
      hhigh i hi htemp

end Cslib.Algorithms.WordRAM.Strassen
