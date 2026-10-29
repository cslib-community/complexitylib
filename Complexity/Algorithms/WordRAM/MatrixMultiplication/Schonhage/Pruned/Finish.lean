/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Node

/-!
# Actual return after all ten child terms

## Main results

* `PrunedQuery.exec_node_finish`: read the completed frame and return through the real
  controller comparisons, preserving all memory.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery

open Cslib.WordRAM

/-- The stored term counter is read and compared with ten. The controller then either
terminates the root or selects the parent's accumulation phase, within 26 instructions. -/
theorem exec_node_finish {w L f a0 b0 d : ℕ} (x : Data registers)
    (hregs : KernelRegs L f a0 b0 x) (hd : x.regs level = d) (hdL : d ≤ L)
    (hm : x.regs mode = 1) (hterm : x.mem (f + 4 * d + 3) = 10)
    (hw : Fits w (8 * f + 64 * (L + 1) * 10 ^ L + 128)) :
    ∃ y, ExecWithin w step x y 26 ∧ KernelRegs L f a0 b0 y ∧ y.mem = x.mem ∧
      y.regs level = (if d = 0 then 0 else d - 1) ∧
      y.regs mode = (if d = 0 then 1 else 2) ∧
      y.regs active = (if d = 0 then 0 else x.regs active) ∧
      y.regs epoch = x.regs epoch := by
  have hpow : 1 ≤ (10 : ℕ) ^ L := Nat.one_le_pow L _ (by decide)
  have hL : L + 1 ≤ (L + 1) * 10 ^ L := by nlinarith only [hpow]
  have hmul : (d + 1) * 10 ^ L ≤ (L + 1) * 10 ^ L :=
    Nat.mul_le_mul_right _ (by omega)
  obtain ⟨u, hu, humem, _, _, _, _, hut, _, _, _, _, _, hureg⟩ :=
    exec_loadFrame x hregs.one_eq hregs.frameWidth_eq (hw.of_le (by
      rw [hregs.frames_eq, hregs.lists_eq, hregs.values_eq, hregs.span_eq, hd]
      nlinarith only [hpow, hL, hmul]))
  have fixed (i : Fin registers) (hi : ¬LoadFrameLocal i) : u.regs i = x.regs i :=
    hureg i hi
  have hut' : u.regs term = 10 := by simpa only [hregs.frames_eq, hd, hterm] using hut
  have hu0 := (fixed nil (by decide)).trans hregs.nil_eq
  have hu1 := (fixed one (by decide)).trans hregs.one_eq
  have hu10 := (fixed ten (by decide)).trans hregs.ten_eq
  have hum : u.regs mode = 1 := (fixed mode (by decide)).trans hm
  have hud : u.regs level = d := (fixed level (by decide)).trans hd
  obtain ⟨y, hy, hymem, hyl, hym, hya, _⟩ := exec_pop u hu0 hu1
    (hw.of_le (by rw [hud]; nlinarith only [hL, hdL]))
  have hcall : ExecWithin w dispatch u y 6 := hy.branch_neg
    (by simp only [Cond.holds_lt, hut', hu10, lt_self_iff_false, not_false_eq_true])
  have hbranch : ExecWithin w
      (ram[ if mode = nil then [ ⟪enter⟫ ] else [
        if mode = one then [ ⟪dispatch⟫ ] else [ ⟪accumulate⟫ ] ] ]) u y 9 :=
    (hcall.branch_pos (by simp only [Cond.holds_eq, hum, hu1])).branch_neg
      (by simp only [Cond.holds_eq, hum, hu0]; decide)
  have he : ExecWithin w step x y 26 := hu.seq hbranch
  exact ⟨y, he, hregs.of_step he, hymem.trans humem,
    by simpa only [hud] using hyl, by simpa only [hud, hum] using hym,
    by simpa only [hud, fixed active (by decide)] using hya,
    (hy.regs_eq (by decide : pop.Preserves epoch)).trans (fixed epoch (by decide))⟩

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery
