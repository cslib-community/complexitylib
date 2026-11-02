/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Strassen.State
import Mathlib.Tactic.FinCases

/-!
# Actual parent-frame restoration after a Strassen child

The child footprint protects the seven earlier parent words. The real fourteen-instruction
load then restores all parent parameters and the saved return phase. In the final induction,
the child result is established recursively for the same native controller, and these saved
words come from the actual push. Neither is an additional argument to the program.
-/

public section

namespace Cslib.Algorithms.WordRAM.Strassen

open Cslib.WordRAM

/-- Every earlier parent word is outside the child's actual write footprint. -/
theorem NodeResult.parent_frame {p k a b out scratch frames frame : ℕ}
    {u v : ℕ → ℤ} {x y : Data 64}
    (hl : NodeLayout p (k + 1) a b out scratch frames frame)
    (h : NodeResult p k (scratch + 2 * (4 ^ k * p)) (scratch + 3 * (4 ^ k * p))
      frames (frame + 7) u v x y) (j : Fin 7) :
    y.mem (frame + j.val) = x.mem (frame + j.val) := by
  apply h.outside
  have hs := hl.scratch_before
  have hf := hl.frames_before
  have hsize : 4 ^ (k + 1) * p = 4 * (4 ^ k * p) := by rw [pow_succ]; ring
  rw [hsize] at hs
  unfold NodeWrites
  omega

/-- Read the real saved parent frame after the actual child return. Every parent parameter,
return phase and frame-readback fact follows from the charged loads and protected words. -/
theorem exec_restore_parent {w p k a b out scratch frames frame : ℕ}
    (phase : Fin 7) (parent child returned : Data 64) (u v : ℕ → ℤ)
    (hp : NodeHeader p (k + 1) a b out scratch frames frame parent)
    (hl : NodeLayout p (k + 1) a b out scratch frames frame)
    (hchild : NodeResult p k (scratch + 2 * (4 ^ k * p)) (scratch + 3 * (4 ^ k * p))
      frames (frame + 7) u v child returned)
    (hwords : ∀ j : Fin 7, child.mem (frame + j.val) =
      if j.val = 6 then phase.val + 1 else parent.regs (field j))
    (haddr : Fits w (addressBound frames frame (k + 1))) :
    ∃ y, ExecWithin w loadFrame returned y 14 ∧ y.mem = returned.mem ∧
      NodeHeader p (k + 1) a b out scratch frames frame y ∧
      y.regs Reg.phase = phase.val + 1 ∧
      (∀ j : Fin 7, y.mem (frame + j.val) = y.regs (field j)) ∧
      ∀ i, ¬LoadLocal i → y.regs i = returned.regs i := by
  have hf := hl.frames_before
  have hlt : frames < frame + 7 := by omega
  have hreturn : returned.regs Reg.frame = frame := by
    simpa only [hlt, ite_true, Nat.add_sub_cancel_right] using hchild.frame_eq
  obtain ⟨y, hy, hm, fields, regs⟩ := exec_loadFrame returned hchild.one_eq
    (by rw [hreturn]; exact haddr.of_le (by unfold addressBound; omega))
  have hfields (j : Fin 7) : y.regs (field j) =
      if j.val = 6 then phase.val + 1 else parent.regs (field j) := by
    rw [fields j, hreturn, hchild.parent_frame hl j, hwords j]
  have hyphase : y.regs Reg.phase = phase.val + 1 := by
    simpa [field] using hfields 6
  have hyheader : NodeHeader p (k + 1) a b out scratch frames frame y := {
    inputA_eq := by simpa [field, hp.inputA_eq] using hfields 0
    inputB_eq := by simpa [field, hp.inputB_eq] using hfields 1
    output_eq := by simpa [field, hp.output_eq] using hfields 2
    scratch_eq := by simpa [field, hp.scratch_eq] using hfields 3
    depth_eq := by simpa [field, hp.depth_eq] using hfields 4
    size_eq := by simpa [field, hp.size_eq] using hfields 5
    modulus_eq := (regs Reg.modulus (by decide)).trans hchild.modulus_eq
    frames_eq := (regs Reg.frames (by decide)).trans hchild.frames_eq
    frame_eq := (regs Reg.frame (by decide)).trans hreturn
    active_eq := (regs Reg.active (by decide)).trans (by
      simpa only [hlt, ite_true] using hchild.active_eq)
    zero_eq := (regs Reg.zero (by decide)).trans hchild.zero_eq
    one_eq := (regs Reg.one (by decide)).trans hchild.one_eq
    four_eq := (regs Reg.four (by decide)).trans hchild.four_eq
    frameWidth_eq := (regs Reg.frameWidth (by decide)).trans hchild.frameWidth_eq }
  refine ⟨y, hy, hm, hyheader, hyphase, ?_, regs⟩
  intro j
  rw [hm, ← hreturn, fields j]

end Cslib.Algorithms.WordRAM.Strassen
