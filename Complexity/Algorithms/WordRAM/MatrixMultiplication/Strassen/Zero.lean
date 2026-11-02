/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Strassen.State
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Strassen.LeafStep

/-!
# Base case of the actual native Strassen traversal induction

A ready scalar frame executes its real native leaf iteration and returns to the parent or
finishes the root. The continuation form accounts for the enclosing native loop overhead;
the final root theorem closes it with the proved zero active flag and the charged loop exit.
All arithmetic and frame fits follow from original scalar/pointer envelopes.
-/

public section

namespace Cslib.Algorithms.WordRAM.Strassen

open Cslib.WordRAM Cslib.WordRAM.Signed

/-- The all-coefficient native scalar node, with its actual return and complete footprint.
No multiplication or execution field occurs in its hypotheses. -/
theorem exec_ready_zero {w p A B a b out scratch frames frame : ℕ}
    (x : Data 64) (u v : ℕ → ℤ) (hx : NodeReady p 0 a b out scratch frames frame x)
    (hl : NodeLayout p 0 a b out scratch frames frame)
    (hu : ∀ i < p, (u i).natAbs ≤ A) (hv : ∀ i < p, (v i).natAbs ≤ B)
    (hleft : ∀ i < p, x.mem (a + i) = encode (u i))
    (hright : ∀ i < p, x.mem (b + i) = encode (v i))
    (hmag : GenericRAM.Signed.Fits w (magnitudeBound p A B 0 : ℤ))
    (haddr : Fits (w + 2) (addressBound frames frame 0)) :
    ∃ y, NodeResult p 0 out scratch frames frame u v x y ∧
      ∀ z T, ExecWithin (w + 2) controller y z T →
        ExecWithin (w + 2) controller x z (traceBudget p 0 + T) := by
  have hs : scratch + p ≤ frames := by simpa only [pow_zero, Nat.one_mul] using hl.scratch_before
  have ha : a + p ≤ scratch := by simpa only [pow_zero, Nat.one_mul] using hl.left_before
  have hb : b + p ≤ scratch := by simpa only [pow_zero, Nat.one_mul] using hl.right_before
  have ho : out + p ≤ scratch := by simpa only [pow_zero, Nat.one_mul] using hl.output_before
  have hf := hl.frames_before
  have hcyclic : GenericRAM.Signed.Fits w (CyclicConvolution.magnitudeBound p A B : ℤ) :=
    hmag.of_natAbs_le (by
      rw [Int.natAbs_natCast]
      exact scalar_le_magnitudeBound p A B)
  obtain ⟨y, hy, values, outside, hyframe, hyactive, hyregs⟩ := exec_step_leaf x u v
    hx.zero_eq hx.one_eq hx.frameWidth_eq hx.depth_eq
    (by simpa only [hx.frame_eq] using hx.frame_words)
    (by rw [hx.frame_eq]; exact haddr.of_le (by unfold addressBound; omega))
    hx.modulus_eq hcyclic hu hv
    (by simpa only [hx.inputA_eq] using hleft)
    (by simpa only [hx.inputB_eq] using hright)
    (haddr.of_le (by unfold addressBound; omega))
    (by rw [hx.inputA_eq]; exact haddr.of_le (by unfold addressBound; omega))
    (by rw [hx.inputB_eq]; exact haddr.of_le (by unfold addressBound; omega))
    (by rw [hx.output_eq]; exact haddr.of_le (by unfold addressBound; omega))
    (by simpa only [hx.inputA_eq, hx.output_eq, pow_zero, Nat.one_mul] using hl.left_disjoint)
    (by simpa only [hx.inputB_eq, hx.output_eq, pow_zero, Nat.one_mul] using hl.right_disjoint)
  refine ⟨y, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [hx.output_eq, pow_zero, Nat.one_mul,
        Cslib.Algorithms.MatrixMultiplication.Strassen.multiply] using values
    · intro q hq
      have hno : ¬(out ≤ q ∧ q < out + p) := by
        intro h
        exact hq (Or.inl (by simpa only [pow_zero, Nat.one_mul] using h))
      exact outside q (by rw [hx.output_eq]; omega)
    · exact (hyregs Reg.output (by decide) (by decide) (by decide) (by decide)).trans hx.output_eq
    · exact (hyregs Reg.modulus (by decide) (by decide) (by decide) (by decide)).trans hx.modulus_eq
    · exact (hyregs Reg.frames (by decide) (by decide) (by decide) (by decide)).trans hx.frames_eq
    · simpa only [hx.frames_eq, hx.frame_eq] using hyframe
    · simpa only [hx.frames_eq, hx.frame_eq, hx.active_eq] using hyactive
    · exact (hyregs Reg.zero (by decide) (by decide) (by decide) (by decide)).trans hx.zero_eq
    · exact (hyregs Reg.one (by decide) (by decide) (by decide) (by decide)).trans hx.one_eq
    · exact (hyregs Reg.four (by decide) (by decide) (by decide) (by decide)).trans hx.four_eq
    · exact (hyregs Reg.frameWidth (by decide) (by decide) (by decide) (by decide)).trans
        hx.frameWidth_eq
  · intro z T hz
    have hc : (Cond.lt Reg.zero Reg.active).Holds x := by
      simp only [Cond.holds_lt, hx.zero_eq, hx.active_eq]
      decide
    exact (ExecWithin.loop_iter hc hy hz).mono (by simp only [traceBudget]; omega)

end Cslib.Algorithms.WordRAM.Strassen
