/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Strassen.Leaf

/-!
# Actual leaf iteration of the explicit Strassen controller

This composes the real frame loads, the depth comparison, cyclic coefficient multiplication
and real parent/root return. The internal frame equality is established by native setup or
push; the complete counter does not accept it as input data or an assumed execution contract.
-/

public section

namespace Cslib.Algorithms.WordRAM.Strassen

open Cslib.WordRAM Cslib.WordRAM.Signed Cslib.CyclicIntRing

/-- A loaded scalar frame executes a complete native controller step, including the actual
depth dispatch and every frame read. All original coefficient/magnitude premises are explicit. -/
theorem exec_step_leaf {w p A B : ℕ} (x : Data 64) (u v : ℕ → ℤ)
    (h0 : x.regs Reg.zero = 0) (h1 : x.regs Reg.one = 1)
    (h7 : x.regs Reg.frameWidth = 7) (hd : x.regs Reg.depth = 0)
    (hframe : ∀ j : Fin 7, x.mem (x.regs Reg.frame + j.val) = x.regs (field j))
    (hptr : Fits (w + 2) (x.regs Reg.frame + 7))
    (hlen : x.regs Reg.modulus = p)
    (hbound : GenericRAM.Signed.Fits w (CyclicConvolution.magnitudeBound p A B : ℤ))
    (hu : ∀ i < p, (u i).natAbs ≤ A) (hv : ∀ i < p, (v i).natAbs ≤ B)
    (hA : ∀ i < p, x.mem (x.regs Reg.inputA + i) = encode (u i))
    (hB : ∀ i < p, x.mem (x.regs Reg.inputB + i) = encode (v i))
    (h2p : Fits (w + 2) (2 * p))
    (ha : Fits (w + 2) (x.regs Reg.inputA + p))
    (hb : Fits (w + 2) (x.regs Reg.inputB + p))
    (hout : Fits (w + 2) (x.regs Reg.output + p))
    (hdisjA : x.regs Reg.inputA + p ≤ x.regs Reg.output ∨
      x.regs Reg.output + p ≤ x.regs Reg.inputA)
    (hdisjB : x.regs Reg.inputB + p ≤ x.regs Reg.output ∨
      x.regs Reg.output + p ≤ x.regs Reg.inputB) :
    ∃ y, ExecWithin (w + 2) step x y (42 * p * p + 9 * p + 26) ∧
      (∀ i < p, y.mem (x.regs Reg.output + i) = encode (convolution p u v i)) ∧
      (∀ a, a < x.regs Reg.output ∨ x.regs Reg.output + p ≤ a → y.mem a = x.mem a) ∧
      y.regs Reg.frame =
        (if x.regs Reg.frames < x.regs Reg.frame then x.regs Reg.frame - 7
          else x.regs Reg.frame) ∧
      y.regs Reg.active =
        (if x.regs Reg.frames < x.regs Reg.frame then x.regs Reg.active else 0) ∧
      ∀ i, 32 ≤ i.val → i ≠ Reg.address → i ≠ Reg.frame → i ≠ Reg.active →
        y.regs i = x.regs i := by
  obtain ⟨s, hs, hm, hr⟩ := exec_loadCurrent x h1 hptr hframe
  obtain ⟨y, hy, values, frame, hyf, hya, hyr⟩ := exec_leaf s u v
    ((hr Reg.modulus (by decide)).trans hlen) hbound hu hv
    (by simpa only [hm, hr Reg.inputA (by decide)] using hA)
    (by simpa only [hm, hr Reg.inputB (by decide)] using hB) h2p
    (by simpa only [hr Reg.inputA (by decide)] using ha)
    (by simpa only [hr Reg.inputB (by decide)] using hb)
    (by simpa only [hr Reg.output (by decide)] using hout)
    (by simpa only [hr Reg.inputA (by decide), hr Reg.output (by decide)] using hdisjA)
    (by simpa only [hr Reg.inputB (by decide), hr Reg.output (by decide)] using hdisjB)
    ((hr Reg.frameWidth (by decide)).trans h7)
    (by rw [hr Reg.frame (by decide)]; exact hptr.of_le (by omega))
  have he : ExecWithin (w + 2) step x y (42 * p * p + 9 * p + 26) := by
    have hc : (Cond.eq Reg.depth Reg.zero).Holds s := by
      simp only [Cond.holds_eq, hr Reg.depth (by decide), hr Reg.zero (by decide), hd, h0]
    exact (hs.seq (.branch_pos hc hy)).mono (by omega)
  refine ⟨y, he, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hr Reg.output (by decide)] using values
  · simpa only [hr Reg.output (by decide), hm] using frame
  · simpa only [hr Reg.frames (by decide), hr Reg.frame (by decide)] using hyf
  · simpa only [hr Reg.frames (by decide), hr Reg.frame (by decide),
      hr Reg.active (by decide)] using hya
  · intro i hi haddr hframe hactive
    exact (hyr i hi hframe hactive).trans (hr i haddr)

end Cslib.Algorithms.WordRAM.Strassen
