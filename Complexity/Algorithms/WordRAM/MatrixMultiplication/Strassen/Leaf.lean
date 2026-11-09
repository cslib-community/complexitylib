/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

import Complexity.Computability.WordRAM.SymbolicExec.CanonicalCall
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Strassen.Control
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.CyclicConvolution.Exec

/-!
# Charged native Strassen scalar leaves

The leaf transition copies real controller arguments into the low helper bank, executes the
actual cyclic kernel, and returns through the actual explicit stack. Its numerical premises
concern only original coefficient envelopes, pointers and the current frame. This internal
composition API assumes no product answer, run or cost certificate.
-/

public section

namespace Cslib.Algorithms.WordRAM.Strassen

open Cslib.WordRAM Cslib.WordRAM.Signed Cslib.CyclicIntRing

/-- A scalar leaf, including four argument copies, all coefficient operations, and return.
Both input arrays are preserved. The frame and active flag implement the real parent return. -/
theorem exec_leaf {w p A B : ℕ} (x : Data 64) (u v : ℕ → ℤ)
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
      x.regs Reg.output + p ≤ x.regs Reg.inputB)
    (h7 : x.regs Reg.frameWidth = 7) (hf : Fits (w + 2) (x.regs Reg.frame)) :
    ∃ y, ExecWithin (w + 2) leaf x y (42 * p * p + 9 * p + 11) ∧
      (∀ r < p, y.mem (x.regs Reg.output + r) = encode (convolution p u v r)) ∧
      (∀ a, a < x.regs Reg.output ∨ x.regs Reg.output + p ≤ a → y.mem a = x.mem a) ∧
      y.regs Reg.frame =
        (if x.regs Reg.frames < x.regs Reg.frame then x.regs Reg.frame - 7
          else x.regs Reg.frame) ∧
      y.regs Reg.active =
        (if x.regs Reg.frames < x.regs Reg.frame then x.regs Reg.active else 0) ∧
      ∀ i, 32 ≤ i.val → i ≠ Reg.frame → i ≠ Reg.active → y.regs i = x.regs i := by
  unfold leaf
  wram_exec [hlen]
  wram_call (CyclicConvolution.exec _ u v
    (by wram_simp [CyclicConvolution.Reg.length]) hbound hu hv
    (by wram_simp [CyclicConvolution.Reg.inputA]; exact hA)
    (by wram_simp [CyclicConvolution.Reg.inputB]; exact hB) h2p
    (by wram_simp [CyclicConvolution.Reg.inputA]; exact ha)
    (by wram_simp [CyclicConvolution.Reg.inputB]; exact hb)
    (by wram_simp [CyclicConvolution.Reg.output]; exact hout)
    (by wram_simp [CyclicConvolution.Reg.inputA, CyclicConvolution.Reg.output]; exact hdisjA)
    (by wram_simp [CyclicConvolution.Reg.inputB, CyclicConvolution.Reg.output]; exact hdisjB))
    canonical (Fin.castLE_injective _) with s ⟨values, frame, _⟩
  wram_call (exec_pop _ (by wram_simp [h7]) (by wram_simp [hf])) with
    y ⟨hym, hyf, hya, hyr⟩
  wram_simp [CyclicConvolution.Reg.output] at values frame
  wram_simp at hym
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr
    rw [hym]
    exact values r hr
  · intro a ha'
    rw [hym]
    exact frame a ha'
  · wram_simp [hyf]
  · wram_simp [hya]
  · intro i hi hframe hactive
    rw [hyr i hframe hactive, Data.extend_regs_of_forall_ne _ _ i (by
      intro j hj
      have hv := congrArg Fin.val hj
      change j.val = i.val at hv
      omega)]
    simp only [Data.set_regs,
      Function.update_of_ne (show i ≠ Reg.length by intro h; subst i; contradiction),
      Function.update_of_ne (show i ≠ Reg.target by intro h; subst i; contradiction),
      Function.update_of_ne (show i ≠ Reg.operandB by intro h; subst i; contradiction),
      Function.update_of_ne (show i ≠ Reg.operandA by intro h; subst i; contradiction)]

end Cslib.Algorithms.WordRAM.Strassen
