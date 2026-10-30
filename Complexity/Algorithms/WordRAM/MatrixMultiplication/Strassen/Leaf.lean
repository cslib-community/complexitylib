/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

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
  let z := (((x.set Reg.operandA (x.regs Reg.inputA)).set Reg.operandB
    (x.regs Reg.inputB)).set Reg.target (x.regs Reg.output)).set Reg.length p
  have hargs : ExecWithin (B := .standard) (w + 2)
      (ram[ Reg.operandA ← Reg.inputA; Reg.operandB ← Reg.inputB;
        Reg.target ← Reg.output; Reg.length ← Reg.modulus ]) x z 4 := by
    ram_eval [z, hlen, Reg.operandA, Reg.operandB, Reg.target, Reg.length,
      Reg.inputA, Reg.inputB, Reg.output, Reg.modulus]
  let f : Fin 32 → Fin 64 := Fin.castLE (by decide)
  have hzm : z.mem = x.mem := rfl
  have hza : (z.comap f).regs CyclicConvolution.Reg.inputA = x.regs Reg.inputA := by
    simp +decide [z, f, Data.comap, Reg.operandA, Reg.operandB, Reg.target, Reg.length,
      CyclicConvolution.Reg.inputA]
  have hzb : (z.comap f).regs CyclicConvolution.Reg.inputB = x.regs Reg.inputB := by
    simp +decide [z, f, Data.comap, Reg.operandA, Reg.operandB, Reg.target, Reg.length,
      CyclicConvolution.Reg.inputB]
  have hzo : (z.comap f).regs CyclicConvolution.Reg.output = x.regs Reg.output := by
    simp +decide [z, f, Data.comap, Reg.operandA, Reg.operandB, Reg.target, Reg.length,
      CyclicConvolution.Reg.output]
  obtain ⟨t, ht, values, frame, _⟩ := CyclicConvolution.exec (z.comap f) u v
    (by simp [z, f, Data.comap, Reg.length, CyclicConvolution.Reg.length]) hbound hu hv
    (by simpa only [Data.comap_mem, hzm, hza] using hA)
    (by simpa only [Data.comap_mem, hzm, hzb] using hB) h2p
    (by simpa only [hza] using ha) (by simpa only [hzb] using hb)
    (by simpa only [hzo] using hout) (by simpa only [hza, hzo] using hdisjA)
    (by simpa only [hzb, hzo] using hdisjB)
  let s := t.extend f z
  have hkernel : ExecWithin (w + 2)
      (CyclicConvolution.program.rename f) z s (42 * p * p + 9 * p + 4) :=
    ht.rename (Fin.castLE_injective _)
  have hs (i : Fin 64) (hi : 32 ≤ i.val) : s.regs i = x.regs i := by
    have hn : ¬∃ j, f j = i := by
      rintro ⟨j, hj⟩
      have he := congrArg Fin.val hj
      change j.val = i.val at he
      omega
    have he : s.regs i = z.regs i := Function.extend_apply' _ _ _ hn
    apply he.trans
    simp only [z, Data.set,
      Function.update_of_ne (show i ≠ Reg.length by intro h; subst i; contradiction),
      Function.update_of_ne (show i ≠ Reg.target by intro h; subst i; contradiction),
      Function.update_of_ne (show i ≠ Reg.operandB by intro h; subst i; contradiction),
      Function.update_of_ne (show i ≠ Reg.operandA by intro h; subst i; contradiction)]
  obtain ⟨y, hy, hym, hyf, hya, hyr⟩ := exec_pop s
    ((hs Reg.frameWidth (by decide)).trans h7)
    (by simpa only [hs Reg.frame (by decide)] using hf)
  have he : ExecWithin (w + 2) leaf x y (42 * p * p + 9 * p + 11) :=
    (hargs.seq (hkernel.seq hy)).mono (by omega)
  refine ⟨y, he, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr
    rw [hym]
    simpa only [s, Data.extend, Data.comap_mem, hzo] using values r hr
  · intro a ha'
    rw [hym]
    simpa only [s, Data.extend, Data.comap_mem, hzm] using frame a (by simpa only [hzo] using ha')
  · simpa only [hs Reg.frame (by decide), hs Reg.frames (by decide)] using hyf
  · simpa only [hs Reg.frame (by decide), hs Reg.frames (by decide),
      hs Reg.active (by decide)] using hya
  · intro i hi hframe hactive
    exact (hyr i hframe hactive).trans (hs i hi)

end Cslib.Algorithms.WordRAM.Strassen
