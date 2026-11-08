/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.CallableBox.Program

/-!
# Exact physical normalization after a pointer-gather product

The conservative pointer pilot retains both actual normalization loops, including the threshold
word. This boundary gives exact physical words and the absolute result pointer, rather than
only virtual residues.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PointerBoxProduct

open Cslib.WordRAM CallableProduct

/-- The unchanged charged threshold adjustment and original span-normalization loops. -/
@[expose] def finish : Code .standard 163 :=
  .seq CallableBoxProduct.includeThreshold (.seq restoreInput returnOutput)

/-- Normalize only the restored private input and returned answers, preserving outside memory. -/
theorem exec_finish {W b I Q O M : ℕ} (x : Data 163)
    (hb : x.regs Reg.base = b) (hI : x.regs Reg.inputSize = I)
    (hQ : x.regs Reg.queryCount = Q) (hO : x.regs Reg.output = O)
    (hmod : x.regs Reg.modulus = M) (hM : 0 < M) (hsep : I + 1 ≤ O)
    (original : ℕ → ℕ) (answers : Fin Q → ℕ)
    (hi : ∀ a < I + 1, x.mem (b + a) % M = original a)
    (hv : ∀ i : Fin Q, x.mem (b + (O + i.val)) % M = answers i)
    (hfit : Fits W (b + (I + 1) + O + Q + M + 8)) :
    ∃ y, ExecWithin W finish x y (2 + 7 * (I + 1) + 7 * Q + 14) ∧
      y.regs Reg.result = b + O ∧
      (∀ a < I + 1, y.mem (b + a) = original a) ∧
      (∀ i : Fin Q, y.mem (b + (O + i.val)) = answers i) ∧
      ∀ a, (a < b ∨ b + (I + 1) ≤ a) → (a < b + O ∨ b + O + Q ≤ a) →
        y.mem a = x.mem a := by
  let z := (x.set Reg.third 1).set Reg.inputSize (I + 1)
  have hz : ExecWithin W CallableBoxProduct.includeThreshold x z 2 := by
    ram_eval [CallableBoxProduct.includeThreshold, z, hI,
      hfit.of_le (show 1 ≤ b + (I + 1) + O + Q + M + 8 by omega),
      hfit.of_le (show I + 1 ≤ b + (I + 1) + O + Q + M + 8 by omega),
      Reg.third, Reg.inputSize, QueriedProduct.Reg.inputSize, Fin.mk.injEq]
  have zb : z.regs Reg.base = b := by
    simpa +decide [z, Reg.base, Reg.third, Reg.inputSize, QueriedProduct.Reg.inputSize,
      Function.update_apply] using hb
  have zm : z.regs Reg.modulus = M := by
    simpa +decide [z, Reg.modulus, Reg.third, Reg.inputSize, QueriedProduct.Reg.inputSize,
      Function.update_apply] using hmod
  have zq : z.regs Reg.queryCount = Q := by
    simpa +decide [z, Reg.queryCount, Reg.third, Reg.inputSize, QueriedProduct.Reg.inputSize,
      QueriedProduct.Reg.queryCount, Function.update_apply] using hQ
  have zo : z.regs Reg.output = O := by
    simpa +decide [z, Reg.output, Reg.third, Reg.inputSize, QueriedProduct.Reg.inputSize,
      QueriedProduct.Reg.output, Function.update_apply] using hO
  obtain ⟨s, hs, sm, sf⟩ := exec_restoreInput (n := I + 1) z zb (by simp [z]) zm hM
    (hfit.of_le (by omega))
  obtain ⟨y, hy, ym, yr, _⟩ := exec_returnOutput s
    ((sf _ (by decide)).trans zb) ((sf _ (by decide)).trans zo)
    ((sf _ (by decide)).trans zq) ((sf _ (by decide)).trans zm) hM
    (hfit.of_le (by omega))
  refine ⟨y, (hz.seq (hs.seq hy)).mono (by omega), yr, ?_, ?_, ?_⟩
  · intro a ha
    rw [ym, ArrayNormalize.normalizePrefix_outside _ _ _ _ _ (by omega), sm,
      ArrayNormalize.normalizePrefix_read _ _ _ _ _ ha]
    exact hi a ha
  · intro i
    rw [ym, show b + (O + i.val) = (b + O) + i.val by omega,
      ArrayNormalize.normalizePrefix_read _ _ _ _ _ i.isLt, sm,
      ArrayNormalize.normalizePrefix_outside _ _ _ _ _ (by omega)]
    simpa only [z, Data.set_mem, Nat.add_assoc] using hv i
  · intro a ha ho
    rw [ym, ArrayNormalize.normalizePrefix_outside _ _ _ _ _ (by omega), sm,
      ArrayNormalize.normalizePrefix_outside _ _ _ _ _ (by omega)]
    rfl

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PointerBoxProduct
