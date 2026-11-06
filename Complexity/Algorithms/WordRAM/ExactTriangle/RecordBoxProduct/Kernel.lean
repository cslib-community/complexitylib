/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

import Complexity.Computability.WordRAM.Call
public import Complexity.Algorithms.WordRAM.ExactTriangle.RecordBoxProduct.Program

/-!
# Checked invocation of the actual callable box product

Original local words derive the translated execution and its charged native ledger.
The appended threshold is restored with the complete local input. Producer and
adapter registers outside the explicit result/callee bank survive the invocation.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.RecordBoxProduct

open Cslib.WordRAM
open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open RecordProduct

/-- The concrete original-input callee derives its execution from the matrices and coordinate
occurrences. No execution or time certificate is accepted by this invocation rule. -/
theorem exec_invoke {W b m N : ℕ}
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ)
    (qs : List (Fin N × Fin N)) (x : Data 320) (hb : x.regs Reg.base = b)
    (hinput : ∀ a, a < QueriedProduct.inputEnd m N qs.length + 1 →
      x.mem (b + a) =
        (State.init (BoxProduct.input true (21 * m) (m / 9) X Y qs) : State 160).data.mem a)
    (hX : ∀ i k, 0 ≤ X i k ∧ X i k ≤ 1) (hY : ∀ k j, 0 ≤ Y k j ∧ Y k j ≤ 1)
    (hN : D m ^ 18 ≤ N) (hfit : Fits W (b + 4 * CallableProduct.windowSize N qs.length + 1024)) :
    ∃ y, ExecWithin W invoke x y (CallableBoxProduct.timeBound m (m / 9) qs + 2) ∧
      y.regs Reg.result = b + QueriedProduct.outputBase (21 * m) m N qs.length ∧
      (∀ i : Fin qs.length,
        y.mem (b + (QueriedProduct.outputBase (21 * m) m N qs.length + i.val)) =
          Signed.encode ((X * Y) (qs.get i).1 (qs.get i).2)) ∧
      (∀ a, a < QueriedProduct.inputEnd m N qs.length + 1 → y.mem (b + a) = x.mem (b + a)) ∧
      (∀ a, a < b ∨ b + CallableProduct.windowSize N qs.length ≤ a → y.mem a = x.mem a) ∧
      ∀ i : Fin 320, i.val < 128 → i ≠ Reg.result → y.regs i = x.regs i := by
  let z := x.set (calleeBank CallableProduct.Reg.base) b
  have hz : ExecWithin (B := .standard) W
      (.op (.copy (calleeBank CallableProduct.Reg.base) Reg.base)) x z 1 := by
    simpa only [z, hb] using
      (ExecWithin.copy (w := W) (x := x) (d := calleeBank CallableProduct.Reg.base)
        (s := Reg.base))
  have zb : (z.comap calleeBank).regs CallableProduct.Reg.base = b := by simp [z]
  obtain ⟨c, hc, ⟨cr, _, _, av, ai, af⟩, hframe⟩ :=
    ExecWithin.rename_post calleeBank_injective (
      CallableBoxProduct.exec X Y qs (z.comap calleeBank) zb hinput hX hY
        (Nat.div_le_self _ _) hN hfit)
  change c.regs (calleeBank CallableProduct.Reg.result) = _ at cr
  let y := c.set Reg.result (b + QueriedProduct.outputBase (21 * m) m N qs.length)
  have hy : ExecWithin (B := .standard) W
      (.op (.copy Reg.result (calleeBank CallableProduct.Reg.result))) c y 1 := by
    simpa only [y, cr] using (ExecWithin.copy (w := W) (x := c) (d := Reg.result)
      (s := calleeBank CallableProduct.Reg.result))
  refine ⟨y, ?_, by simp [y], av, ai, af, ?_⟩
  · exact (hz.seq (hc.seq hy)).mono (by omega)
  · intro i hi hne
    have hbank (j) : calleeBank j ≠ i := by
      intro hj
      have h := congrArg Fin.val hj
      change 128 + j.val = i.val at h
      omega
    have hiz : i ≠ calleeBank CallableProduct.Reg.base := (hbank _).symm
    rw [Data.set_regs, Function.update_of_ne hne, hframe i hbank]
    simp only [z, Data.set_regs, Function.update_of_ne hiz]

end Cslib.Algorithms.WordRAM.ExactTriangle.RecordBoxProduct
