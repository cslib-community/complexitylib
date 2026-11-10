/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct.Front
public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Product.Transfer

/-!
# Actual restoration of the original matrix, coordinate and threshold words

The unchanged native copy restores every original matrix/coordinate word and the native
length header from its protected snapshot. Two final instructions restore the additional
threshold word, which was retained in a high register before producer reuse.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct

open Cslib.WordRAM

/-- Actual restoration copy and threshold store, with their complete memory readback. -/
theorem exec_restoreInput {W L m t N Q : ℕ} (x : Data 160)
    (hp : QueriedProduct.Parameters L m N Q x) (ht : x.regs Reg.threshold = t)
    (hfit : Fits W (wordBudget L m t N Q)) :
    ∃ y, ExecWithin W restoreInput x y (7 * QueriedProduct.inputEnd m N Q + 12) ∧
      QueriedProduct.Parameters L m N Q y ∧
      y.mem = Function.update
        (ArrayCopy.copyPrefix x.mem (QueriedProduct.snapshotBase L m N Q) 0
          (QueriedProduct.inputEnd m N Q)) (QueriedProduct.inputEnd m N Q) t := by
  obtain ⟨u, hu, up, um⟩ := QueriedProduct.exec_restoreInput x hp (old_fits hfit)
  have ut : u.regs Reg.threshold = t := (hu.regs_eq (by decide)).trans ht
  let y := (u.set QueriedProduct.Reg.address (QueriedProduct.inputEnd m N Q)).write
    (QueriedProduct.inputEnd m N Q) t
  have hy : ExecWithin W restoreThreshold u y 2 := by
    ram_eval [restoreThreshold, y, up.inputSize, ut, QueriedProduct.Reg.address,
      QueriedProduct.Reg.inputSize, Reg.threshold, Fin.mk.injEq]
  refine ⟨y, (hu.seq hy).mono (by omega), up.of_frame ?_, ?_⟩
  · intro i hi
    have hnot : QueriedProduct.Reg.address ∉ QueriedProduct.parameterRegisters := by decide
    have hne : i ≠ QueriedProduct.Reg.address := by
      intro heq
      exact hnot (heq ▸ hi)
    simp only [y, Data.write_regs, Data.set_regs, Function.update_of_ne hne]
  · change Function.update u.mem _ t = _
    rw [um]

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct
