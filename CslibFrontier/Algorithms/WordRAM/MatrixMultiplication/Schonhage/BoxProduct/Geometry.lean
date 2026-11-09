/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct.State


/-!
# One actual shared box-geometry construction for all tiles

The constructor consumes original depth, inner count, threshold and an actual directory
pointer. Its computed records, retained-value base and compact count are saved in the high
bank. No assumed table or geometry execution is supplied to this stage.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct

open Cslib.WordRAM Cslib.Algorithms.MatrixMultiplication.Schonhage

set_option maxRecDepth 4096 in
-- Fixed 160-register frame checks unfold the existing 32-member caller register set.
/-- Construct shared geometry exactly once, save its actual addresses/count and initialize
the reusable sparse-result allocation and tile index. -/
theorem exec_prepareGeometry {w L m t N Q : ℕ} (x : Data 160)
    (hp : QueriedProduct.Parameters L m N Q x) (ht : x.regs Reg.threshold = t)
    (hfit : Fits w (wordBudget L m t N Q)) :
    ∃ y, ExecWithin w prepareGeometry x y (BoxTable.geometryTime L m t + 17) ∧
      QueriedProduct.Parameters L m N Q y ∧ Parameters L m t N Q y ∧
      y.regs QueriedProduct.Reg.index = 0 ∧ Geometry L m t N Q y.mem ∧
      (∀ p, ¬(directoryBase L m N Q ≤ p ∧ p < valueBase L m t N Q) →
        y.mem p = x.mem p) := by
  let D := directoryBase L m N Q
  let R := recordBase L m t N Q
  let V := valueBase L m t N Q
  let K := (boxes L m t).card
  let u := ((((x.set Reg.directory D).set (boxBank BoxTable.Reg.levels) L).set
    (boxBank BoxTable.Reg.inner) m).set (boxBank BoxTable.Reg.threshold) t).set
      (boxBank BoxTable.Reg.directory) D
  have hu : ExecWithin w geometryHead x u 5 := by
    ram_eval [geometryHead, u, D, directoryBase, hp.memoryLimit, hp.depth, hp.inner, ht,
      boxBank, Reg.directory, Reg.threshold, BoxTable.Reg.levels, BoxTable.Reg.inner,
      BoxTable.Reg.threshold, BoxTable.Reg.directory, Fin.mk.injEq, Fin.val_ofNat, Fin.val_natCast]
  have hT : 10 ^ L ≤ (L + 1) * 10 ^ L := Nat.le_mul_of_pos_left _ (by omega)
  have up : QueriedProduct.Parameters L m N Q u := hp.of_frame (by
    intro i hi
    exact hu.regs_eq (by decide +revert))
  obtain ⟨z, hz, zp, zK, zV, zcat⟩ := BoxTable.exec_geometry (L := L) (m := m) (t := t) (D := D)
      (u.comap boxBank)
    (by simp [u, boxBank, BoxTable.Reg.levels, BoxTable.Reg.inner,
      BoxTable.Reg.threshold, BoxTable.Reg.directory, Reg.directory])
    (by simp [u, boxBank, BoxTable.Reg.inner, BoxTable.Reg.threshold,
      BoxTable.Reg.directory, Reg.directory])
    (by simp [u, boxBank, BoxTable.Reg.threshold, BoxTable.Reg.directory])
    (by simp [u, boxBank])
    (hfit.of_le (by unfold wordBudget; dsimp only [D]; omega))
  let v := z.extend boxBank u
  have hv := hz.rename boxBank_injective
  have vp : QueriedProduct.Parameters L m N Q v := up.reframe
    (fun i hi => boxBank_extend_high z u i (by omega))
  have vR : v.regs ⟨15, by decide⟩ = R := by
    exact (boxBank_injective.extend_apply _ _ _).trans zp.records
  have vV : v.regs ⟨16, by decide⟩ = V := by
    exact (boxBank_injective.extend_apply _ _ _).trans zV
  have vK : v.regs ⟨21, by decide⟩ = K := by
    exact (boxBank_injective.extend_apply _ _ _).trans zK
  have vt : v.regs Reg.threshold = t :=
    (boxBank_extend_high z u _ (by decide)).trans ((hu.regs_eq (by decide)).trans ht)
  have vD : v.regs Reg.directory = D := by
    rw [boxBank_extend_high z u _ (by decide)]
    simp [u, Reg.directory, boxBank, BoxTable.Reg.levels, BoxTable.Reg.inner,
      BoxTable.Reg.threshold, BoxTable.Reg.directory]
  have f10 : Fits w 10 := hfit.of_le (by unfold wordBudget; omega)
  have f5 : Fits w 5 := hfit.of_le (by unfold wordBudget; omega)
  have fL : Fits w (L + 1) := hfit.of_le (by unfold wordBudget; omega)
  have fT : Fits w ((L + 1) * 10 ^ L) := hfit.of_le (by unfold wordBudget; omega)
  have fC : Fits w ((L + 1) * 10 ^ L + 10) := hfit.of_le (by unfold wordBudget; omega)
  have fS : Fits w (((L + 1) * 10 ^ L + 10) * 5) := hfit.of_le (by
    unfold wordBudget; omega)
  have fV : Fits w (((L + 1) * 10 ^ L + 10) * 5 + V) := hfit.of_le (by
    unfold wordBudget; dsimp only [V]; omega)
  have fK : Fits w (((L + 1) * 10 ^ L + 10) * 5 + V + K) := by
    apply allocated_fits hfit
    unfold memoryEnd resultBase stackBase BoxQuery.stackCapacity
    dsimp only [V, K]
    omega
  let y₀ := ((v.set Reg.records R).set Reg.values V).set Reg.count K
  let y₁ := (y₀.set Reg.results (L + 1)).set Reg.results ((L + 1) * 10 ^ L)
  let y₂ := (y₁.set QueriedProduct.Reg.temporary 10).set Reg.results
    ((L + 1) * 10 ^ L + 10)
  let y₃ := (y₂.set QueriedProduct.Reg.temporary 5).set Reg.results
    (((L + 1) * 10 ^ L + 10) * 5)
  let y := ((y₃.set Reg.results (((L + 1) * 10 ^ L + 10) * 5 + V)).set
    Reg.results (((L + 1) * 10 ^ L + 10) * 5 + V + K)).set QueriedProduct.Reg.index 0
  have eR : boxBank BoxTable.Reg.records = (15 : Fin 160) := rfl
  have eV : boxBank BoxTable.Reg.values = (16 : Fin 160) := rfl
  have eK : boxBank BoxTable.Reg.count = (21 : Fin 160) := rfl
  change v.regs (15 : Fin 160) = R at vR
  change v.regs (16 : Fin 160) = V at vV
  change v.regs (21 : Fin 160) = K at vK
  have hy : ExecWithin w geometryFinish v y 12 := by
    simp only [geometryFinish, eR, eV, eK]
    ram_eval [y, y₀, y₁, y₂, y₃, vR, vV, vK, vp.depth, vp.one, vp.leaves,
      f10, f5, fL, fT, fC, fS, fV, fK, Reg.records, Reg.values,
      Reg.count, Reg.results, QueriedProduct.Reg.depth, QueriedProduct.Reg.one,
      QueriedProduct.Reg.leaves, QueriedProduct.Reg.temporary, QueriedProduct.Reg.index,
      Fin.mk.injEq]
  have yp : QueriedProduct.Parameters L m N Q y := vp.of_frame (by
    intro i hi
    exact hy.regs_eq (by decide +revert))
  refine ⟨y, (hu.seq (hv.seq hy)).mono (by unfold BoxTable.geometryTime; omega), yp,
    ?_, by simp [y], ?_, ?_⟩
  · constructor
    · exact (hy.regs_eq (by decide)).trans vt
    · exact (hy.regs_eq (by decide)).trans vD
    · simp [y, y₀, y₁, y₂, y₃, Reg.records, Reg.values, Reg.count, Reg.results,
        QueriedProduct.Reg.temporary, QueriedProduct.Reg.index, R]
    · simp [y, y₀, y₁, y₂, y₃, Reg.records, Reg.values, Reg.count, Reg.results,
        QueriedProduct.Reg.temporary,
        QueriedProduct.Reg.index, V]
    · simp [y, y₀, y₁, y₂, y₃, Reg.records, Reg.values, Reg.count, Reg.results,
        QueriedProduct.Reg.temporary,
        QueriedProduct.Reg.index, K]
    · simp [y, y₀, y₁, y₂, y₃, Reg.results, Reg.records, Reg.values, Reg.count,
        QueriedProduct.Reg.index, QueriedProduct.Reg.temporary, resultBase, stackBase,
        BoxQuery.stackCapacity, V, K, Nat.add_assoc, Nat.add_comm,
        Nat.mul_comm]
  · exact ⟨zcat.directory, zcat.code, zcat.stars, zcat.stride⟩
  · intro p hp
    apply zcat.frame p
    · simp only [D] at *
      unfold valueBase recordBase at hp
      omega
    · rw [BoxTable.count_eligible_eq_card_boxes]
      simp only [D]
      unfold valueBase recordBase at hp
      omega

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct
