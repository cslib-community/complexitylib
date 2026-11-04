/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable.InputLayout

/-!
# Native box-table input adaptation

The actual header loads, reused power code and pointer arithmetic locate the original
two leaf arrays and the first writable word. No array or workspace is copied or cleared.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable

open Cslib.WordRAM

/-- Actual scalar header loads with unchanged memory. -/
theorem exec_inputHeaders {w L m t : ℕ} (x : Data registers)
    (hL : x.mem 1 = L) (hm : x.mem 2 = m) (ht : x.mem 3 = t)
    (hfit : Fits w 3) :
    ∃ y, ExecWithin w inputHeaders x y 6 ∧ y.regs Reg.levels = L ∧
      y.regs Reg.inner = m ∧ y.regs Reg.threshold = t ∧ y.mem = x.mem := by
  have h1 : Fits w 1 := hfit.of_le (by decide)
  have h2 : Fits w 2 := hfit.of_le (by decide)
  let y := (((((x.set Reg.address 1).set Reg.levels L).set Reg.address 2).set
    Reg.inner m).set Reg.address 3).set Reg.threshold t
  have he : ExecWithin w inputHeaders x y 6 := by
    ram_eval [inputHeaders, y, hL, hm, ht, h1, h2, hfit,
      Reg.address, Reg.levels, Reg.inner, Reg.threshold, Fin.mk.injEq]
  exact ⟨y, he, by simp [y, Reg.levels, Reg.inner, Reg.threshold, Reg.address],
    by simp [y, Reg.inner, Reg.threshold, Reg.address], by simp [y], rfl⟩

/-- Complete native initialization from the three actual input header words. -/
theorem exec_loadInput {w L m t : ℕ} (x : Data registers)
    (hL : x.mem 1 = L) (hm : x.mem 2 = m) (ht : x.mem 3 = t)
    (hfit : Fits w (2 * 10 ^ L + L + 12)) :
    ∃ y, ExecWithin w loadInput x y (4 * L + 19) ∧
      y.regs Reg.levels = L ∧ y.regs Reg.inner = m ∧ y.regs Reg.threshold = t ∧
      y.regs Reg.arrayA = 4 ∧ y.regs Reg.arrayB = 4 + 10 ^ L ∧
      y.regs Reg.directory = directoryBase L ∧ y.mem = x.mem := by
  obtain ⟨a, ha, aL, am, ath, haμ⟩ := exec_inputHeaders x hL hm ht
    (hfit.of_le (by omega))
  obtain ⟨b, hb, _, _, b10, _, _, hbμ, bf⟩ := exec_constants a
    (hfit.of_le ((by decide : 10 ≤ 12).trans (Nat.le_add_left _ _)))
  have bL : b.regs Reg.levels = L :=
    (bf _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans aL
  obtain ⟨c, hc, cT, _, hcμ, cf⟩ := exec_span b bL b10 (hfit.of_le (by omega))
  have cL : c.regs Reg.levels = L := (cf _ (by decide) (by decide) (by decide)).trans bL
  have cm : c.regs Reg.inner = m :=
    (cf _ (by decide) (by decide) (by decide)).trans
      ((bf _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans am)
  have ct : c.regs Reg.threshold = t :=
    (cf _ (by decide) (by decide) (by decide)).trans
      ((bf _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans ath)
  have hf4 : Fits w 4 := hfit.of_le (by omega)
  have hfB : Fits w (4 + 10 ^ L) := hfit.of_le (by omega)
  have hfD : Fits w (4 + 10 ^ L + 10 ^ L) := hfit.of_le (by omega)
  let y := ((c.set Reg.arrayA 4).set Reg.arrayB (4 + 10 ^ L)).set
    Reg.directory (4 + 10 ^ L + 10 ^ L)
  have hd : ExecWithin w inputPointers c y 3 := by
    ram_eval [inputPointers, y, cT, hf4, hfB, hfD, Reg.arrayA, Reg.arrayB,
      Reg.directory, Reg.span, Fin.mk.injEq]
  refine ⟨y, (ha.seq (hb.seq (hc.seq hd))).mono (by omega), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [y, Reg.levels, Reg.arrayA, Reg.arrayB, Reg.directory] using cL
  · simpa [y, Reg.inner, Reg.arrayA, Reg.arrayB, Reg.directory] using cm
  · simpa [y, Reg.threshold, Reg.arrayA, Reg.arrayB, Reg.directory] using ct
  · simp [y, Reg.arrayA, Reg.arrayB, Reg.directory]
  · simp [y, Reg.arrayB, Reg.directory]
  · simp [y, directoryBase]; omega
  · exact hcμ.trans (hbμ.trans haμ)

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable
