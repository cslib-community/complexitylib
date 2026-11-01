/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable.CatalogueLoop
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable.Index

/-!
# Complete shared native box geometry

The actual program computes its power, directory extent, compact count and value-table
base from the original scalar parameters. It assigns every directory slot and writes
exactly the catalogue records counted by the existing finite box family.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable

open Cslib.WordRAM

private theorem powerRegisters_injective : Function.Injective powerRegisters := by decide

/-- The existing power routine computes the actual native span with unchanged memory. -/
theorem exec_span {w L : ℕ} (x : Data registers)
    (hL : x.regs Reg.levels = L) (h10 : x.regs Reg.ten = 10)
    (hfit : Fits w (10 ^ L + L + 2)) :
    ∃ y, ExecWithin w (Power.program.rename powerRegisters) x y (4 * L + 5) ∧
      y.regs Reg.span = 10 ^ L ∧ y.regs Reg.one = 1 ∧ y.mem = x.mem ∧
      (∀ i, i ≠ Reg.span → i ≠ Reg.level → i ≠ Reg.one → y.regs i = x.regs i) := by
  obtain ⟨z, hz, hv, _, ho, hm, _, _⟩ :=
    Power.exec 10 L (by decide) (x.comap powerRegisters) h10 hL hfit
  have he := hz.rename powerRegisters_injective
  refine ⟨z.extend powerRegisters x, he, ?_, ?_, hm, ?_⟩
  · have h := congrArg (fun d : Data 5 => d.regs Power.value)
      (Data.comap_extend powerRegisters_injective z x)
    exact h.trans hv
  · have h := congrArg (fun d : Data 5 => d.regs Power.one)
      (Data.comap_extend powerRegisters_injective z x)
    exact h.trans ho
  · intro i hv hc ho
    apply he.regs_eq
    simp [Power.program, Power.body, Code.rename, Code.Preserves, Op.rename, Op.dest,
      Op.bin, powerRegisters, Power.value, Power.counter, Power.base, Power.exponent,
      Power.one, Ne.symm hv, Ne.symm hc, Ne.symm ho]

/-- Explicit scalar initialization, also valid when every old temporary is dirty. -/
theorem exec_constants {w : ℕ} (x : Data registers) (hfit : Fits w 10) :
    ∃ y, ExecWithin w constants x y 5 ∧ y.regs Reg.nil = 0 ∧
      y.regs Reg.one = 1 ∧ y.regs Reg.ten = 10 ∧ y.regs Reg.nine = 9 ∧
      y.regs Reg.three = 3 ∧ y.mem = x.mem ∧
      (∀ i, i ≠ Reg.nil → i ≠ Reg.one → i ≠ Reg.ten → i ≠ Reg.nine →
        i ≠ Reg.three → y.regs i = x.regs i) := by
  have h0 := hfit.of_le (by decide : 0 ≤ 10)
  have h1 := hfit.of_le (by decide : 1 ≤ 10)
  have h3 := hfit.of_le (by decide : 3 ≤ 10)
  have h9 := hfit.of_le (by decide : 9 ≤ 10)
  let y := ((((x.set Reg.nil 0).set Reg.one 1).set Reg.ten 10).set Reg.nine 9).set Reg.three 3
  have he : ExecWithin w constants x y 5 := by
    ram_eval [constants, y, h0, h1, h3, h9, hfit, Reg.nil, Reg.one, Reg.ten,
      Reg.nine, Reg.three, Fin.mk.injEq]
  refine ⟨y, he, by simp [y, Reg.nil, Reg.one, Reg.ten, Reg.nine, Reg.three],
    by simp [y, Reg.nil, Reg.one, Reg.ten, Reg.nine, Reg.three],
    by simp [y, Reg.nil, Reg.one, Reg.ten, Reg.nine, Reg.three],
    by simp [y, Reg.nil, Reg.one, Reg.ten, Reg.nine, Reg.three],
    by simp [y, Reg.nil, Reg.one, Reg.ten, Reg.nine, Reg.three], rfl, ?_⟩
  intro i hi0 hi1 hi10 hi9 hi3
  exact he.regs_eq (by simp [constants, Code.Preserves, Op.dest,
    Ne.symm hi0, Ne.symm hi1, Ne.symm hi10, Ne.symm hi9, Ne.symm hi3])

/-- Actual extent setup and its complete persistent parameter readback. -/
theorem exec_geometrySetup {w L m t D : ℕ} (x : Data registers)
    (hL : x.regs Reg.levels = L) (hm : x.regs Reg.inner = m)
    (ht : x.regs Reg.threshold = t) (hD : x.regs Reg.directory = D)
    (hT : x.regs Reg.span = 10 ^ L) (h1 : x.regs Reg.one = 1)
    (h10 : x.regs Reg.ten = 10) (h9 : x.regs Reg.nine = 9)
    (h3 : x.regs Reg.three = 3) (h0 : x.regs Reg.nil = 0)
    (hfit : Fits w (D + (m - t + 1) * 10 ^ L + m + 12)) :
    ∃ y, ExecWithin w geometrySetup x y 6 ∧
      CatalogueParameters L (m - t) D (D + (m - t + 1) * 10 ^ L) y ∧
      y.regs Reg.slot = 0 ∧ y.regs Reg.count = 0 ∧ y.mem = x.mem := by
  let S := (m - t + 1) * 10 ^ L
  have hp : 0 < 10 ^ L := by positivity
  have hh : Fits w (m - t) := hfit.of_le (by omega)
  have hh1 : Fits w (m - t + 1) := hfit.of_le (by omega)
  have hS : Fits w S := hfit.of_le (by omega)
  have hR : Fits w (D + S) := hfit.of_le (by omega)
  have hf0 : Fits w 0 := hfit.of_le (Nat.zero_le _)
  let a := ((x.set Reg.height (m - t)).set Reg.slots (m - t + 1)).set Reg.slots S
  let y := ((a.set Reg.records (D + S)).set Reg.slot 0).set Reg.count 0
  have he : ExecWithin w geometrySetup x y 6 := by
    ram_eval [geometrySetup, y, a, S, hm, ht, hD, hT, h1, hh, hh1, hS, hR, hf0,
      Reg.height, Reg.slots, Reg.records, Reg.slot, Reg.count, Reg.inner, Reg.threshold,
      Reg.directory, Reg.span, Reg.one, Fin.mk.injEq]
  refine ⟨y, he, ?_, ?_, ?_, rfl⟩
  · constructor <;> simp [y, a, S, hL, hD, hT, h1, h10, h9, h3, h0,
      Reg.height, Reg.slots, Reg.records, Reg.slot, Reg.count, Reg.levels,
      Reg.directory, Reg.span, Reg.one, Reg.ten, Reg.nine, Reg.three, Reg.nil]
  · simp [y, a, Reg.count, Reg.slot]
  · simp [y, a]

/-- Actual shared setup, including all digit scans and descriptor writes. -/
theorem exec_geometry {w L m t D : ℕ} (x : Data registers)
    (hL : x.regs Reg.levels = L) (hm : x.regs Reg.inner = m)
    (ht : x.regs Reg.threshold = t) (hD : x.regs Reg.directory = D)
    (hfit : Fits w (D + (D + (m - t + 1) * 10 ^ L) +
      6 * ((m - t + 1) * 10 ^ L) + 10 ^ L + L + m + 12)) :
    ∃ y, ExecWithin w geometry x y
        (4 * L + 20 + (11 * L + 28) * ((m - t + 1) * 10 ^ L)) ∧
      CatalogueParameters L (m - t) D (D + (m - t + 1) * 10 ^ L) y ∧
      y.regs Reg.count = (Cslib.Algorithms.MatrixMultiplication.Schonhage.boxes L m t).card ∧
      y.regs Reg.values = D + (m - t + 1) * 10 ^ L +
        3 * (Cslib.Algorithms.MatrixMultiplication.Schonhage.boxes L m t).card ∧
      CataloguePrefix L (m - t) D (D + (m - t + 1) * 10 ^ L)
        ((m - t + 1) * 10 ^ L) x.mem y.mem := by
  let S := (m - t + 1) * 10 ^ L
  let R := D + S
  let B := Nat.count (Eligible L (m - t)) S
  have hS : Nat.count (Eligible L (m - t)) S ≤ S := Nat.count_le _
  have h10 : Fits w 10 := hfit.of_le ((by decide : 10 ≤ 12).trans (Nat.le_add_left _ _))
  obtain ⟨a, ha, a0, a1, a10, a9, a3, am, af⟩ := exec_constants x h10
  have aL : a.regs Reg.levels = L := (af _ (by decide) (by decide)
    (by decide) (by decide) (by decide)).trans hL
  obtain ⟨b, hb, bT, b1, bm, bf⟩ := exec_span a aL a10 (hfit.of_le (by omega))
  have bL : b.regs Reg.levels = L := (bf _ (by decide) (by decide) (by decide)).trans aL
  have bD : b.regs Reg.directory = D :=
    (bf _ (by decide) (by decide) (by decide)).trans
      ((af _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hD)
  have bm' : b.regs Reg.inner = m :=
    (bf _ (by decide) (by decide) (by decide)).trans
      ((af _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hm)
  have bt : b.regs Reg.threshold = t :=
    (bf _ (by decide) (by decide) (by decide)).trans
      ((af _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans ht)
  have b0 : b.regs Reg.nil = 0 := (bf _ (by decide) (by decide) (by decide)).trans a0
  have b10 : b.regs Reg.ten = 10 := (bf _ (by decide) (by decide) (by decide)).trans a10
  have b9 : b.regs Reg.nine = 9 := (bf _ (by decide) (by decide) (by decide)).trans a9
  have b3 : b.regs Reg.three = 3 := (bf _ (by decide) (by decide) (by decide)).trans a3
  obtain ⟨c, hc, cp, cs, cc, cm⟩ := exec_geometrySetup b bL bm' bt bD bT b1 b10 b9 b3 b0
    (hfit.of_le (by omega))
  obtain ⟨d, hd, dp, ds, dc, dmem⟩ := exec_catalogueLoop c cp cs cc
    (Nat.le_refl _) (hfit.of_le (by omega))
  have hf3 : Fits w (B * 3) := hfit.of_le (by dsimp only [B]; omega)
  have hfV : Fits w (R + B * 3) := hfit.of_le (by dsimp only [B, R]; omega)
  let y := (d.set Reg.temporary (B * 3)).set Reg.values (R + B * 3)
  have he : ExecWithin w geometryFinish d y 2 := by
    ram_eval [geometryFinish, y, dc, dp.three, dp.records, hf3, hfV, B, R, S,
      Reg.temporary, Reg.values, Reg.count, Reg.three, Reg.records, Fin.mk.injEq]
  have hy : ExecWithin w geometry x y
      (4 * L + 20 + (11 * L + 28) * ((m - t + 1) * 10 ^ L)) := by
    exact (ha.seq (hb.seq (hc.seq (hd.seq he)))).mono (by omega)
  have hycount : y.regs Reg.count = B := by
    simpa [y, Reg.temporary, Reg.values, Reg.count, B, S] using dc
  have hB : B = (Cslib.Algorithms.MatrixMultiplication.Schonhage.boxes L m t).card :=
    count_eligible_eq_card_boxes L m t
  refine ⟨y, hy, ?_, hycount.trans hB, ?_, ?_⟩
  · constructor
    · simpa [y, Reg.temporary, Reg.values, Reg.levels] using dp.levels
    · simpa [y, Reg.temporary, Reg.values, Reg.height] using dp.height
    · simpa [y, Reg.temporary, Reg.values, Reg.span] using dp.span
    · simpa [y, Reg.temporary, Reg.values, Reg.directory] using dp.directory
    · simpa [y, Reg.temporary, Reg.values, Reg.records] using dp.records
    · simpa [y, Reg.temporary, Reg.values, Reg.slots] using dp.slots
    · simpa [y, Reg.temporary, Reg.values, Reg.one] using dp.one
    · simpa [y, Reg.temporary, Reg.values, Reg.ten] using dp.ten
    · simpa [y, Reg.temporary, Reg.values, Reg.nine] using dp.nine
    · simpa [y, Reg.temporary, Reg.values, Reg.three] using dp.three
    · simpa [y, Reg.temporary, Reg.values, Reg.nil] using dp.nil
  · simp [y, R, S, hB, Nat.mul_comm]
  · simpa only [y, Data.set_mem, cm, bm, am] using dmem

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable
