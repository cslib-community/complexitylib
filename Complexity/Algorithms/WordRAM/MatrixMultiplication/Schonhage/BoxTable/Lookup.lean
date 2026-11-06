/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable.LookupLoop
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable.Values

/-!
# Native lookup in the computed compact box table

The real code scans the original cube digits and reads its computed directory rank
and signed table word. The caller supplies ordinary memory readback, as obtained from
the native catalogue and value constructors. All scan and address arithmetic is charged;
the lookup preserves all memory and registers outside its documented scalar workspace.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable

open Cslib.WordRAM Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- The complete scalar workspace modified by native lookup, including returned fields. -/
@[expose] def LookupWholeLocal (i : Fin registers) : Prop :=
  LookupLocal i ∨ i = Reg.nil ∨ i = Reg.one ∨ i = Reg.ten ∨ i = Reg.nine ∨
    i = Reg.three ∨ i = Reg.found ∨ i = Reg.answer ∨ i = Reg.childSlot ∨ i = Reg.childRank

instance (i : Fin registers) : Decidable (LookupWholeLocal i) :=
  inferInstanceAs (Decidable (LookupLocal i ∨ i = Reg.nil ∨ i = Reg.one ∨ i = Reg.ten ∨
    i = Reg.nine ∨ i = Reg.three ∨ i = Reg.found ∨ i = Reg.answer ∨
    i = Reg.childSlot ∨ i = Reg.childRank))

private theorem lookup_preserves (i : Fin registers) :
    ¬LookupWholeLocal i → lookup.Preserves i := by decide +revert

private theorem lookupSetup_preserves (i : Fin registers) :
    ¬LookupWholeLocal i → lookupSetup.Preserves i := by decide +revert

private theorem exec_lookupSetup {w L C : ℕ} (x : Data registers)
    (hL : x.regs Reg.levels = L) (hC : x.regs Reg.cube = C) (hfit : Fits w 10) :
    ∃ y, ExecWithin w lookupSetup x y 14 ∧ y.mem = x.mem ∧ LookupParameters L C y ∧
      y.regs Reg.level = 0 ∧ y.regs Reg.power = 1 ∧ y.regs Reg.completion = 0 ∧
      y.regs Reg.stars = 0 ∧ y.regs Reg.population = 0 ∧
      y.regs Reg.fixedSeen = 0 ∧ y.regs Reg.invalid = 0 ∧
      (∀ i, ¬LookupWholeLocal i → y.regs i = x.regs i) := by
  have hf0 : Fits w 0 := hfit.of_le (by decide)
  have hf1 : Fits w 1 := hfit.of_le (by decide)
  have hf3 : Fits w 3 := hfit.of_le (by decide)
  have hf9 : Fits w 9 := hfit.of_le (by decide)
  let y := ((((((((((((((x.set Reg.nil 0).set Reg.one 1).set Reg.ten 10).set Reg.nine 9).set
    Reg.three 3).set Reg.level 0).set Reg.stars 0).set Reg.population 0).set
    Reg.fixedSeen 0).set Reg.invalid 0).set Reg.completion 0).set Reg.power 1).set
    Reg.found 0).set Reg.answer 0)
  have hy : ExecWithin w lookupSetup x y 14 := by
    ram_eval [lookupSetup, constants, y, hfit, hf0, hf1, hf3, hf9,
      Reg.nil, Reg.one, Reg.ten, Reg.nine, Reg.three, Reg.level, Reg.stars,
      Reg.population, Reg.fixedSeen, Reg.invalid, Reg.completion, Reg.power,
      Reg.found, Reg.answer, Fin.mk.injEq]
  refine ⟨y, hy, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun i hi => hy.regs_eq (lookupSetup_preserves i hi)⟩
  · constructor <;> simp [y, hL, hC, Reg.nil, Reg.one, Reg.ten, Reg.nine, Reg.three,
      Reg.level, Reg.stars, Reg.population, Reg.fixedSeen, Reg.invalid, Reg.completion,
      Reg.power, Reg.found, Reg.answer, Reg.levels, Reg.cube]
  all_goals simp [y, Reg.nil, Reg.one, Reg.ten, Reg.nine, Reg.three,
    Reg.level, Reg.stars, Reg.population, Reg.fixedSeen, Reg.invalid, Reg.completion,
    Reg.power, Reg.found, Reg.answer]

/-- Read the genuine signed word at a valid box's computed compact rank. -/
theorem exec_lookup {w L m t C D V : ℕ} (x : Data registers) (π : Cube L)
    (a b : Leaf L → ℤ) (hπ : IsBox m t π)
    (hL : x.regs Reg.levels = L) (hH : x.regs Reg.height = m - t)
    (hT : x.regs Reg.span = 10 ^ L) (hC : x.regs Reg.cube = C)
    (hD : x.regs Reg.directory = D) (hV : x.regs Reg.values = V)
    (hread : ∀ i < L, x.mem (C + i) = rawCubeDigit π i)
    (hdir : ∀ s < (m - t + 1) * 10 ^ L, x.mem (D + s) = directoryWord L (m - t) s)
    (hvalues : ∀ s < (m - t + 1) * 10 ^ L, Eligible L (m - t) s →
      x.mem (V + Nat.count (Eligible L (m - t)) s) = Signed.encode (slotValue a b s))
    (hfit : Fits w (C + D + V + (m - t + 1) * 10 ^ L + 10 ^ L + L + 30)) :
    ∃ y, ExecWithin w lookup x y (18 * L + 32) ∧ y.mem = x.mem ∧
      y.regs Reg.found = 1 ∧
      y.regs Reg.answer = Signed.encode (boxValue a b π.starLevels.card π) ∧
      (∀ i, ¬LookupWholeLocal i → y.regs i = x.regs i) := by
  obtain ⟨u, hu, hum, hup, hul, hupow, huc, hus, huf, huv, hui, hframeu⟩ :=
    exec_lookupSetup x hL hC (hfit.of_le (by omega))
  obtain ⟨z, hz, hzm, hzp, hzl, hzpow, hzc, hzs, hzf, hzi, hframez⟩ :=
    exec_lookupLoop u π hπ hup (by simpa only [hum] using hread)
      hul hupow huc hus huf huv hui (hfit.of_le (by omega))
  have hmem : z.mem = x.mem := hzm.trans hum
  have hpres (i : Fin registers) (hi : ¬LookupWholeLocal i) : z.regs i = x.regs i :=
    (hframez i (fun h => hi (Or.inl h))).trans (hframeu i hi)
  have zH : z.regs Reg.height = m - t := (hpres _ (by decide)).trans hH
  have zT : z.regs Reg.span = 10 ^ L := (hpres _ (by decide)).trans hT
  have zD : z.regs Reg.directory = D := (hpres _ (by decide)).trans hD
  have zV : z.regs Reg.values = V := (hpres _ (by decide)).trans hV
  let s := cubeSlot π
  let r := Nat.count (Eligible L (m - t)) s
  have hs : s < (m - t + 1) * 10 ^ L := cubeSlot_lt hπ
  have hv : Eligible L (m - t) s := eligible_cubeSlot hπ
  have hr : r ≤ s := Nat.count_le _
  have hslot : π.starLevels.card * 10 ^ L +
      (Encoding.leafIndex π.starsToP0).val = s := rfl
  have hword : z.mem (D + s) = r + 1 := by
    rw [hmem, hdir s hs, directoryWord, ite_eq_left hv]
  have hvalue : z.mem (V + r) = Signed.encode (slotValue a b s) := by
    rw [hmem]
    exact hvalues s hs hv
  have hfprod : Fits w (π.starLevels.card * 10 ^ L) := hfit.of_le (by omega)
  have hfs : Fits w s := hfit.of_le (by omega)
  have hfD : Fits w (D + s) := hfit.of_le (by omega)
  have hfr : Fits w r := hfit.of_le (by omega)
  have hfV : Fits w (V + r) := hfit.of_le (by omega)
  have hf1 : Fits w 1 := hfit.of_le (by omega)
  have hnH : ¬m - t < π.starLevels.card + π.P0Levels.card := not_lt.mpr hπ.1
  have hnr : ¬r + 1 = 0 := by omega
  let z' := z.set Reg.temporary (z.regs Reg.temporary)
  let y := ((((((((z'.set Reg.childSlot (π.starLevels.card * 10 ^ L)).set Reg.childSlot s).set
    Reg.address (D + s)).set Reg.childRank (r + 1)).set Reg.childRank r).set
    Reg.address (V + r)).set Reg.answer (Signed.encode (slotValue a b s))).set Reg.found 1)
  have hy : ExecWithin w lookupFinish z y 16 := by
    ram_eval [lookupFinish, y, z', zH, zT, zD, zV, hzs, hzc, hzf, hzi,
      hzp.nil, hzp.one, hnH, hslot, hword, hvalue, hnr,
      hfprod, hfs, hfD, hfr, hfV, hf1, Nat.add_sub_cancel,
      Reg.height, Reg.population, Reg.invalid, Reg.nil, Reg.temporary,
      Reg.childSlot, Reg.stars, Reg.span, Reg.completion, Reg.address, Reg.directory,
      Reg.childRank, Reg.one, Reg.values, Reg.answer, Reg.found, Fin.mk.injEq]
  have he : ExecWithin w lookup x y (18 * L + 32) :=
    (hu.seq (hz.seq hy)).mono (by omega)
  refine ⟨y, he, hmem, ?_, ?_, fun i hi => he.regs_eq (lookup_preserves i hi)⟩
  · simp [y, Reg.found, Reg.answer]
  · have hval : slotValue a b s = boxValue a b π.starLevels.card π := by
      have hstars : recordStars L s = π.starLevels.card := by
        dsimp only [s, cubeSlot]
        rw [recordStars_slot]
      rw [slotValue, hstars, slotCube_cubeSlot hπ]
    simpa [y, Reg.found, Reg.answer] using congrArg Signed.encode hval

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable
