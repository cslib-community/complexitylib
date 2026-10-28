/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandMeaning

/-!
# Charged native splitting of tensor-string digits

## Main results

* `BandPreparation.exec_split`: the actual base-seven digit loop computes the binary mask
  and both compressed offsets with every native arithmetic operation charged.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandPreparation

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open BandDigits

/-- Fixed scalar inputs to a digit loop, without execution or fit assumptions. -/
structure SplitParameters (L : ℕ) (x : Data 96) : Prop where
  /-- Original depth. -/
  levels : x.regs levels = L
  /-- Constant one. -/
  one : x.regs one = 1
  /-- Constant two. -/
  two : x.regs two = 2
  /-- Constant three. -/
  three : x.regs three = 3
  /-- Constant four. -/
  four : x.regs four = 4
  /-- Constant seven. -/
  seven : x.regs seven = 7

private def splitParameterRegisters : Finset (Fin 96) := {levels, one, two, three, four, seven}

private theorem SplitParameters.of_eq {L : ℕ} {x y : Data 96} (hx : SplitParameters L x)
    (h : ∀ i ∈ splitParameterRegisters, y.regs i = x.regs i) : SplitParameters L y :=
  ⟨(h _ (by decide)).trans hx.levels, (h _ (by decide)).trans hx.one,
    (h _ (by decide)).trans hx.two, (h _ (by decide)).trans hx.three,
    (h _ (by decide)).trans hx.four, (h _ (by decide)).trans hx.seven⟩

/-- Remaining-digit equations and elementary counter bounds during the native scan. -/
structure SplitProgress (L a : ℕ) (x : Data 96) : Prop where
  /-- Parameters are retained. -/
  fixed : SplitParameters L x
  /-- Number of consumed levels. -/
  level_le : x.regs level ≤ L
  /-- Division only decreases the residual index. -/
  residue_le : x.regs residue ≤ a
  /-- Binary place weight. -/
  mask_power : x.regs maskPower = 2 ^ x.regs level
  /-- At most one outer place is consumed per level. -/
  outer_power : x.regs outerPower ≤ 3 ^ x.regs level
  /-- At most one inner place is consumed per level. -/
  inner_power : x.regs innerPower ≤ 4 ^ x.regs level
  /-- Partial binary value is below its next place. -/
  mask_acc : x.regs maskAcc < x.regs maskPower
  /-- Partial base-three value is below its next place. -/
  outer_acc : x.regs outerAcc < x.regs outerPower
  /-- Partial base-four value is below its next place. -/
  inner_acc : x.regs innerAcc < x.regs innerPower
  /-- The binary accumulator and remaining digits give the complete mask. -/
  mask_value : x.regs maskAcc + x.regs maskPower *
    (parts (L - x.regs level) (x.regs residue)).mask = (parts L a).mask
  /-- The outer accumulator and remaining digits give the complete outer offset. -/
  outer_value : x.regs outerAcc + x.regs outerPower *
    (parts (L - x.regs level) (x.regs residue)).outer = (parts L a).outer
  /-- The inner accumulator and remaining digits give the complete inner offset. -/
  inner_value : x.regs innerAcc + x.regs innerPower *
    (parts (L - x.regs level) (x.regs residue)).inner = (parts L a).inner

/-- One native digit iteration, using only bounds derived from the original index/depth. -/
theorem exec_splitBody {w : ℕ} (L a : ℕ) (x : Data 96) (hx : SplitProgress L a x)
    (hc : (Cond.lt level levels).Holds x) (hfit : Fits w (a + L + 16 * 10 ^ L + 16)) :
    ∃ y, ExecWithin w splitBody x y 11 ∧ SplitProgress L a y ∧ y.mem = x.mem ∧
      L - y.regs level < L - x.regs level := by
  have hj : x.regs level < L := by simpa only [Cond.holds_lt, hx.fixed.levels] using hc
  have hd : x.regs residue % 7 < 7 := Nat.mod_lt _ (by decide)
  have hpow (b : ℕ) (hb : b ≤ 10) : b ^ x.regs level ≤ 10 ^ L :=
    (Nat.pow_le_pow_left hb _).trans (Nat.pow_le_pow_right (by decide) hx.level_le)
  have hmp : x.regs maskPower ≤ 10 ^ L := by rw [hx.mask_power]; exact hpow 2 (by decide)
  have hop : x.regs outerPower ≤ 10 ^ L := hx.outer_power.trans (hpow 3 (by decide))
  have hip : x.regs innerPower ≤ 10 ^ L := hx.inner_power.trans (hpow 4 (by decide))
  have hdFit : Fits w (x.regs residue % 7) := hfit.of_le (by omega)
  have hrFit : Fits w (x.regs residue / 7) :=
    hfit.of_le ((Nat.div_le_self _ _).trans (by have := hx.residue_le; omega))
  have hmFit : Fits w (x.regs maskPower * 2) := hfit.of_le (by omega)
  have hjFit : Fits w (x.regs level + 1) := hfit.of_le (by omega)
  have hrest : L - x.regs level = L - (x.regs level + 1) + 1 := by omega
  by_cases houter : x.regs residue % 7 < 3
  · have hmul : Fits w (x.regs residue % 7 * x.regs outerPower) :=
      hfit.of_le (by nlinarith)
    have hadd : Fits w (x.regs outerAcc + x.regs residue % 7 * x.regs outerPower) :=
      hfit.of_le (by have := hx.outer_acc; nlinarith)
    have hpower : Fits w (x.regs outerPower * 3) := hfit.of_le (by omega)
    let y := (((((((x.set digit (x.regs residue % 7)).set residue (x.regs residue / 7)).set
      temporary (x.regs residue % 7 * x.regs outerPower)).set outerAcc
      (x.regs outerAcc + x.regs residue % 7 * x.regs outerPower)).set outerPower
      (x.regs outerPower * 3)).set maskPower (x.regs maskPower * 2)).set
      level (x.regs level + 1))
    have he : ExecWithin w splitBody x y 11 := by
      ram_eval [splitBody, y, hx.fixed.one, hx.fixed.two, hx.fixed.three, hx.fixed.seven,
        hdFit, hrFit, hmFit, hjFit, hmul, hadd, hpower, houter,
        digit, residue, temporary, outerAcc, outerPower, maskPower, level, one, two,
        three, seven, Fin.mk.injEq]
    have hfixed : SplitParameters L y := hx.fixed.of_eq (by
      intro i hi
      apply he.regs_eq
      have hf : ∀ i ∈ splitParameterRegisters, splitBody.Preserves i := by
        simp only [splitBody, Code.Preserves, Op.dest, Op.bin]
        decide
      exact hf i hi)
    have hmval := hx.mask_value
    have hoval := hx.outer_value
    have hival := hx.inner_value
    rw [hrest, parts, ite_eq_left houter] at hmval hoval hival
    refine ⟨y, he, ?_, rfl, ?_⟩
    · constructor
      · exact hfixed
      all_goals simp +decide only [y, Data.set_regs, Function.update_apply, ↓reduceIte]
      · omega
      · exact (Nat.div_le_self _ _).trans hx.residue_le
      · simpa only [pow_succ] using congrArg (fun n => n * 2) hx.mask_power
      · rw [pow_succ]
        exact Nat.mul_le_mul_right 3 hx.outer_power
      · exact hx.inner_power.trans (Nat.pow_le_pow_right (by decide) (by omega))
      · have := hx.mask_acc; omega
      · have := hx.outer_acc; nlinarith only [this, houter]
      · exact hx.inner_acc
      · nlinarith only [hmval]
      · nlinarith only [hoval]
      · exact hival
    · have hyl : y.regs level = x.regs level + 1 := by simp [y]
      rw [hyl]
      omega
  · have hsub : Fits w (x.regs residue % 7 - 3) := hfit.of_le (by omega)
    have hsuble : x.regs residue % 7 - 3 < 4 := by omega
    have hmul : Fits w ((x.regs residue % 7 - 3) * x.regs innerPower) :=
      hfit.of_le (by nlinarith only [hip, hsuble])
    have hadd : Fits w (x.regs innerAcc + (x.regs residue % 7 - 3) * x.regs innerPower) :=
      hfit.of_le (by nlinarith only [hx.inner_acc, hip, hsuble])
    have hpower : Fits w (x.regs innerPower * 4) := hfit.of_le (by omega)
    have hmask : Fits w (x.regs maskAcc + x.regs maskPower) :=
      hfit.of_le (by have := hx.mask_acc; omega)
    let y := (((((((((x.set digit (x.regs residue % 7)).set residue (x.regs residue / 7)).set
      digit (x.regs residue % 7 - 3)).set temporary
      ((x.regs residue % 7 - 3) * x.regs innerPower)).set innerAcc
      (x.regs innerAcc + (x.regs residue % 7 - 3) * x.regs innerPower)).set innerPower
      (x.regs innerPower * 4)).set maskAcc (x.regs maskAcc + x.regs maskPower)).set
      maskPower (x.regs maskPower * 2)).set level (x.regs level + 1))
    have he : ExecWithin w splitBody x y 11 := by
      ram_eval [splitBody, y, hx.fixed.one, hx.fixed.two, hx.fixed.three, hx.fixed.four,
        hx.fixed.seven, hdFit, hrFit, hmFit, hjFit, hsub, hmul, hadd, hpower, hmask, houter,
        digit, residue, temporary, innerAcc, innerPower, maskAcc, maskPower, level,
        one, two, three, four, seven, Fin.mk.injEq]
    have hfixed : SplitParameters L y := hx.fixed.of_eq (by
      intro i hi
      apply he.regs_eq
      have hf : ∀ i ∈ splitParameterRegisters, splitBody.Preserves i := by
        simp only [splitBody, Code.Preserves, Op.dest, Op.bin]
        decide
      exact hf i hi)
    have hmval := hx.mask_value
    have hoval := hx.outer_value
    have hival := hx.inner_value
    rw [hrest, parts, ite_eq_right houter] at hmval hoval hival
    refine ⟨y, he, ?_, rfl, ?_⟩
    · constructor
      · exact hfixed
      all_goals simp +decide only [y, Data.set_regs, Function.update_apply, ↓reduceIte]
      · omega
      · exact (Nat.div_le_self _ _).trans hx.residue_le
      · simpa only [pow_succ] using congrArg (fun n => n * 2) hx.mask_power
      · exact hx.outer_power.trans (Nat.pow_le_pow_right (by decide) (by omega))
      · rw [pow_succ]
        exact Nat.mul_le_mul_right 4 hx.inner_power
      · have := hx.mask_acc; omega
      · exact hx.outer_acc
      · nlinarith only [hx.inner_acc, hsuble]
      · nlinarith only [hmval]
      · exact hoval
      · nlinarith only [hival]
    · have hyl : y.regs level = x.regs level + 1 := by simp [y]
      rw [hyl]
      omega

/-- All digits are split by the fixed native loop. Scratch need not start at zero: every
accumulator and place weight is explicitly initialized and its initialization is charged. -/
theorem exec_split {w : ℕ} (L a : ℕ) (x : Data 96) (hx : SplitParameters L x)
    (ha : x.regs index = a) (hfit : Fits w (a + L + 16 * 10 ^ L + 16)) :
    ∃ y, ExecWithin w splitCode x y (13 * L + 10) ∧ SplitParameters L y ∧
      y.regs maskAcc = (parts L a).mask ∧ y.regs outerAcc = (parts L a).outer ∧
      y.regs innerAcc = (parts L a).inner ∧ y.mem = x.mem := by
  have h0 : Fits w 0 := hfit.of_le (Nat.zero_le _)
  have h1 : Fits w 1 := hfit.of_le (by omega)
  let start := ((((((((x.set residue a).set maskAcc 0).set outerAcc 0).set innerAcc 0).set
    maskPower 1).set outerPower 1).set innerPower 1).set level 0)
  have hs : ExecWithin w splitHead x start 8 := by
    ram_eval [splitHead, start, ha, h0, h1, residue, index, maskAcc, outerAcc, innerAcc,
      maskPower, outerPower, innerPower, level, Fin.mk.injEq]
  have hp : SplitParameters L start := hx.of_eq (by
    intro i hi
    apply hs.regs_eq
    have hf : ∀ i ∈ splitParameterRegisters, splitHead.Preserves i := by
      simp only [splitHead, Code.Preserves, Op.dest]
      decide
    exact hf i hi)
  have hi : SplitProgress L a start := by
    constructor
    · exact hp
    all_goals simp [start, residue, maskAcc, outerAcc, innerAcc,
      maskPower, outerPower, innerPower, level]
  let I (y : Data 96) : Prop := SplitProgress L a y ∧ y.mem = x.mem
  have hb (y : Data 96) (hy : I y) (hc : (Cond.lt level levels).Holds y) :
      ∃ z, ExecWithin w splitBody y z 11 ∧ I z ∧ L - z.regs level < L - y.regs level := by
    obtain ⟨z, he, hz, hm, ht⟩ := exec_splitBody L a y hy.1 hc hfit
    exact ⟨z, he, ⟨hz, hm.trans hy.2⟩, ht⟩
  obtain ⟨y, he, hy, hc⟩ := ExecWithin.loop_invariant I
    (fun y => L - y.regs level) hb ⟨hi, rfl⟩
  have hlevel : y.regs level = L := by
    simp only [Cond.holds_lt, hy.1.fixed.levels] at hc
    have := hy.1.level_le
    omega
  have hwhole : ExecWithin w splitCode x y (13 * L + 10) := by
    apply (hs.seq he).mono
    have hs0 : start.regs level = 0 := by simp [start]
    rw [hs0, Nat.sub_zero]
    omega
  refine ⟨y, hwhole, hy.1.fixed, ?_, ?_, ?_, hy.2⟩
  · simpa only [hlevel, Nat.sub_self, parts, Nat.mul_zero, Nat.add_zero]
      using hy.1.mask_value
  · simpa only [hlevel, Nat.sub_self, parts, Nat.mul_zero, Nat.add_zero]
      using hy.1.outer_value
  · simpa only [hlevel, Nat.sub_self, parts, Nat.mul_zero, Nat.add_zero]
      using hy.1.inner_value

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandPreparation
