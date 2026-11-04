/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable.Program
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable.Digits

/-!
# Execution of the box-geometry digit scan

The native remainder/division loop counts P0 digits and records the place value of
the requested P0 occurrence. Every scalar fit follows from the original code, depth
and final power. The memory is preserved, including dirty caller scratch.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable

open Cslib.WordRAM

/-- Registers changed by a native digit step. -/
@[expose] def DigitLocal (i : Fin registers) : Prop :=
  i = Reg.digit ∨ i = Reg.suffix ∨ i = Reg.population ∨ i = Reg.starPower ∨
    i = Reg.power ∨ i = Reg.level ∨ i = Reg.temporary

instance (i : Fin registers) : Decidable (DigitLocal i) :=
  inferInstanceAs (Decidable (i = Reg.digit ∨ i = Reg.suffix ∨ i = Reg.population ∨
    i = Reg.starPower ∨ i = Reg.power ∨ i = Reg.level ∨ i = Reg.temporary))

private theorem countDigit_preserves (i : Fin registers) :
    ¬DigitLocal i → countDigit.Preserves i := by decide +revert

/-- One charged step of the real native scan, with its original-input-derived fits. -/
theorem exec_countDigit {w L c e k : ℕ} (x : Data registers) (hk : k < L)
    (h10 : x.regs Reg.ten = 10) (h9 : x.regs Reg.nine = 9)
    (h1 : x.regs Reg.one = 1) (he : x.regs Reg.stars = e)
    (hl : x.regs Reg.level = k) (hq : x.regs Reg.suffix = c / 10 ^ k)
    (hp : x.regs Reg.population = population c k)
    (hpow : x.regs Reg.power = 10 ^ k)
    (hs : x.regs Reg.starPower = starStride c e k)
    (hfit : Fits w (c + 10 ^ L + L + 12)) :
    ∃ y, ExecWithin w countDigit x y 9 ∧ y.regs Reg.level = k + 1 ∧
      y.regs Reg.suffix = c / 10 ^ (k + 1) ∧
      y.regs Reg.population = population c (k + 1) ∧
      y.regs Reg.power = 10 ^ (k + 1) ∧
      y.regs Reg.starPower = starStride c e (k + 1) ∧ y.mem = x.mem ∧
      (∀ i, ¬DigitLocal i → y.regs i = x.regs i) := by
  have hp0 := population_le c k
  have hcBound : c ≤ c + 10 ^ L + L + 12 :=
    ((Nat.le_add_right c (10 ^ L)).trans (Nat.le_add_right _ L)).trans
      (Nat.le_add_right _ 12)
  have hLBound : L ≤ c + 10 ^ L + L + 12 :=
    (Nat.le_add_left L (c + 10 ^ L)).trans (Nat.le_add_right _ 12)
  have hPBound : 10 ^ L ≤ c + 10 ^ L + L + 12 :=
    ((Nat.le_add_left (10 ^ L) c).trans (Nat.le_add_right _ L)).trans
      (Nat.le_add_right _ 12)
  have h12Bound : 12 ≤ c + 10 ^ L + L + 12 := Nat.le_add_left _ _
  have hfpop : Fits w (population c k + 1) :=
    hfit.of_le ((Nat.succ_le_of_lt (hp0.trans_lt hk)).trans hLBound)
  have hfk : Fits w (k + 1) := hfit.of_le ((Nat.succ_le_of_lt hk).trans hLBound)
  have hfd : Fits w (digitAt c k) := hfit.of_le
    ((Nat.le_of_lt (Nat.mod_lt _ (by decide : 0 < 10))).trans
      ((by decide : 10 ≤ 12).trans h12Bound))
  have hfq : Fits w (c / 10 ^ k / 10) := hfit.of_le
    ((Nat.div_le_self _ _).trans ((Nat.div_le_self _ _).trans hcBound))
  have hpowle : 10 ^ (k + 1) ≤ 10 ^ L :=
    Nat.pow_le_pow_right (by decide) (Nat.succ_le_of_lt hk)
  have hfpow : Fits w (10 ^ k * 10) := by
    simpa only [pow_succ] using hfit.of_le (hpowle.trans hPBound)
  have hpowq : c / 10 ^ k / 10 = c / 10 ^ (k + 1) := by
    rw [Nat.div_div_eq_div_mul, pow_succ]
  let base := (x.set Reg.digit (digitAt c k)).set Reg.suffix (c / 10 ^ k / 10)
  let changed := if digitAt c k = 9 then
      if population c k + 1 = e then
        (base.set Reg.population (population c k + 1)).set Reg.starPower (10 ^ k)
      else (base.set Reg.population (population c k + 1)).set Reg.temporary
        (x.regs Reg.temporary)
    else base.set Reg.temporary (x.regs Reg.temporary)
  let y := (changed.set Reg.power (10 ^ k * 10)).set Reg.level (k + 1)
  have hy : ExecWithin w countDigit x y 9 := by
    dsimp only [digitAt] at hfd
    by_cases hd : c / 10 ^ k % 10 = 9 <;> by_cases hm : population c k + 1 = e
    all_goals
      have hf9 : Fits w 9 := hfit.of_le ((by decide : 9 ≤ 12).trans h12Bound)
      have hfn := hfpop
      try rw [hm] at hfn
      ram_eval [countDigit, y, changed, base, hd, hm, h10, h9, h1, he, hl, hq, hp,
        hpow, hs, hfd, hfq, hfpop, hfn, hf9, hfpow, hfk, digitAt,
        Reg.digit, Reg.suffix, Reg.population, Reg.starPower, Reg.power, Reg.level,
        Reg.temporary, Reg.ten, Reg.nine, Reg.one, Reg.stars, Fin.mk.injEq]
  refine ⟨y, hy, ?_, ?_, ?_, ?_, ?_, ?_, fun i hi => hy.regs_eq
    (countDigit_preserves i hi)⟩
  all_goals
    by_cases hd : digitAt c k = 9 <;> by_cases hm : population c k + 1 = e <;>
      simp [y, changed, base, hd, hm, hp, hs, population_succ, starStride,
        hpowq, pow_succ, Reg.level, Reg.power, Reg.population, Reg.suffix,
        Reg.starPower, Reg.digit, Reg.temporary]

/-- Registers changed by the scan, including its descriptor initialization. -/
@[expose] def InspectLocal (i : Fin registers) : Prop :=
  DigitLocal i ∨ i = Reg.stars ∨ i = Reg.completion

instance (i : Fin registers) : Decidable (InspectLocal i) :=
  inferInstanceAs (Decidable (DigitLocal i ∨ i = Reg.stars ∨ i = Reg.completion))

private theorem inspect_preserves (i : Fin registers) :
    ¬InspectLocal i → inspect.Preserves i := by decide +revert

/-- The complete digit loop computes the population and highest-star stride from a raw slot. -/
theorem exec_inspect {w L s : ℕ} (x : Data registers)
    (hL : x.regs Reg.levels = L) (hT : x.regs Reg.span = 10 ^ L)
    (hslot : x.regs Reg.slot = s) (h1 : x.regs Reg.one = 1)
    (h10 : x.regs Reg.ten = 10) (h9 : x.regs Reg.nine = 9)
    (hfit : Fits w (s + 10 ^ L + L + 12)) :
    ∃ y, ExecWithin w inspect x y (11 * L + 9) ∧
      y.regs Reg.stars = s / 10 ^ L ∧ y.regs Reg.completion = s % 10 ^ L ∧
      y.regs Reg.population = population (s % 10 ^ L) L ∧
      y.regs Reg.starPower = starStride (s % 10 ^ L) (s / 10 ^ L) L ∧
      y.mem = x.mem ∧ (∀ i, ¬InspectLocal i → y.regs i = x.regs i) := by
  let e := s / 10 ^ L
  let c := s % 10 ^ L
  have hc : c ≤ s := Nat.mod_le _ _
  have he : e ≤ s := Nat.div_le_self _ _
  have hscalar : s ≤ s + 10 ^ L + L + 12 :=
    ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)).trans (Nat.le_add_right _ _)
  have hfe : Fits w e := hfit.of_le (he.trans hscalar)
  have hfc : Fits w c := hfit.of_le (hc.trans hscalar)
  have hfitc : Fits w (c + 10 ^ L + L + 12) := hfit.of_le
    (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right hc _) _) _)
  have hf1 : Fits w 1 := hfit.of_le ((by decide : 1 ≤ 12).trans (Nat.le_add_left _ _))
  let start := ((((((x.set Reg.stars e).set Reg.completion c).set Reg.suffix c).set
    Reg.level 0).set Reg.population 0).set Reg.power 1).set Reg.starPower 0
  have hs : ExecWithin w (ram[
      Reg.stars ← Reg.slot / Reg.span; Reg.completion ← Reg.slot % Reg.span;
      Reg.suffix ← Reg.completion; Reg.level ← #0; Reg.population ← #0;
      Reg.power ← #1; Reg.starPower ← #0 ]) x start 7 := by
    ram_eval [start, e, c, hslot, hT, hfe, hfc, hf1,
      Reg.stars, Reg.slot, Reg.span, Reg.completion, Reg.suffix, Reg.level,
      Reg.population, Reg.power, Reg.starPower, Fin.mk.injEq]
  let I (y : Data registers) : Prop :=
    y.regs Reg.level ≤ L ∧
      y.regs Reg.suffix = c / 10 ^ y.regs Reg.level ∧
      y.regs Reg.population = population c (y.regs Reg.level) ∧
      y.regs Reg.power = 10 ^ y.regs Reg.level ∧
      y.regs Reg.starPower = starStride c e (y.regs Reg.level) ∧
      y.mem = x.mem ∧ (∀ i, ¬DigitLocal i → y.regs i = start.regs i)
  have hi : I start := by
    simp [I, start, Reg.level, Reg.starPower, Reg.power, Reg.population, Reg.suffix,
      Reg.completion, Reg.stars, population_zero, starStride]
  have hb (y : Data registers) (hy : I y) (hg : (Cond.lt Reg.level Reg.levels).Holds y) :
      ∃ z, ExecWithin w countDigit y z 9 ∧ I z ∧
        L - z.regs Reg.level < L - y.regs Reg.level := by
    obtain ⟨hle, hq, hp, hpow, hstar, hm, hframe⟩ := hy
    have hlevels : y.regs Reg.levels = L := by
      simpa [start, Reg.levels, Reg.stars, Reg.completion, Reg.suffix, Reg.level,
        Reg.population, Reg.power, Reg.starPower] using
        (hframe Reg.levels (by decide)).trans (by
          simpa [start, Reg.levels, Reg.stars, Reg.completion, Reg.suffix, Reg.level,
            Reg.population, Reg.power, Reg.starPower] using hL)
    have hconst1 : y.regs Reg.one = 1 := by
      simpa [start, Reg.one, Reg.stars, Reg.completion, Reg.suffix, Reg.level,
        Reg.population, Reg.power, Reg.starPower] using
        (hframe Reg.one (by decide)).trans (by
          simpa [start, Reg.one, Reg.stars, Reg.completion, Reg.suffix, Reg.level,
            Reg.population, Reg.power, Reg.starPower] using h1)
    have hconst10 : y.regs Reg.ten = 10 := by
      simpa [start, Reg.ten, Reg.stars, Reg.completion, Reg.suffix, Reg.level,
        Reg.population, Reg.power, Reg.starPower] using
        (hframe Reg.ten (by decide)).trans (by
          simpa [start, Reg.ten, Reg.stars, Reg.completion, Reg.suffix, Reg.level,
            Reg.population, Reg.power, Reg.starPower] using h10)
    have hconst9 : y.regs Reg.nine = 9 := by
      simpa [start, Reg.nine, Reg.stars, Reg.completion, Reg.suffix, Reg.level,
        Reg.population, Reg.power, Reg.starPower] using
        (hframe Reg.nine (by decide)).trans (by
          simpa [start, Reg.nine, Reg.stars, Reg.completion, Reg.suffix, Reg.level,
            Reg.population, Reg.power, Reg.starPower] using h9)
    have hstars : y.regs Reg.stars = e := by
      simpa [start, Reg.stars, Reg.completion, Reg.suffix, Reg.level,
        Reg.population, Reg.power, Reg.starPower] using hframe Reg.stars (by decide)
    have hk : y.regs Reg.level < L := by simpa only [Cond.holds_lt, hlevels] using hg
    obtain ⟨z, hz, hzl, hzq, hzp, hzpow, hzs, hzm, hzf⟩ :=
      exec_countDigit y hk hconst10 hconst9 hconst1 hstars rfl hq hp hpow hstar hfitc
    refine ⟨z, hz, ⟨by omega, ?_, ?_, ?_, ?_, hzm.trans hm,
      fun i h => (hzf i h).trans (hframe i h)⟩, by omega⟩
    · simpa only [hzl] using hzq
    · simpa only [hzl] using hzp
    · simpa only [hzl] using hzpow
    · simpa only [hzl] using hzs
  obtain ⟨y, hloop, hy, hstop⟩ := ExecWithin.loop_invariant I
    (fun y => L - y.regs Reg.level) hb hi
  have hlevels : y.regs Reg.levels = L := by
    simpa [start, Reg.levels, Reg.stars, Reg.completion, Reg.suffix, Reg.level,
      Reg.population, Reg.power, Reg.starPower] using
      (hy.2.2.2.2.2.2 Reg.levels (by decide)).trans (by
        simpa [start, Reg.levels, Reg.stars, Reg.completion, Reg.suffix, Reg.level,
          Reg.population, Reg.power, Reg.starPower] using hL)
  have hdone : y.regs Reg.level = L := by
    simp only [Cond.holds_lt, hlevels, not_lt] at hstop
    exact Nat.le_antisymm hy.1 hstop
  have hwhole : ExecWithin w inspect x y (11 * L + 9) := by
    apply (hs.seq hloop).mono
    simp only [start, Data.set_regs, Reg.level, Reg.population, Reg.power, Reg.starPower,
      Function.update_apply, Fin.reduceEq, ↓reduceIte, Nat.sub_zero]
    omega
  refine ⟨y, hwhole, ?_, ?_, ?_, ?_, hy.2.2.2.2.2.1,
    fun i hi => hwhole.regs_eq (inspect_preserves i hi)⟩
  · simpa [start, Reg.stars, Reg.completion, Reg.suffix, Reg.level,
      Reg.population, Reg.power, Reg.starPower] using hy.2.2.2.2.2.2 Reg.stars (by decide)
  · simpa [start, Reg.stars, Reg.completion, Reg.suffix, Reg.level,
      Reg.population, Reg.power, Reg.starPower] using
      hy.2.2.2.2.2.2 Reg.completion (by decide)
  · simpa only [hdone] using hy.2.2.1
  · simpa only [hdone] using hy.2.2.2.2.1

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable
