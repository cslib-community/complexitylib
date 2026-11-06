/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable.LookupStep
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable.LookupDigits

/-!
# Complete native cube-digit lookup scan

The actual loop reads every original cube word once and returns the existing completed
leaf index, exact star/P0 counts and a valid order flag. Its invariant counts fixed P0
occurrences with Mathlib's count, so no precomputed order or index certificate is needed.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable

open Cslib.WordRAM Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Persistent actual register contents used by a raw cube lookup scan. -/
structure LookupParameters (L C : ℕ) (x : Data registers) : Prop where
  /-- Original depth. -/
  levels : x.regs Reg.levels = L
  /-- Real input cube pointer. -/
  cube : x.regs Reg.cube = C
  /-- Constant zero. -/
  nil : x.regs Reg.nil = 0
  /-- Constant one. -/
  one : x.regs Reg.one = 1
  /-- Constant P0 digit. -/
  nine : x.regs Reg.nine = 9
  /-- Constant radix and star digit. -/
  ten : x.regs Reg.ten = 10

private theorem lookupLoop_preserves (i : Fin registers) :
    ¬LookupLocal i → (Code.loop (.lt Reg.level Reg.levels) lookupDigit).Preserves i := by
  decide +revert

/-- The native loop computes every final lookup scalar from the actual cube words. -/
theorem exec_lookupLoop {w L m t C : ℕ} (x : Data registers) (π : Cube L)
    (hπ : IsBox m t π) (hx : LookupParameters L C x)
    (hread : ∀ i < L, x.mem (C + i) = rawCubeDigit π i)
    (hlevel : x.regs Reg.level = 0) (hpow : x.regs Reg.power = 1)
    (hcode : x.regs Reg.completion = 0) (hstars : x.regs Reg.stars = 0)
    (hpop : x.regs Reg.population = 0) (hseen : x.regs Reg.fixedSeen = 0)
    (hinvalid : x.regs Reg.invalid = 0)
    (hfit : Fits w (C + 10 ^ L + L + 20)) :
    ∃ y, ExecWithin w (.loop (.lt Reg.level Reg.levels) lookupDigit) x y (18 * L + 2) ∧
      y.mem = x.mem ∧ LookupParameters L C y ∧ y.regs Reg.level = L ∧
      y.regs Reg.power = 10 ^ L ∧
      y.regs Reg.completion = (Encoding.leafIndex π.starsToP0).val ∧
      y.regs Reg.stars = π.starLevels.card ∧
      y.regs Reg.population = π.starLevels.card + π.P0Levels.card ∧
      y.regs Reg.invalid = 0 ∧
      (∀ i, ¬LookupLocal i → y.regs i = x.regs i) := by
  let raw := rawCubeDigit π
  let I (y : Data registers) : Prop :=
    LookupParameters L C y ∧ y.mem = x.mem ∧ y.regs Reg.level ≤ L ∧
      y.regs Reg.power = 10 ^ y.regs Reg.level ∧
      y.regs Reg.completion = lookupCompletion raw (y.regs Reg.level) ∧
      y.regs Reg.stars = Nat.count (fun i => raw i = 10) (y.regs Reg.level) ∧
      y.regs Reg.population = Nat.count (fun i => raw i = 9 ∨ raw i = 10) (y.regs Reg.level) ∧
      y.regs Reg.fixedSeen = (if Nat.count (fun i => raw i = 9) (y.regs Reg.level) = 0
        then 0 else 1) ∧ y.regs Reg.invalid = 0
  have hi : I x := by
    refine ⟨hx, rfl, by omega, ?_, ?_, ?_, ?_, ?_, hinvalid⟩
    all_goals simp [hlevel, hpow, hcode, hstars, hpop, hseen, lookupCompletion]
  have hb (y : Data registers) (hy : I y)
      (hg : (Cond.lt Reg.level Reg.levels).Holds y) :
      ∃ z, ExecWithin w lookupDigit y z 16 ∧ I z ∧
        L - z.regs Reg.level < L - y.regs Reg.level := by
    obtain ⟨hp, hm, hle, hpower, hc, hs, hf, hv, hinv⟩ := hy
    have hk : y.regs Reg.level < L := by simpa only [Cond.holds_lt, hp.levels] using hg
    have hseenle : (if Nat.count (fun i => raw i = 9) (y.regs Reg.level) = 0
        then 0 else 1) ≤ 1 := by split <;> omega
    have horder : raw (y.regs Reg.level) = 10 →
        (if Nat.count (fun i => raw i = 9) (y.regs Reg.level) = 0 then 0 else 1) = 0 := by
      intro hstar
      have hn := rawCubeDigit_no_fixed_before_star hπ hk hstar
      have hz : Nat.count (fun i => raw i = 9) (y.regs Reg.level) = 0 :=
        Nat.count_of_forall_not (fun i hi hh => hn ⟨i, hi, hh⟩)
      rw [hz]
      rfl
    obtain ⟨z, hz, hzm, hzl, hzp, hzc, hzs, hzf, hzv, hzi, hframe⟩ :=
      exec_lookupDigit y hk (rawCubeDigit_le_ten π _) (Nat.count_le _)
        (Nat.count_le _) (lookupCompletion_lt (fun i _ => rawCubeDigit_le_ten π i))
        hseenle horder hp.cube (by rw [hm]; exact hread _ hk) rfl hs hf hc hv hinv
        hpower hp.nil hp.one hp.nine hp.ten hfit
    have hpz : LookupParameters L C z :=
      ⟨(hframe _ (by decide)).trans hp.levels, (hframe _ (by decide)).trans hp.cube,
        (hframe _ (by decide)).trans hp.nil, (hframe _ (by decide)).trans hp.one,
        (hframe _ (by decide)).trans hp.nine, (hframe _ (by decide)).trans hp.ten⟩
    refine ⟨z, hz, ⟨hpz, hzm.trans hm, by omega, ?_, ?_, ?_, ?_, ?_, hzi⟩, by omega⟩
    · simpa only [hzl] using hzp
    · simpa only [hzl, lookupCompletion] using hzc
    · simpa only [hzl, Nat.count_succ] using hzs
    · simpa only [hzl, Nat.count_succ] using hzf
    · rw [hzl, hzv, Nat.count_succ]
      by_cases hd : raw (y.regs Reg.level) = 9
      all_goals dsimp only [raw] at hd ⊢; simp [hd]
  obtain ⟨y, hy, hIy, hstop⟩ := ExecWithin.loop_invariant I
    (fun y => L - y.regs Reg.level) hb hi
  obtain ⟨hp, hm, hle, hpower, hc, hs, hf, _, hinv⟩ := hIy
  have hdone : y.regs Reg.level = L := by
    simp only [Cond.holds_lt, hp.levels, not_lt] at hstop
    omega
  refine ⟨y, ?_, hm, hp, hdone, ?_, ?_, ?_, ?_, hinv,
    fun i hi => hy.regs_eq (lookupLoop_preserves i hi)⟩
  · simpa only [hlevel, Nat.sub_zero, Nat.mul_comm] using hy
  · simpa only [hdone] using hpower
  · simpa only [hdone, raw, lookupCompletion_rawCubeDigit] using hc
  · simpa only [hdone, raw, count_rawCubeDigit_stars] using hs
  · simpa only [hdone, raw, count_rawCubeDigit_population] using hf

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable
