/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable.Program

/-!
# Actual cube-digit lookup step

The native scan reads a real cube digit, checks its alphabet and order, and updates
the completed-leaf code and star/P0 counts. The step theorem consumes ordinary scalar
and memory readback, with all intermediate fits derived from one address/depth envelope.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable

open Cslib.WordRAM

/-- Registers modified by the actual lookup digit scan. -/
@[expose] def LookupLocal (i : Fin registers) : Prop :=
  i = Reg.address ∨ i = Reg.digit ∨ i = Reg.invalid ∨ i = Reg.fixedSeen ∨
    i = Reg.stars ∨ i = Reg.population ∨ i = Reg.temporary ∨ i = Reg.completion ∨
    i = Reg.power ∨ i = Reg.level

instance (i : Fin registers) : Decidable (LookupLocal i) :=
  inferInstanceAs (Decidable (i = Reg.address ∨ i = Reg.digit ∨ i = Reg.invalid ∨
    i = Reg.fixedSeen ∨ i = Reg.stars ∨ i = Reg.population ∨ i = Reg.temporary ∨
    i = Reg.completion ∨ i = Reg.power ∨ i = Reg.level))

private theorem lookupDigit_preserves (i : Fin registers) :
    ¬LookupLocal i → lookupDigit.Preserves i := by decide +revert

/-- The real scan preserves a valid prefix and charges both failed branch instructions. -/
theorem exec_lookupDigit {w L k C d s f c v : ℕ} (x : Data registers)
    (hk : k < L) (hd : d ≤ 10) (hs : s ≤ k) (hf : f ≤ k)
    (hc : c < 10 ^ k) (_hv : v ≤ 1) (horder : d = 10 → v = 0)
    (hC : x.regs Reg.cube = C) (hread : x.mem (C + k) = d)
    (hlevel : x.regs Reg.level = k) (hstars : x.regs Reg.stars = s)
    (hpop : x.regs Reg.population = f) (hcode : x.regs Reg.completion = c)
    (hseen : x.regs Reg.fixedSeen = v) (hinvalid : x.regs Reg.invalid = 0)
    (hpow : x.regs Reg.power = 10 ^ k) (h0 : x.regs Reg.nil = 0)
    (h1 : x.regs Reg.one = 1) (h9 : x.regs Reg.nine = 9)
    (h10 : x.regs Reg.ten = 10)
    (hfit : Fits w (C + 10 ^ L + L + 20)) :
    ∃ y, ExecWithin w lookupDigit x y 16 ∧ y.mem = x.mem ∧
      y.regs Reg.level = k + 1 ∧ y.regs Reg.power = 10 ^ (k + 1) ∧
      y.regs Reg.completion = c + (if d = 10 then 9 else d) * 10 ^ k ∧
      y.regs Reg.stars = s + (if d = 10 then 1 else 0) ∧
      y.regs Reg.population = f + (if d = 9 ∨ d = 10 then 1 else 0) ∧
      y.regs Reg.fixedSeen = (if d = 9 then 1 else v) ∧ y.regs Reg.invalid = 0 ∧
      (∀ i, ¬LookupLocal i → y.regs i = x.regs i) := by
  let digit := if d = 10 then 9 else d
  have hdn : digit ≤ 9 := by dsimp only [digit]; split <;> omega
  have hpowle : 10 ^ (k + 1) ≤ 10 ^ L :=
    Nat.pow_le_pow_right (by decide) (Nat.succ_le_of_lt hk)
  have hcnext : c + digit * 10 ^ k < 10 ^ (k + 1) := by
    rw [pow_succ]
    have := Nat.mul_le_mul_right (10 ^ k) hdn
    omega
  have hfa : Fits w (C + k) := hfit.of_le (by omega)
  have hfl : Fits w (k + 1) := hfit.of_le (by omega)
  have hfs : Fits w (s + 1) := hfit.of_le (by omega)
  have hff : Fits w (f + 1) := hfit.of_le (by omega)
  have hf0 : Fits w 0 := hfit.of_le (Nat.zero_le _)
  have hf1 : Fits w 1 := hfit.of_le (by omega)
  have hfm : Fits w (digit * 10 ^ k) := hfit.of_le (by omega)
  have hfc : Fits w (c + digit * 10 ^ k) := hfit.of_le (by omega)
  have hfp : Fits w (10 ^ k * 10) := by
    rw [← pow_succ]
    exact hfit.of_le (by omega)
  let loaded := (x.set Reg.address (C + k)).set Reg.digit d
  let checked := loaded.set Reg.temporary (x.regs Reg.temporary)
  let starred := (((checked.set Reg.temporary (x.regs Reg.temporary)).set
    Reg.stars (s + 1)).set Reg.population (f + 1)).set Reg.digit 9
  let counted := if d = 10 then starred
    else if d = 9 then (checked.set Reg.fixedSeen 1).set Reg.population (f + 1)
    else checked.set Reg.temporary (x.regs Reg.temporary)
  let y := (((counted.set Reg.temporary (digit * 10 ^ k)).set
    Reg.completion (c + digit * 10 ^ k)).set Reg.power (10 ^ k * 10)).set Reg.level (k + 1)
  have he : ExecWithin w lookupDigit x y 16 := by
    by_cases hd10 : d = 10 <;> by_cases hd9 : d = 9
    all_goals
      try omega
    all_goals
      simp +decide only [digit, hd10, hd9, ite_true, ite_false] at hfm hfc
      have hn10 : ¬10 < d := by omega
      have hv0 : d = 10 → ¬0 < v := by intro h; rw [horder h]; omega
      ram_eval [lookupDigit, y, counted, starred, checked, loaded, digit, hd10, hd9, hn10,
        hv0, horder, hC, hread, hlevel, hstars, hpop, hcode, hseen, hinvalid, hpow,
        h0, h1, h9, h10, hfa, hfl, hfs, hff, hf0, hf1, hfm, hfc, hfp,
        Reg.address, Reg.digit, Reg.invalid, Reg.fixedSeen, Reg.stars, Reg.population,
        Reg.temporary, Reg.completion, Reg.power, Reg.level, Reg.cube, Reg.nil,
        Reg.one, Reg.nine, Reg.ten, Fin.mk.injEq]
  refine ⟨y, he, by dsimp only [y, counted]; split <;> first | rfl | (split <;> rfl),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun i hi => he.regs_eq (lookupDigit_preserves i hi)⟩
  all_goals
    by_cases hd10 : d = 10 <;> by_cases hd9 : d = 9
    all_goals simp_all [y, counted, starred, checked, loaded, digit,
      Reg.address, Reg.digit, Reg.invalid, Reg.fixedSeen, Reg.stars, Reg.population,
      Reg.temporary, Reg.completion, Reg.power, Reg.level, pow_succ]

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable
