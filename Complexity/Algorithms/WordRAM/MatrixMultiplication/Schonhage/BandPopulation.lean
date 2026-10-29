/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandProgram
public import Complexity.Algorithms.MatrixMultiplication.Schonhage.MaskTable

/-!
# Charged native binary-mask population scans

## Main results

* `BandPreparation.exec_population`: the actual remainder/division loop computes the
  population in `6L+5` instructions, preserves memory and changes only its four local registers.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandPreparation

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open Cslib.Algorithms.MatrixMultiplication.Schonhage.MaskTable

/-- Popcount is a native loop, with a fit derived for each arithmetic operation from a
bound on its original mask and depth. No memory cell is touched. -/
theorem exec_population {w : ℕ} (L a : ℕ) (x : Data 96)
    (hl : x.regs levels = L) (ha : x.regs mask = a)
    (ho : x.regs one = 1) (ht : x.regs two = 2) (hfit : Fits w (a + L + 2)) :
    ∃ y, ExecWithin w populationCode x y (6 * L + 5) ∧
      y.regs population = MaskTable.population L a ∧ y.mem = x.mem ∧
      (∀ i, i ≠ residue → i ≠ population → i ≠ counter → i ≠ digit →
        y.regs i = x.regs i) := by
  have hzero : Fits w 0 := hfit.of_le (by omega)
  let start := ((x.set residue a).set population 0).set counter 0
  let I (y : Data 96) : Prop :=
    y.mem = x.mem ∧ y.regs levels = L ∧ y.regs one = 1 ∧ y.regs two = 2 ∧
      y.regs counter ≤ L ∧ y.regs residue ≤ a ∧
      y.regs population + MaskTable.population (L - y.regs counter) (y.regs residue) =
        MaskTable.population L a
  have hi : I start := by
    simp [I, start, hl, ho, ht, counter, residue, population, levels, one, two]
  have hb (y : Data 96) (hy : I y) (hc : (Cond.lt counter levels).Holds y) :
      ∃ z, ExecWithin w (ram[
          digit ← residue % two; population ← population + digit;
          residue ← residue / two; counter ← counter + one ]) y z 4 ∧
        I z ∧ L - z.regs counter < L - y.regs counter := by
    obtain ⟨hm, hL, h1, h2, hj, hr, hp⟩ := hy
    have hjL : y.regs counter < L := by simpa only [Cond.holds_lt, hL] using hc
    have hrec : MaskTable.population (L - y.regs counter) (y.regs residue) =
        y.regs residue % 2 +
          MaskTable.population (L - (y.regs counter + 1)) (y.regs residue / 2) := by
      rw [show L - y.regs counter = (L - (y.regs counter + 1)) + 1 by omega,
        population_succ]
    have hpop := population_le L a
    have hfpop : Fits w (y.regs population + y.regs residue % 2) :=
      hfit.of_le (by omega)
    have hfmod : Fits w (y.regs residue % 2) := hfit.of_le (by omega)
    have hfdiv : Fits w (y.regs residue / 2) :=
      hfit.of_le ((Nat.div_le_self _ _).trans (by omega))
    have hfnext : Fits w (y.regs counter + 1) := hfit.of_le (by omega)
    let z := (((y.set digit (y.regs residue % 2)).set population
      (y.regs population + y.regs residue % 2)).set residue (y.regs residue / 2)).set
      counter (y.regs counter + 1)
    have he : ExecWithin w (ram[
        digit ← residue % two; population ← population + digit;
        residue ← residue / two; counter ← counter + one ]) y z 4 := by
      ram_eval [z, hfpop, hfmod, hfdiv, hfnext, h1, h2,
        digit, residue, population, counter, one, two, Fin.mk.injEq]
    refine ⟨z, he, ?_, ?_⟩
    · have hsum : (y.regs population + y.regs residue % 2) +
          MaskTable.population (L - (y.regs counter + 1)) (y.regs residue / 2) =
            MaskTable.population L a := by omega
      simpa +decide [I, z, levels, one, two, residue, population, counter, digit,
        Function.update_apply] using
        (show y.mem = x.mem ∧ y.regs levels = L ∧ y.regs one = 1 ∧ y.regs two = 2 ∧
          y.regs counter + 1 ≤ L ∧ y.regs residue / 2 ≤ a ∧
          (y.regs population + y.regs residue % 2) +
            MaskTable.population (L - (y.regs counter + 1)) (y.regs residue / 2) =
              MaskTable.population L a from
          ⟨hm, hL, h1, h2, by omega, (Nat.div_le_self _ _).trans hr, hsum⟩)
    · simp only [z, Data.set_regs, Function.update_self]
      omega
  obtain ⟨y, he, hy, hc⟩ := ExecWithin.loop_invariant I
    (fun y => L - y.regs counter) hb hi
  have hj : y.regs counter = L := by
    simp only [Cond.holds_lt, hy.2.1] at hc
    have := hy.2.2.2.2.1
    omega
  have hwhole : ExecWithin w populationCode x y (6 * L + 5) := by
    have hs : ExecWithin (B := .standard) w (.op (.copy residue mask))
        x (x.set residue a) 1 := by
      simpa only [ha] using (ExecWithin.copy (B := .standard) (w := w)
        (x := x) (d := residue) (s := mask))
    have hwhole := hs.seq ((ExecWithin.const (d := population) hzero).seq
      ((ExecWithin.const (d := counter) hzero).seq he))
    apply hwhole.mono
    simp only [start, Data.set_regs, Function.update_self, Nat.sub_zero]
    omega
  refine ⟨y, hwhole, ?_, hy.1, ?_⟩
  · have h := hy.2.2.2.2.2.2
    simpa only [hj, Nat.sub_self, population_zero, Nat.add_zero] using h
  · intro i hr hp hc hd
    apply hwhole.regs_eq
    have hframe : ∀ i : Fin 96, i ≠ residue → i ≠ population → i ≠ counter → i ≠ digit →
        populationCode.Preserves i := by decide
    exact hframe i hr hp hc hd

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandPreparation
