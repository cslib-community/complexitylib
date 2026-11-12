/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandPopulation

import CslibFrontier.Computability.WordRAM.CountingLoop

/-!
# Native counting of all valid subset masks

## Main results

* `BandPreparation.exec_countMasks`: the complete binary-mask scan computes the binomial
  coefficient, with its inner population loops and all outer controls charged.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandPreparation

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open MaskTable

/-- Scanning all masks computes `K L m`; neither that count nor a valid table is supplied
as an input. Every mask-counter and accepted-counter fit follows from the scan range. -/
theorem exec_countMasks {w : ℕ} (L m : ℕ) (x : Data 96)
    (hL : x.regs levels = L) (hm : x.regs inner = m) (hM : x.regs masks = 2 ^ L)
    (h1 : x.regs one = 1) (h2 : x.regs two = 2) (hfit : Fits w (2 ^ L + L + 4)) :
    ∃ y, ExecWithin w countMasks x y ((6 * L + 11) * 2 ^ L + 4) ∧
      y.regs count = K L m ∧ y.regs mask = 2 ^ L ∧ y.mem = x.mem ∧
      (∀ i, i ≠ mask → i ≠ count → i ≠ residue → i ≠ population → i ≠ counter →
        i ≠ digit → y.regs i = x.regs i) := by
  have h0 : Fits w 0 := hfit.of_le (by omega)
  let start := (x.set mask 0).set count 0
  have hs : ExecWithin (B := .standard) w (ram[ mask ← #0; count ← #0 ]) x start 2 := by
    ram_eval [start, h0, mask, count, Fin.mk.injEq]
  let P (j : ℕ) (y : Data 96) : Prop :=
    y.mem = x.mem ∧ y.regs levels = L ∧ y.regs inner = m ∧ y.regs masks = 2 ^ L ∧
      y.regs one = 1 ∧ y.regs two = 2 ∧
      y.regs count = prefixCount L m j
  have hi : P (start.regs mask) start := by
    simp [P, start, hL, hm, hM, h1, h2, levels, inner, masks, one, two, mask, count,
      prefixCount_zero]
  have hb (y : Data 96) (hy : P (y.regs mask) y) (htlt : y.regs mask < 2 ^ L) :
      ∃ z, ExecWithin w countBody y z (6 * L + 9) ∧ P (y.regs mask + 1) z ∧
        z.regs mask = y.regs mask + 1 := by
    obtain ⟨hmem, hL, hm, hM, h1, h2, hcount⟩ := hy
    obtain ⟨u, hu, hpop, humem, huf⟩ := exec_population L (y.regs mask) y hL rfl h1 h2
      (hfit.of_le (by omega))
    have hureg (r : Fin 96) (h1 : r ≠ residue := by decide) (h2 : r ≠ population := by decide)
        (h3 : r ≠ counter := by decide) (h4 : r ≠ digit := by decide) : u.regs r = y.regs r :=
      huf r h1 h2 h3 h4
    have hul : u.regs levels = L := (hureg levels).trans hL
    have hui : u.regs inner = m := (hureg inner).trans hm
    have huM : u.regs masks = 2 ^ L := (hureg masks).trans hM
    have hu1 : u.regs one = 1 := (hureg one).trans h1
    have hu2 : u.regs two = 2 := (hureg two).trans h2
    have hut : u.regs mask = y.regs mask := hureg mask
    have huc : u.regs count = prefixCount L m (y.regs mask) := (hureg count).trans hcount
    have hfnext : Fits w (y.regs mask + 1) := hfit.of_le (by omega)
    have hfc : Fits w (prefixCount L m (y.regs mask) + 1) :=
      hfit.of_le (by have := prefixCount_le L m (y.regs mask); omega)
    let z := (u.set count (prefixCount L m (y.regs mask + 1))).set mask (y.regs mask + 1)
    have hz : ExecWithin w (ram[
        if population = inner then [ count ← count + one ] else [ count ← count ];
        mask ← mask + one ]) u z 4 := by
      by_cases h : MaskTable.population L (y.regs mask) = m <;>
        ram_eval [z, prefixCount_succ, h, hpop, hui, hu1, hut, huc, hfnext, hfc,
          population, inner, count, one, mask, Fin.mk.injEq]
    refine ⟨z, hu.seq hz, ?_, by simp [z]⟩
    · simpa +decide [P, z, levels, inner, masks, one, two, mask, count,
        Function.update_apply] using
        (show u.mem = x.mem ∧ u.regs levels = L ∧ u.regs inner = m ∧
          u.regs masks = 2 ^ L ∧ u.regs one = 1 ∧ u.regs two = 2 from
          ⟨humem.trans hmem, hul, hui, huM, hu1, hu2⟩)
  obtain ⟨y, he, ⟨hymem, _, _, _, _, _, hycount⟩, ht⟩ := ExecWithin.loop_count P
    (fun y hy => hy.2.2.2.1) hb (by simp [start, mask, count]) hi
  have hwhole : ExecWithin w countMasks x y ((6 * L + 11) * 2 ^ L + 4) := by
    apply (hs.seq he).mono
    have hs0 : start.regs mask = 0 := by simp [start, mask, count]
    rw [hs0, Nat.sub_zero]
    nlinarith
  refine ⟨y, hwhole, ?_, ht, hymem, ?_⟩
  · simpa only [prefixCount_full] using hycount
  · intro i hm hc hr hp hj hd
    apply hwhole.regs_eq
    have hf : ∀ i : Fin 96, i ≠ mask → i ≠ count → i ≠ residue → i ≠ population →
        i ≠ counter → i ≠ digit → countMasks.Preserves i := by
      simp only [countMasks, countBody, populationCode, Code.Preserves, Op.dest, Op.bin]
      decide
    exact hf i hm hc hr hp hj hd

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandPreparation
