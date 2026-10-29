/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandPopulation

/-!
# Native counting of all valid subset masks

## Main results

* `BandPreparation.exec_countMasks`: the complete binary-mask scan computes the binomial
  coefficient, with its inner population loops and all outer controls charged.
-/

@[expose] public section

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
  let I (y : Data 96) : Prop :=
    y.mem = x.mem ∧ y.regs levels = L ∧ y.regs inner = m ∧ y.regs masks = 2 ^ L ∧
      y.regs one = 1 ∧ y.regs two = 2 ∧ y.regs mask ≤ 2 ^ L ∧
      y.regs count = prefixCount L m (y.regs mask)
  have hi : I start := by
    simp [I, start, hL, hm, hM, h1, h2, levels, inner, masks, one, two, mask, count,
      prefixCount_zero]
  have hb (y : Data 96) (hy : I y) (hc : (Cond.lt mask masks).Holds y) :
      ∃ z, ExecWithin w countBody y z (6 * L + 9) ∧ I z ∧
        2 ^ L - z.regs mask < 2 ^ L - y.regs mask := by
    obtain ⟨hmem, hL, hm, hM, h1, h2, ht, hcount⟩ := hy
    have htlt : y.regs mask < 2 ^ L := by simpa only [Cond.holds_lt, hM] using hc
    obtain ⟨u, hu, hpop, humem, huf⟩ := exec_population L (y.regs mask) y hL rfl h1 h2
      (hfit.of_le (by omega))
    have hul : u.regs levels = L :=
      (huf levels (by decide) (by decide) (by decide) (by decide)).trans hL
    have hui : u.regs inner = m :=
      (huf inner (by decide) (by decide) (by decide) (by decide)).trans hm
    have huM : u.regs masks = 2 ^ L :=
      (huf masks (by decide) (by decide) (by decide) (by decide)).trans hM
    have hu1 : u.regs one = 1 :=
      (huf one (by decide) (by decide) (by decide) (by decide)).trans h1
    have hu2 : u.regs two = 2 :=
      (huf two (by decide) (by decide) (by decide) (by decide)).trans h2
    have hut : u.regs mask = y.regs mask :=
      huf mask (by decide) (by decide) (by decide) (by decide)
    have huc : u.regs count = prefixCount L m (y.regs mask) :=
      (huf count (by decide) (by decide) (by decide) (by decide)).trans hcount
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
    refine ⟨z, hu.seq hz, ?_, ?_⟩
    · simpa +decide [I, z, levels, inner, masks, one, two, mask, count,
        Function.update_apply] using
        (show u.mem = x.mem ∧ u.regs levels = L ∧ u.regs inner = m ∧
          u.regs masks = 2 ^ L ∧ u.regs one = 1 ∧ u.regs two = 2 ∧
          y.regs mask + 1 ≤ 2 ^ L from
          ⟨humem.trans hmem, hul, hui, huM, hu1, hu2, by omega⟩)
    · have hzt : z.regs mask = y.regs mask + 1 := by simp [z]
      rw [hzt]
      omega
  obtain ⟨y, he, hy, hc⟩ := ExecWithin.loop_invariant I
    (fun y => 2 ^ L - y.regs mask) hb hi
  have ht : y.regs mask = 2 ^ L := by
    simp only [Cond.holds_lt, hy.2.2.2.1] at hc
    have := hy.2.2.2.2.2.2.1
    omega
  have hwhole : ExecWithin w countMasks x y ((6 * L + 11) * 2 ^ L + 4) := by
    apply (hs.seq he).mono
    have hs0 : start.regs mask = 0 := by simp [start, mask, count]
    rw [hs0, Nat.sub_zero]
    nlinarith
  refine ⟨y, hwhole, ?_, ht, hy.1, ?_⟩
  · have h := hy.2.2.2.2.2.2.2
    simpa only [ht, prefixCount_full] using h
  · intro i hm hc hr hp hj hd
    apply hwhole.regs_eq
    have hf : ∀ i : Fin 96, i ≠ mask → i ≠ count → i ≠ residue → i ≠ population →
        i ≠ counter → i ≠ digit → countMasks.Preserves i := by
      simp only [countMasks, countBody, populationCode, Code.Preserves, Op.dest, Op.bin]
      decide
    exact hf i hm hc hr hp hj hd

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandPreparation
