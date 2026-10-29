/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.NodeRound
public import Complexity.Computability.WordRAM.Signed.Fits

/-!
# Complete native Chan–He node construction

The parent supplies three injective signed-encoded input arrays ending before a fresh allocation
base, a positive modulus `M`, `N ≥ 2M`, and magnitude bound `U`. The fixed native program computes
all residues/histograms, the three exact compact heavy arrays and the existing `Node.oneArray`
in `4N` cells. Initialization, tags, address calculations, all called code and count stores are
charged. A single polynomial envelope derives every arithmetic/address fit.

## Main results

* `NodePacking.exec`: complete native execution in `66(n₀+n₁+n₂)+15M+12N+228` instructions.
* `NodePacking.time_le_linear`: a uniform linear instruction bound.

Prime selection, the frontend, recursion, global `State.init` composition and the global width
and preprocessing asymptotics remain the responsibility of the parent construction.

## References

* [T. M. Chan and Q. He, *Reducing 3SUM to Convolution-3SUM*][ChanHe2020]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.NodePacking

open Cslib.WordRAM Cslib.WordRAM.Signed

/-- Complete node work, with only actual supplied array contents and one explicit polynomial
width envelope as premises. The instruction bound excludes the final halt. -/
theorem exec {w : ℕ} (x : Data 64) (values : Fin 3 → ℕ → ℤ)
    (hM : 0 < (layout x).M) (hN : 2 * (layout x).M ≤ (layout x).N)
    (hwidth : GenericRAM.Signed.Fits w ((layout x).budget : ℤ))
    (hsrc : ∀ j, x.regs (source j) + (layout x).n j ≤ (layout x).base)
    (hbdd : ∀ j i, i < (layout x).n j → (values j i).natAbs ≤ (layout x).U)
    (hinput : ∀ j i, i < (layout x).n j →
      x.mem (x.regs (source j) + i) = encode (values j i))
    (hinj : ∀ j, Set.InjOn (values j) (↑(Finset.range ((layout x).n j)) : Set ℕ)) :
    ∃ y, ExecWithin (w + 2) program x y
        (66 * (layout x).total + 15 * (layout x).M + 12 * (layout x).N + 228) ∧
      y.mem = memory (layout x) values x.mem ∧ Parameters x y := by
  let L := layout x
  have hfit : Fits (w + 2) L.budget := unsigned_fits_of_signed hwidth
  have hwidth' : GenericRAM.Signed.Fits w (L.budget : ℤ) := hwidth
  have hM' : 0 < L.M := hM
  have hN' : 2 * L.M ≤ L.N := hN
  have hmod : GenericRAM.Signed.Fits w (L.M : ℤ) := hwidth'.of_natAbs_le
    (by simpa only [Int.natAbs_natCast] using
      (show L.M ≤ L.budget by have := L.bounds.2.2; omega))
  have hu : L.U ≤ L.budget := by have := L.bounds.2.2; omega
  have hsigned (j : Fin 3) (i : ℕ) (hi : i < L.n j) :
      GenericRAM.Signed.Fits w (values j i) :=
    hwidth'.of_natAbs_le ((hbdd j i hi).trans hu)
  let R (y : Data 64) : Prop := Parameters x y ∧ Prepared L y ∧
    ∀ a < L.base, y.mem a = x.mem a
  obtain ⟨a, ha, hap, har, ham⟩ := exec_initialize x hfit
  have hRa : R a := by
    refine ⟨hap, har, ?_⟩
    intro b hb
    rw [ham]
    have hp : L.base ≤ L.packed := by dsimp only [Layout.packed]; omega
    have hnot : ¬(L.packed ≤ b ∧ b < L.packed + 4 * L.N) := by omega
    change paddingMemory L x.mem b = x.mem b
    simp only [paddingMemory, Padding.memory, hnot, ↓reduceIte]
  have hcall (j : Fin 3) (y : Data 64) (hy : R y) :
      ∃ z, ExecWithin (w + 2) (round j) y z (66 * L.n j + 5 * L.M + 65) ∧
        R z ∧ z.mem = roundMemory L values j y.mem := by
    obtain ⟨hp, hr, hm⟩ := hy
    obtain ⟨z, hz, hzm, _, hzp, hzr⟩ := exec_round x y values j hp hr hfit hM' hN' hmod
      (hsrc j) (hbdd j) (hsigned j)
      (by
        intro i hi
        have hi' : i < L.n j := hi
        have hsi := hsrc j
        have hsi' : x.regs (source j) + L.n j ≤ L.base := hsi
        rw [hm _ (by omega)]
        exact hinput j i hi)
      (hinj j)
    refine ⟨z, hz, ⟨hzp, hzr, ?_⟩, hzm⟩
    intro b hb
    rw [hzm, roundMemory_before L values j y.mem hM' hN'
      (lt_of_lt_of_le hb (L.base_le_descriptor j)), hm b hb]
  obtain ⟨b, hb, hRb, hbm⟩ := hcall 0 a hRa
  obtain ⟨c, hc, hRc, hcm⟩ := hcall 1 b hRb
  obtain ⟨d, hd, hRd, hdm⟩ := hcall 2 c hRc
  refine ⟨d, (ha.seq (hb.seq (hc.seq hd))).mono (by dsimp only [L, Layout.total]; omega),
    ?_, hRd.1⟩
  rw [hdm, hcm, hbm, ham]
  rfl

/-- The complete charged bound is uniformly linear in input lengths, modulus and output length. -/
theorem time_le_linear (L : Layout) :
    66 * L.total + 15 * L.M + 12 * L.N + 228 ≤ 256 * (L.total + L.M + L.N + 1) := by
  omega

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.NodePacking
