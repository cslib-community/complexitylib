/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.NodeInitialize

/-!
# Complete charged native rounds of a Chan–He node

## Main definitions

* `NodePacking.CallArgs`: exact runtime delivery to the existing complete counting/placement code.

## References

These native setup and composition proofs are original.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.NodePacking

open Cslib.WordRAM

/-- Exact runtime parameters delivered to one complete counting/placement call. -/
structure CallArgs (L : Layout) (s : Fin 3 → ℕ) (j : Fin 3) (x : Data 64) : Prop where
  /-- Actual input length. -/
  len : x.regs CountPlace.len = L.n j
  /-- Actual signed input base. -/
  src : x.regs CountPlace.src = s j
  /-- Computed residue workspace. -/
  scratch : x.regs CountPlace.scratch = L.scratch
  /-- Computed histogram workspace. -/
  hist : x.regs CountPlace.hist = L.hist
  /-- Computed compact heavy data base. -/
  heavy : x.regs CountPlace.heavy = L.heavy j
  /-- Computed packed array base. -/
  packed : x.regs CountPlace.packed = L.packed
  /-- Actual positive modulus. -/
  modulus : x.regs CountPlace.modulus = L.M
  /-- Exact encoded positive tag. -/
  tag : x.regs CountPlace.tag = 2 * L.tag j
  /-- Packed column. -/
  column : x.regs CountPlace.column = j.val + 1
  /-- Duplicate-store offset. -/
  distance : x.regs CountPlace.distance = if j = 2 then 4 * L.M else 0
  /-- Sign multiplier flag. -/
  negative : x.regs CountPlace.negative = if j = 2 then 1 else 0
  /-- Computed descriptor/count cell. -/
  descriptor : x.regs CountPlace.descriptor = L.descriptor j

/-- Runtime argument delivery keeps all persistent caller registers. -/
theorem prepare_preserves (j : Fin 3) (i : Fin 64) (hi : 46 ≤ i.val) (hne : i ≠ temporary) :
    (prepare j).Preserves i := by
  have h : 46 ≤ i.val ∧ i ≠ temporary := ⟨hi, hne⟩
  fin_cases j <;> fin_cases i <;> norm_num [temporary] at h <;> decide

/-- Every complete native round retains the caller arguments and prepared layout/constants. -/
theorem round_preserves (j : Fin 3) (i : Fin 64) (hi : 46 ≤ i.val) (hne : i ≠ temporary) :
    (round j).Preserves i := by
  change (prepare j).Preserves i ∧ CountPlace.program.Preserves i
  exact ⟨prepare_preserves j i hi hne, CountPlace.preserves i (by omega)
    (by intro he; subst i; norm_num [CountCall.modulus] at hi)
    (by intro he; subst i; norm_num [CountCall.result] at hi)⟩

/-- All count/place arguments are computed from actual retained caller values in at most
twenty instructions. In particular no output pointer or encoded tag is supplied for free. -/
theorem exec_prepare {w : ℕ} (x y : Data 64) (j : Fin 3)
    (hparams : Parameters x y) (hready : Prepared (layout x) y)
    (hfit : Fits w (layout x).budget) (hN : 2 * (layout x).M ≤ (layout x).N) :
    ∃ q, ExecWithin w (prepare j) y q 20 ∧
      CallArgs (layout x) (fun j => x.regs (source j)) j q ∧ q.mem = y.mem := by
  let L := layout x
  have hfit' : Fits w L.budget := hfit
  have hN' : 2 * L.M ≤ L.N := hN
  obtain ⟨hk, hh, hp, hg, hpad, h1, h4⟩ := hready
  have hl (k : Fin 3) : y.regs (length k) = L.n k :=
    hparams _ (by dsimp only [length]; omega)
  have hs (k : Fin 3) : y.regs (source k) = x.regs (source k) :=
    hparams _ (by dsimp only [source]; omega)
  have hb : y.regs base = L.base := hparams _ (by decide)
  have hm : y.regs modulus = L.M := hparams _ (by decide)
  have f (v : ℕ) (hv : v ≤ L.packed) : Fits w v :=
    (hfit'.of_le L.bounds.1).of_le (by
      dsimp only [Layout.endpoint, Layout.hist, Layout.scratch]
      omega)
  have fc (v : ℕ) (hv : v ≤ 16) : Fits w v := hfit'.of_le (by have := L.bounds.2.2; omega)
  have fm (v : ℕ) (hv : v ≤ 120 * L.U + 80) : Fits w v :=
    (hfit'.of_le L.bounds.2.1).of_le hv
  have f0 : Fits w 0 := fits_zero _
  have f1 : Fits w 1 := fc _ (by decide)
  have f2 : Fits w 2 := fc _ (by decide)
  have f3 : Fits w 3 := fc _ (by decide)
  have fb₀ : Fits w (L.base + 1) := f _ (by dsimp only [Layout.packed]; omega)
  have fb₁ : Fits w (L.base + 1 + L.n 0) := f _ (by
    dsimp only [Layout.packed, Layout.total]; omega)
  have fb₂ : Fits w (L.base + 1 + L.n 0 + 1) := f _ (by
    dsimp only [Layout.packed, Layout.total]; omega)
  have fb₃ : Fits w (L.base + 1 + L.n 0 + 1 + L.n 1) := f _ (by
    dsimp only [Layout.packed, Layout.total]; omega)
  have fo₁ : Fits w (L.base + 1 + L.n 0 + 1) := fb₂
  have fo₂ : Fits w (L.base + 1 + L.n 0 + 1 + L.n 1 + 1) := f _ (by
    dsimp only [Layout.packed, Layout.total]; omega)
  have ft₁ : Fits w (3 * (2 * L.gap)) := fm _ (by dsimp only [Layout.gap]; omega)
  have ft₂ : Fits w (4 * (2 * L.gap)) := fm _ (by dsimp only [Layout.gap]; omega)
  have fd : Fits w (4 * L.M) := (hfit'.of_le L.bounds.1).of_le (by
    dsimp only [Layout.endpoint, Layout.hist, Layout.scratch]
    omega)
  dsimp only [L] at *
  fin_cases j <;> simp only [Fin.mk_zero, Fin.mk_one]
  all_goals
    refine ⟨?_, ?_, ?_, ?_⟩
    rotate_left
    · ram_eval [prepare, descriptorCode, tagCode, distanceCode, Fin.val_zero, Fin.val_one,
        hk, hh, hp, hg, h1, h4, hl, hs, hb, hm, f0, f1, f2, f3,
        fb₀, fb₁, fb₂, fb₃, fo₁, fo₂, ft₁, ft₂, fd]
    · constructor <;>
        simp +decide [CountPlace.len, CountPlace.src, CountPlace.scratch,
          CountPlace.hist, CountPlace.heavy, CountPlace.packed, CountPlace.modulus,
          CountPlace.tag, CountPlace.column, CountPlace.distance, CountPlace.negative,
          CountPlace.descriptor, Layout.heavy, Layout.descriptor, Layout.tag, layout,
          source, length] <;> omega
    · rfl

/-- A complete native round, with all actual counting calls discharged and all pointer,
tag, duplicate-store and count-descriptor work charged. -/
theorem exec_round {w : ℕ} (x y : Data 64) (values : Fin 3 → ℕ → ℤ) (j : Fin 3)
    (hparams : Parameters x y) (hready : Prepared (layout x) y)
    (hfit : Fits (w + 2) (layout x).budget)
    (hM : 0 < (layout x).M) (hN : 2 * (layout x).M ≤ (layout x).N)
    (hmod : GenericRAM.Signed.Fits w ((layout x).M : ℤ))
    (hsrc : x.regs (source j) + (layout x).n j ≤ (layout x).base)
    (hbdd : ∀ i < (layout x).n j, (values j i).natAbs ≤ (layout x).U)
    (hsigned : ∀ i < (layout x).n j, GenericRAM.Signed.Fits w (values j i))
    (hinput : ∀ i < (layout x).n j, y.mem (x.regs (source j) + i) =
      Signed.encode (values j i))
    (hinj : Set.InjOn (values j) (↑(Finset.range ((layout x).n j)) : Set ℕ)) :
    ∃ z, ExecWithin (w + 2) (round j) y z (66 * (layout x).n j + 5 * (layout x).M + 65) ∧
      z.mem = roundMemory (layout x) values j y.mem ∧ Frame y z ∧
      Parameters x z ∧ Prepared (layout x) z := by
  let L := layout x
  have hsrc' : x.regs (source j) + L.n j ≤ L.base := hsrc
  obtain ⟨q, hp, hq, hqm⟩ := exec_prepare x y j hparams hready hfit hN
  have hf : Fits (w + 2) (CountPlace.budget q L.M L.N L.U (L.tag j)) := by
    rw [CountPlace.budget, hq.src, hq.scratch, hq.hist, hq.heavy, hq.packed, hq.len]
    exact hfit.of_le (L.count_budget_le j _ _ (by omega) (L.tag_bounds j).2)
  have hn := L.n_le_total j
  obtain ⟨z, hz, hzm, _⟩ := CountPlace.exec q (values j) (decide (j = 2)) hM hmod
    hq.modulus hN (L.tag_bounds j).1 hq.tag
    (by by_cases hj : j = 2 <;> simpa [hj] using hq.negative)
    (by rw [hq.column]; omega) (by rw [hq.distance]; split_ifs <;> omega)
    (by simpa only [hq.len] using hbdd) (by simpa only [hq.len] using hsigned) hf
    (by
      rw [hq.src, hq.len, hq.heavy]
      have hd : (layout x).base ≤ (layout x).descriptor j := L.base_le_descriptor j
      dsimp only [Layout.heavy]
      omega)
    (by rw [hq.heavy, hq.len, hq.packed]; exact L.heavy_end_le_packed j)
    (by rw [hq.packed, hq.scratch]; rfl)
    (by rw [hq.scratch, hq.len, hq.hist]; exact Nat.add_le_add_left hn _)
    (by simpa only [hq.len, hq.src, hqm] using hinput)
    (by simpa only [hq.len] using hinj)
  have he : ExecWithin (w + 2) (round j) y z (66 * L.n j + 5 * L.M + 65) := by
    have hz' : ExecWithin (w + 2) CountPlace.program q z (66 * L.n j + 5 * L.M + 45) :=
      by simpa only [hq.len] using hz
    exact (hp.seq hz').mono (by omega)
  have hframe : Frame y z := fun i hi hne => ExecWithin.regs_eq he (round_preserves j i hi hne)
  refine ⟨z, he, ?_, hframe, hparams.of_frame hframe, hready.of_frame hframe⟩
  rw [hzm, hqm, hq.len, hq.heavy, hq.packed, hq.column, hq.distance,
    hq.scratch, hq.hist, hq.descriptor]
  rfl

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.NodePacking
