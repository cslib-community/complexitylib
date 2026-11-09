/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Product.Tile
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Actual all-tile execution with shared encodings and epochs

## Main definitions

* `QueriedProduct.tileCharge`: the charge of one actual tile call and its outer loop control.

## Main results

* `QueriedProduct.exec_evaluateTiles`: every original request receives its exact matrix-product
  value in grouped order, while actual returned epochs retain one shared timestamp directory.

The finite charge uses original coordinate occurrences and the existing pruned trace count.
The proof derives it from executed spans and calls. No sparse bound is assumed.
-/

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open scoped BigOperators

/-- Per-tile analysis of the actual program, including call setup, returned epoch/index
updates and two outer-loop instructions. Duplicate coordinate occurrences remain charged. -/
@[expose] public def tileCharge {L m N : ℕ} (hm : m ≤ L)
    (qs : List (Fin N × Fin N)) (t : ℕ) : ℕ :=
  4 * L + 29 * Nat.count (fun i => (Wanted.tileKey L m N ∘ Wanted.inputPairs qs) i = t)
    qs.length + PrunedQuery.traceWeight
      (wantedStrings (MaskTable.layout hm) qs.toFinset (t / numBands L m N)
        (t % numBands L m N)) + 66

private structure Progress {L m N : ℕ} (hm : m ≤ L)
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ)
    (qs : List (Fin N × Fin N)) (old initial : ℕ → ℕ) (z : Data 160) : Prop where
  fixed : Parameters L m N qs.length z
  index_le : z.regs Reg.index ≤ numBands L m N ^ 2
  epoch_le : z.regs Reg.epoch ≤ z.regs Reg.index * (1 + PrunedQuery.epochAllowance L)
  groups : SavedGroups L m N qs.length old z.mem
  catalogue : EncodedBands hm X Y z.mem
  marks : ∀ j < 10 ^ L, z.mem (stampBase L m N qs.length + j) ≤ z.regs Reg.epoch
  answers : ∀ i : Fin qs.length,
    (Wanted.tileKey L m N ∘ Wanted.inputPairs qs) i.val < z.regs Reg.index →
      z.mem (groupedBase L m N qs.length +
          CountingSort.position (Wanted.tileKey L m N ∘ Wanted.inputPairs qs) qs.length i) =
        Signed.encode ((X * Y) (qs.get i).1 (qs.get i).2)
  frame : ∀ p, ¬(groupedBase L m N qs.length ≤ p ∧ p < outputBase L m N qs.length) →
    ¬(scratchBase L m N qs.length ≤ p ∧ p < memoryEnd L m N qs.length) → z.mem p = initial p

/-- Every real tile is evaluated by the same fixed program. The zero-band case exits without
division, and repeated requested coordinates retain their distinct grouped positions. -/
public theorem exec_evaluateTiles {w L m N A : ℕ} (hw : 0 < w) (hm : m ≤ L)
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ)
    (qs : List (Fin N × Fin N)) (old : ℕ → ℕ) (x : Data 160)
    (hp : Parameters L m N qs.length x) (hi : x.regs Reg.index = 0) (hE : x.regs Reg.epoch = 0)
    (hg : SavedGroups L m N qs.length old x.mem) (he : EncodedBands hm X Y x.mem)
    (hvalues : ∀ i : Fin qs.length,
      old (Wanted.codeAddress L m N qs.length +
          CountingSort.position (Wanted.tileKey L m N ∘ Wanted.inputPairs qs) qs.length i) =
        (PrunedQuery.queryIndex
          (outStrOfPos (MaskTable.layout hm) (qs.get i).1 (qs.get i).2)).val)
    (hoffsets : ∀ t ≤ numBands L m N ^ 2,
      old (Wanted.offsetAddress L m N qs.length + t) =
        Nat.count (fun k => (Wanted.tileKey L m N ∘ Wanted.inputPairs qs) k < t) qs.length)
    (hmarks : ∀ j < 10 ^ L, x.mem (stampBase L m N qs.length + j) = 0)
    (hX : ∀ i k, |X i k| ≤ (A : ℤ)) (hY : ∀ k j, |Y k j| ≤ (A : ℤ))
    (hmag : magnitudeBound L A < 2 ^ (w - 1))
    (hfit : Fits (w + 2) (wordBudget L m N qs.length)) :
    ∃ y, ExecWithin (w + 2) evaluateTiles x y
        ((∑ t ∈ Finset.range (numBands L m N ^ 2), tileCharge hm qs t) + 2) ∧
      Parameters L m N qs.length y ∧ SavedGroups L m N qs.length old y.mem ∧
      EncodedBands hm X Y y.mem ∧
      (∀ i : Fin qs.length,
        y.mem (groupedBase L m N qs.length +
            CountingSort.position (Wanted.tileKey L m N ∘ Wanted.inputPairs qs) qs.length i) =
          Signed.encode ((X * Y) (qs.get i).1 (qs.get i).2)) ∧
      (∀ p, ¬(groupedBase L m N qs.length ≤ p ∧ p < outputBase L m N qs.length) →
        ¬(scratchBase L m N qs.length ≤ p ∧ p < memoryEnd L m N qs.length) →
          y.mem p = x.mem p) := by
  let key := Wanted.tileKey L m N ∘ Wanted.inputPairs qs
  let T := numBands L m N ^ 2
  let I := Progress hm X Y qs old x.mem
  let Φ (z : Data 160) := ∑ t ∈ Finset.Ico (z.regs Reg.index) T, tileCharge hm qs t
  have hout : groupedBase L m N qs.length + qs.length = outputBase L m N qs.length := rfl
  have hfree : outputBase L m N qs.length ≤ scratchBase L m N qs.length := by
    unfold scratchBase
    omega
  have hstart : I x := ⟨hp, by rw [hi]; omega, by rw [hi, hE]; simp,
    hg, he, by intro j hj; rw [hmarks j hj, hE],
    by intro i hk; rw [hi] at hk; omega, by intro p _ _; rfl⟩
  have hbody (z : Data 160) (hz : I z) (hc : (Cond.lt Reg.index Reg.tiles).Holds z) :
      ∃ y C, ExecWithin (w + 2) tileStep z y C ∧ I y ∧ C + 2 + Φ y ≤ Φ z := by
    have ht : z.regs Reg.index < T := by simpa only [Cond.holds_lt, hz.fixed.tiles, T] using hc
    have hepoch : z.regs Reg.epoch ≤ epochBound L m N := by
      have h := hz.epoch_le.trans
        (Nat.mul_le_mul_right (1 + PrunedQuery.epochAllowance L) hz.index_le)
      simpa only [epochBound] using h
    obtain ⟨y, hr, yp, yi, _, yeu, yg, ye, ym, yvalues, yf⟩ := exec_tileStep hw hm X Y qs old z
      hz.fixed rfl ht rfl hepoch hz.groups hz.catalogue hvalues hoffsets hz.marks hX hY hmag hfit
    have ha := (hz.groups.offsets _ ht.le).trans (hoffsets _ ht.le)
    have hb := (hz.groups.offsets _ (Nat.succ_le_of_lt ht)).trans
      (hoffsets _ (Nat.succ_le_of_lt ht))
    have hdiff : z.mem (offsetBase L m N qs.length + z.regs Reg.index + 1) -
        z.mem (offsetBase L m N qs.length + z.regs Reg.index) =
      Nat.count (fun k => key k = z.regs Reg.index) qs.length := by
      rw [show offsetBase L m N qs.length + z.regs Reg.index + 1 =
          offsetBase L m N qs.length + (z.regs Reg.index + 1) by omega, hb, ha,
        CountingSort.count_lt_succ]
      dsimp only [key]
      omega
    rw [hdiff] at hr
    refine ⟨y, _, hr, ?_, ?_⟩
    · refine ⟨yp, by rw [yi]; omega, ?_, yg, ye, ym, ?_, ?_⟩
      · rw [yi, Nat.add_mul, Nat.one_mul]
        have h := hz.epoch_le
        omega
      · intro i hik
        change key i.val < y.regs Reg.index at hik
        by_cases hki : key i.val = z.regs Reg.index
        · exact yvalues i hki
        · have hold : key i.val < z.regs Reg.index := by rw [yi] at hik; omega
          have hs := (CountingSort.position_mem key i.isLt).2
          have hmcount : Nat.count (fun k => key k < key i.val + 1) qs.length ≤
              Nat.count (fun k => key k < z.regs Reg.index) qs.length :=
            Nat.count_mono_left (fun k _ hk => by omega)
          have hpos := CountingSort.position_lt key i.isLt
          dsimp only [key] at hs hmcount hpos
          rw [yf _ (by omega) (by omega)]
          exact hz.answers i hold
      · intro p ho hf
        have hbQ := (hz.groups.span_bounds key hoffsets ht).2
        rw [yf p (by omega) hf]
        exact hz.frame p ho hf
    · have hsplit := Finset.sum_eq_sum_Ico_succ_bot ht (tileCharge hm qs)
      dsimp only [Φ]
      rw [yi, hsplit]
      dsimp only [tileCharge, key]
      omega
  obtain ⟨y, hr, hy, hc⟩ := ExecWithin.loop_potential I Φ hbody hstart
  have hlast : y.regs Reg.index = T := by
    have h := hy.index_le
    simp only [Cond.holds_lt, hy.fixed.tiles] at hc
    dsimp only [T] at *
    omega
  refine ⟨y, ?_, hy.fixed, hy.groups, hy.catalogue, ?_, hy.frame⟩
  · simpa only [Φ, hi, Nat.Ico_zero_eq_range, T, evaluateTiles] using hr
  · intro i
    apply hy.answers i
    rw [hlast]
    have hk := Wanted.tileKey_lt hm (Wanted.inputPairs qs i.val)
      (Wanted.inputPairs_lt qs i i.isLt).1 (Wanted.inputPairs_lt qs i i.isLt).2
    exact hk

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct
