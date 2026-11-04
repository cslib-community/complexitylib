/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct.Tile
import Mathlib.Algebra.BigOperators.Intervals

/-!
# All routed tiles with one shared box geometry

Every actual group span is evaluated against the shared band encodings. The geometry
is never rebuilt by this loop; values, stack and temporary answers are reused. The
charged sum counts each original request occurrence only in its own tile.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct

open Cslib.WordRAM Cslib.Algorithms.MatrixMultiplication.Schonhage
open scoped BigOperators

private structure Progress {L m t N : ℕ} (hm : m ≤ L)
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ)
    (qs : List (Fin N × Fin N)) (old initial : ℕ → ℕ) (z : Data 160) : Prop where
  fixed : QueriedProduct.Parameters L m N qs.length z
  boxes : Parameters L m t N qs.length z
  index_le : z.regs QueriedProduct.Reg.index ≤ numBands L m N ^ 2
  groups : QueriedProduct.SavedGroups L m N qs.length old z.mem
  catalogue : QueriedProduct.EncodedBands hm X Y z.mem
  geometry : Geometry L m t N qs.length z.mem
  answers : ∀ i : Fin qs.length,
    (Wanted.tileKey L m N ∘ Wanted.inputPairs qs) i.val < z.regs QueriedProduct.Reg.index →
      z.mem (QueriedProduct.groupedBase L m N qs.length +
          CountingSort.position (Wanted.tileKey L m N ∘ Wanted.inputPairs qs) qs.length i) =
        Signed.encode ((X * Y) (qs.get i).1 (qs.get i).2)
  frame : ∀ p,
    ¬(QueriedProduct.groupedBase L m N qs.length ≤ p ∧
      p < QueriedProduct.outputBase L m N qs.length) →
    ¬(directoryBase L m N qs.length ≤ p ∧ p < memoryEnd L m t N qs.length) →
      z.mem p = initial p

/-- The fixed native loop evaluates every original wanted occurrence and preserves both
actual routing and shared encoding/geometry readback, with no tile/time oracle. -/
theorem exec_evaluateTiles {w L m t N A : ℕ} (hw : 0 < w) (hm : m ≤ L) (ht : t ≤ m)
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ)
    (qs : List (Fin N × Fin N)) (old : ℕ → ℕ) (x : Data 160)
    (hp : QueriedProduct.Parameters L m N qs.length x) (hb : Parameters L m t N qs.length x)
    (hi : x.regs QueriedProduct.Reg.index = 0)
    (hg : QueriedProduct.SavedGroups L m N qs.length old x.mem)
    (he : QueriedProduct.EncodedBands hm X Y x.mem) (hgeom : Geometry L m t N qs.length x.mem)
    (hvalues : ∀ i : Fin qs.length,
      old (Wanted.codeAddress L m N qs.length +
          CountingSort.position (Wanted.tileKey L m N ∘ Wanted.inputPairs qs) qs.length i) =
        (PrunedQuery.queryIndex
          (outStrOfPos (MaskTable.layout hm) (qs.get i).1 (qs.get i).2)).val)
    (hoffsets : ∀ s ≤ numBands L m N ^ 2,
      old (Wanted.offsetAddress L m N qs.length + s) =
        Nat.count (fun k => (Wanted.tileKey L m N ∘ Wanted.inputPairs qs) k < s) qs.length)
    (hX : ∀ i k, |X i k| ≤ (A : ℤ)) (hY : ∀ k i, |Y k i| ≤ (A : ℤ))
    (hmag : magnitudeBound L A < 2 ^ (w - 1))
    (hfit : Fits (w + 2) (wordBudget L m t N qs.length)) :
    ∃ y, ExecWithin (w + 2) evaluateTiles x y
        ((∑ j ∈ Finset.range (numBands L m N ^ 2), tileCharge L m t qs j) + 2) ∧
      QueriedProduct.Parameters L m N qs.length y ∧ Parameters L m t N qs.length y ∧
      QueriedProduct.SavedGroups L m N qs.length old y.mem ∧
      QueriedProduct.EncodedBands hm X Y y.mem ∧ Geometry L m t N qs.length y.mem ∧
      (∀ i : Fin qs.length,
        y.mem (QueriedProduct.groupedBase L m N qs.length +
          CountingSort.position (Wanted.tileKey L m N ∘ Wanted.inputPairs qs) qs.length i) =
            Signed.encode ((X * Y) (qs.get i).1 (qs.get i).2)) ∧
      (∀ p, ¬(QueriedProduct.groupedBase L m N qs.length ≤ p ∧
        p < QueriedProduct.outputBase L m N qs.length) →
        ¬(directoryBase L m N qs.length ≤ p ∧ p < memoryEnd L m t N qs.length) →
          y.mem p = x.mem p) := by
  let key := Wanted.tileKey L m N ∘ Wanted.inputPairs qs
  let T := numBands L m N ^ 2
  let I := Progress (t := t) hm X Y qs old x.mem
  let Φ (z : Data 160) :=
    ∑ j ∈ Finset.Ico (z.regs QueriedProduct.Reg.index) T, tileCharge L m t qs j
  have hout : QueriedProduct.groupedBase L m N qs.length + qs.length =
      QueriedProduct.outputBase L m N qs.length := rfl
  have hgroupBefore := (allocation_order L m t N qs.length).2.1
  have hstart : I x := ⟨hp, hb, by rw [hi]; omega, hg, he, hgeom,
    by intro i hk; rw [hi] at hk; omega, by intro p _ _; rfl⟩
  have hbody (z : Data 160) (hz : I z)
      (hc : (Cond.lt QueriedProduct.Reg.index QueriedProduct.Reg.tiles).Holds z) :
      ∃ y C, ExecWithin (w + 2) tileStep z y C ∧ I y ∧ C + 2 + Φ y ≤ Φ z := by
    have hj : z.regs QueriedProduct.Reg.index < T := by
      simpa only [Cond.holds_lt, hz.fixed.tiles, T] using hc
    obtain ⟨y, hr, yp, yb, yi, yg, ye, ygeom, yvalues, yf⟩ :=
      exec_tileStep hw hm ht X Y qs old z hz.fixed hz.boxes rfl hj
        hz.groups hz.catalogue hz.geometry hvalues hoffsets hX hY hmag hfit
    have ha := (hz.groups.offsets _ hj.le).trans (hoffsets _ hj.le)
    have hb := (hz.groups.offsets _ (Nat.succ_le_of_lt hj)).trans
      (hoffsets _ (Nat.succ_le_of_lt hj))
    have hdiff :
        z.mem (QueriedProduct.offsetBase L m N qs.length + z.regs QueriedProduct.Reg.index + 1) -
          z.mem (QueriedProduct.offsetBase L m N qs.length + z.regs QueriedProduct.Reg.index) =
        Nat.count (fun k => key k = z.regs QueriedProduct.Reg.index) qs.length := by
      rw [show QueriedProduct.offsetBase L m N qs.length + z.regs QueriedProduct.Reg.index + 1 =
          QueriedProduct.offsetBase L m N qs.length +
            (z.regs QueriedProduct.Reg.index + 1) by omega,
        hb, ha, CountingSort.count_lt_succ]
      dsimp only [key]
      omega
    rw [hdiff] at hr
    refine ⟨y, _, hr, ?_, ?_⟩
    · refine ⟨yp, yb, by rw [yi]; omega, yg, ye, ygeom, ?_, ?_⟩
      · intro i hik
        change key i.val < y.regs QueriedProduct.Reg.index at hik
        by_cases hki : key i.val = z.regs QueriedProduct.Reg.index
        · exact yvalues i hki
        · have hold : key i.val < z.regs QueriedProduct.Reg.index := by rw [yi] at hik; omega
          have hs := (CountingSort.position_mem key i.isLt).2
          have hmcount : Nat.count (fun k => key k < key i.val + 1) qs.length ≤
              Nat.count (fun k => key k < z.regs QueriedProduct.Reg.index) qs.length :=
            Nat.count_mono_left (fun k _ hk => by omega)
          have hpos := CountingSort.position_lt key i.isLt
          dsimp only [key] at hs hmcount hpos
          rw [yf _ (by omega) (by omega)]
          exact hz.answers i hold
      · intro p ho hf
        have hbQ := (hz.groups.span_bounds key hoffsets hj).2
        rw [yf p (by omega) hf]
        exact hz.frame p ho hf
    · have hsplit := Finset.sum_eq_sum_Ico_succ_bot hj (tileCharge L m t qs)
      dsimp only [Φ]
      rw [yi, hsplit]
      dsimp only [tileCharge, key]
      omega
  obtain ⟨y, hr, hy, hc⟩ := ExecWithin.loop_potential I Φ hbody hstart
  have hlast : y.regs QueriedProduct.Reg.index = T := by
    have h := hy.index_le
    simp only [Cond.holds_lt, hy.fixed.tiles] at hc
    dsimp only [T] at *
    omega
  refine ⟨y, ?_, hy.fixed, hy.boxes, hy.groups, hy.catalogue, hy.geometry, ?_, hy.frame⟩
  · simpa only [Φ, hi, Nat.Ico_zero_eq_range, T, evaluateTiles] using hr
  · intro i
    apply hy.answers i
    rw [hlast]
    exact Wanted.tileKey_lt hm (Wanted.inputPairs qs i.val)
      (Wanted.inputPairs_lt qs i i.isLt).1 (Wanted.inputPairs_lt qs i i.isLt).2

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct
