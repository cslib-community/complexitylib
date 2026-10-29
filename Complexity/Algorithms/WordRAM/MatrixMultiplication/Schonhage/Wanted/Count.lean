/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted.CountStep

/-!
# Complete native count pass for wanted positions

## Main results

* `Wanted.exec_clearCounts`: initialize exactly the actual tile-count cells.
* `Wanted.exec_countQueries`: all original occurrences, including repetitions, are counted
  by the actual coordinate-loading and tile-index code in linear charged time.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Actual dense initialization of tile counts. It touches no query or computed table. -/
theorem exec_clearCounts {w L m N Q : ℕ} (x : Data 96) (hx : Parameters L m N Q x)
    (hfit : Fits w (wordBudget L m N Q)) :
    ∃ y, ExecWithin w clearCounts x y (5 * numBands L m N ^ 2 + 3) ∧
      Parameters L m N Q y ∧
      (∀ t < numBands L m N ^ 2, y.mem (countAddress L Q + t) = 0) ∧
      (∀ a, a < countAddress L Q ∨ countAddress L Q + numBands L m N ^ 2 ≤ a →
        y.mem a = x.mem a) := by
  let T := numBands L m N ^ 2
  let body : Code .standard 96 := ram[
    pointer ← counts + index; *pointer ← BandPreparation.zero;
    index ← index + BandPreparation.one ]
  let I (z : Data 96) : Prop := Parameters L m N Q z ∧ z.regs index ≤ T ∧
    (∀ t < z.regs index, z.mem (countAddress L Q + t) = 0) ∧
    (∀ a, a < countAddress L Q ∨ countAddress L Q + T ≤ a → z.mem a = x.mem a)
  let start := x.set index 0
  have hs : ExecWithin w (ram[index ← #0] : Code .standard 96) x start 1 := by
    ram_eval [start]
  have hp : Parameters L m N Q start := hx.reframe (by
    intro i hi
    apply hs.regs_eq
    have h : ∀ i ∈ parameterRegisters, (ram[index ← #0] : Code .standard 96).Preserves i := by
      decide +kernel
    exact h i hi)
  have hstart : I start := ⟨hp, by simp [start], by simp [start], by simp [start]⟩
  have hb (z : Data 96) (hz : I z) (hc : (Cond.lt index tileCount).Holds z) :
      ∃ u, ExecWithin w body z u 3 ∧ I u ∧ T - u.regs index < T - z.regs index := by
    have hn : z.regs index < T := by
      simpa only [Cond.holds_lt, hz.1.tileCount] using hc
    have hl := local_fits hfit
    have hend := memoryLimit_eq L m N Q
    have h10 := Nat.zero_le (10 ^ L)
    have hfaddr : Fits w (countAddress L Q + z.regs index) := hl.of_le (by
      unfold countAddress tableAddress inputLimit
      dsimp [T] at hn
      omega)
    have hnext : Fits w (z.regs index + 1) := hl.of_le (by dsimp [T] at hn; omega)
    let u := ((z.set pointer (countAddress L Q + z.regs index)).write
      (countAddress L Q + z.regs index) 0).set index (z.regs index + 1)
    have he : ExecWithin w body z u 3 := by
      ram_eval [body, u, hz.1.counts, hz.1.tables.zero, hz.1.tables.one, hfaddr, hnext,
        pointer, counts, index, BandPreparation.zero, BandPreparation.one, Fin.mk.injEq]
    have hu : Parameters L m N Q u := hz.1.reframe (by
      intro i hi
      apply he.regs_eq
      have h : ∀ i ∈ parameterRegisters, body.Preserves i := by decide +kernel
      exact h i hi)
    have hi : u.regs index = z.regs index + 1 := by simp [u, index]
    refine ⟨u, he, ⟨hu, by rw [hi]; omega, ?_, ?_⟩, by rw [hi]; omega⟩
    · intro t ht
      rw [hi] at ht
      change Function.update z.mem (countAddress L Q + z.regs index) 0
        (countAddress L Q + t) = 0
      by_cases h : t = z.regs index
      · subst t
        exact Function.update_self _ _ _
      · rw [Function.update_of_ne (by omega)]
        exact hz.2.2.1 t (by omega)
    · intro a ha
      change Function.update z.mem (countAddress L Q + z.regs index) 0 a = x.mem a
      rw [Function.update_of_ne (by rcases ha with ha | ha <;> omega)]
      exact hz.2.2.2 a ha
  obtain ⟨y, he, hy, hc⟩ := ExecWithin.loop_invariant I (fun z => T - z.regs index) hb hstart
  have hn : y.regs index = T := by
    have hu := hy.2.1
    simp only [Cond.holds_lt, hy.1.tileCount] at hc
    dsimp [T] at hu ⊢
    omega
  refine ⟨y, ?_, hy.1, ?_, hy.2.2.2⟩
  · apply (hs.seq he).mono
    have hzero : start.regs index = 0 := by simp [start]
    rw [hzero, Nat.sub_zero]
    dsimp [T]
    omega
  · intro t ht
    exact hy.2.2.1 t (hn ▸ ht)

/-- Every original query is loaded and its actual tile computed. Duplicate input pairs
increase counts independently; the readonly input and both computed tables are preserved. -/
theorem exec_countQueries {w L m N Q : ℕ} (hm : m ≤ L) (pairs : ℕ → ℕ × ℕ)
    (hpairs : ∀ i < Q, (pairs i).1 < N ∧ (pairs i).2 < N) (x : Data 96)
    (hx : Parameters L m N Q x)
    (hinput : ∀ i < Q, x.mem (5 + 2 * i) = (pairs i).1 ∧
      x.mem (5 + 2 * i + 1) = (pairs i).2)
    (hzero : ∀ t < numBands L m N ^ 2, x.mem (countAddress L Q + t) = 0)
    (hfit : Fits w (wordBudget L m N Q)) :
    ∃ y, ExecWithin w countQueries x y (16 * Q + 3) ∧ Parameters L m N Q y ∧
      (∀ t < numBands L m N ^ 2,
        y.mem (countAddress L Q + t) = Nat.count (fun k => (tileKey L m N ∘ pairs) k = t) Q) ∧
      (∀ a, a < countAddress L Q ∨ countAddress L Q + numBands L m N ^ 2 ≤ a →
        y.mem a = x.mem a) := by
  let key := tileKey L m N ∘ pairs
  let T := numBands L m N ^ 2
  let I (z : Data 96) : Prop := Parameters L m N Q z ∧ z.regs index ≤ Q ∧
    (∀ i < Q, z.mem (5 + 2 * i) = (pairs i).1 ∧
      z.mem (5 + 2 * i + 1) = (pairs i).2) ∧
    (∀ t < T, z.mem (countAddress L Q + t) = Nat.count (fun k => key k = t) (z.regs index)) ∧
    (∀ a, a < countAddress L Q ∨ countAddress L Q + T ≤ a → z.mem a = x.mem a)
  let start := x.set index 0
  have hs : ExecWithin w (ram[index ← #0] : Code .standard 96) x start 1 := by
    ram_eval [start]
  have hsp : Parameters L m N Q start := hx.reframe (by
    intro i hi
    apply hs.regs_eq
    have h : ∀ i ∈ parameterRegisters, (ram[index ← #0] : Code .standard 96).Preserves i := by
      decide +kernel
    exact h i hi)
  have hi : I start := by
    refine ⟨hsp, by simp [start], hinput, ?_, by simp [start]⟩
    intro t ht
    simpa only [start, Data.set_regs, Function.update_self, Data.set_mem,
      Nat.count_zero] using hzero t ht
  have hb (z : Data 96) (hz : I z) (hc : (Cond.lt index queryCount).Holds z) :
      ∃ u, ExecWithin w countStep z u 14 ∧ I u ∧
        Q - u.regs index < Q - z.regs index := by
    have hn : z.regs index < Q := by
      simpa only [Cond.holds_lt, hz.1.queryCount] using hc
    obtain ⟨u, he, hu, hidx, hcounts, hf⟩ := exec_countStep hm pairs hn (hpairs _ hn)
      z hz.1 rfl (hz.2.2.1 _ hn) hz.2.2.2.1 hfit
    refine ⟨u, he, ⟨hu, by rw [hidx]; omega, ?_, ?_, ?_⟩, by rw [hidx]; omega⟩
    · intro i hi
      have ha : 5 + 2 * i + 1 < countAddress L Q := by
        have h2 := Nat.zero_le (2 ^ L)
        unfold countAddress tableAddress inputLimit
        omega
      rw [hf _ (Or.inl (by omega)), hf _ (Or.inl ha)]
      exact hz.2.2.1 i hi
    · intro t ht
      rw [hidx]
      exact hcounts t ht
    · intro a ha
      exact (hf a ha).trans (hz.2.2.2.2 a ha)
  obtain ⟨y, he, hy, hc⟩ := ExecWithin.loop_invariant I (fun z => Q - z.regs index) hb hi
  have hn : y.regs index = Q := by
    have hu := hy.2.1
    simp only [Cond.holds_lt, hy.1.queryCount] at hc
    omega
  refine ⟨y, ?_, hy.1, ?_, hy.2.2.2.2⟩
  · apply (hs.seq he).mono
    have hz : start.regs index = 0 := by simp [start]
    rw [hz, Nat.sub_zero]
    omega
  · intro t ht
    simpa only [hn] using hy.2.2.2.1 t ht

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted
