/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted.ScatterStep

/-!
# Complete native wanted-query scatter

## Main results

* `Wanted.exec_scatter`: compute every original position's output code and stable destination,
  retaining repetitions and writing the original-position permutation with a charged bound.

This internal implementation API composes the actual router and stores. The finite scatter
permutation is proved from occurrence counts; it is neither supplied nor checked by an oracle.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- The actual original-order scan fills all grouped codes and the original-position
permutation. Its only writes are scatter cursors and the two grouped output arrays. -/
theorem exec_scatter {w L m N Q : ℕ} (hm : m ≤ L) (pairs : ℕ → ℕ × ℕ)
    (hpairs : ∀ i < Q, (pairs i).1 < N ∧ (pairs i).2 < N) (x : Data 96)
    (hx : Parameters L m N Q x)
    (hinput : ∀ i < Q, x.mem (5 + 2 * i) = (pairs i).1 ∧
      x.mem (5 + 2 * i + 1) = (pairs i).2)
    (htable : ∀ gh : Fin (K0 L m) × Fin (K0 L m),
      x.mem (tableAddress L Q + (MaskTable.pairRank gh).val) = (MaskTable.selectedMask gh).val)
    (hcursors : ∀ t < numBands L m N ^ 2,
      x.mem (cursorAddressBase L m N Q + t) = Nat.count (fun k => (tileKey L m N ∘ pairs) k < t) Q)
    (hfit : Fits w (wordBudget L m N Q)) :
    ∃ y, ExecWithin w scatter x y ((15 * L + 41) * Q + 3) ∧ Parameters L m N Q y ∧
      (∀ i < Q,
        y.mem (codeAddress L m N Q + CountingSort.position (tileKey L m N ∘ pairs) Q i) =
            (PrunedQuery.queryIndex
              (outStrOfPos (MaskTable.layout hm) (pairs i).1 (pairs i).2)).val ∧
          y.mem (originalAddress L m N Q + CountingSort.position (tileKey L m N ∘ pairs) Q i) = i) ∧
      (∀ t < numBands L m N ^ 2, y.mem (cursorAddressBase L m N Q + t) =
        Nat.count (fun k => (tileKey L m N ∘ pairs) k < (t + 1)) Q) ∧
      (∀ a, a < cursorAddressBase L m N Q ∨ memoryLimit L m N Q ≤ a →
        y.mem a = x.mem a) := by
  let key := tileKey L m N ∘ pairs
  let I (z : Data 96) : Prop := Parameters L m N Q z ∧ z.regs index ≤ Q ∧
    (∀ i < Q, z.mem (5 + 2 * i) = (pairs i).1 ∧
      z.mem (5 + 2 * i + 1) = (pairs i).2) ∧
    (∀ gh : Fin (K0 L m) × Fin (K0 L m),
      z.mem (tableAddress L Q + (MaskTable.pairRank gh).val) = (MaskTable.selectedMask gh).val) ∧
    (∀ t < numBands L m N ^ 2, z.mem (cursorAddressBase L m N Q + t) =
      Nat.count (fun k => key k < t) Q + Nat.count (fun k => key k = t) (z.regs index)) ∧
    (∀ i < z.regs index,
      z.mem (codeAddress L m N Q + CountingSort.position key Q i) =
          (PrunedQuery.queryIndex
            (outStrOfPos (MaskTable.layout hm) (pairs i).1 (pairs i).2)).val ∧
        z.mem (originalAddress L m N Q + CountingSort.position key Q i) = i) ∧
    (∀ a, a < cursorAddressBase L m N Q ∨ memoryLimit L m N Q ≤ a → z.mem a = x.mem a)
  let start := x.set index 0
  have hs : ExecWithin w (ram[index ← #0] : Code .standard 96) x start 1 := by
    ram_eval [start]
  have hp : Parameters L m N Q start := hx.reframe (by
    intro i hi
    apply hs.regs_eq
    have h : ∀ i ∈ parameterRegisters, (ram[index ← #0] : Code .standard 96).Preserves i := by
      decide +kernel
    exact h i hi)
  have hi : I start := by
    refine ⟨hp, by simp [start], hinput, htable, ?_, by simp [start], by simp [start]⟩
    intro t ht
    simpa only [start, Data.set_regs, Function.update_self, Data.set_mem,
      Nat.count_zero, Nat.add_zero] using hcursors t ht
  have hb (z : Data 96) (hz : I z) (hc : (Cond.lt index queryCount).Holds z) :
      ∃ u, ExecWithin w scatterStep z u (15 * L + 39) ∧ I u ∧
        Q - u.regs index < Q - z.regs index := by
    have hn : z.regs index < Q := by
      simpa only [Cond.holds_lt, hz.1.queryCount] using hc
    obtain ⟨u, he, hu, hidx, hcur, hcode, horig, hf⟩ := exec_scatterStep hm pairs hn
      (hpairs _ hn) z hz.1 rfl (hz.2.2.1 _ hn) hz.2.2.2.1 hz.2.2.2.2.1 hfit
    change ∀ a, a ≠ cursorAddressBase L m N Q + key (z.regs index) →
      a ≠ codeAddress L m N Q + CountingSort.position key Q (z.regs index) →
      a ≠ originalAddress L m N Q + CountingSort.position key Q (z.regs index) →
        u.mem a = z.mem a at hf
    have hk : key (z.regs index) < numBands L m N ^ 2 := tileKey_lt hm _ (hpairs _ hn).1
      (hpairs _ hn).2
    have hpos : CountingSort.position key Q (z.regs index) < Q :=
      CountingSort.position_lt key hn
    have hcursor : cursorAddressBase L m N Q + key (z.regs index) < codeAddress L m N Q := by
      unfold codeAddress
      omega
    have hcodes : codeAddress L m N Q + CountingSort.position key Q (z.regs index) <
        originalAddress L m N Q := by
      unfold originalAddress
      omega
    have horiginals : originalAddress L m N Q + CountingSort.position key Q (z.regs index) <
        memoryLimit L m N Q := by
      unfold memoryLimit
      omega
    have horder : cursorAddressBase L m N Q ≤ codeAddress L m N Q ∧
        codeAddress L m N Q ≤ originalAddress L m N Q ∧
        originalAddress L m N Q ≤ memoryLimit L m N Q := by
      simp only [codeAddress, originalAddress, memoryLimit]
      omega
    have hlow (a : ℕ) (ha : a < cursorAddressBase L m N Q) : u.mem a = z.mem a :=
      hf a (by omega) (by omega) (by omega)
    refine ⟨u, he, ⟨hu, by rw [hidx]; omega, ?_, ?_, ?_, ?_, ?_⟩, by rw [hidx]; omega⟩
    · intro i hi
      have h2 := Nat.zero_le (2 ^ L)
      have ha : 5 + 2 * i + 1 < cursorAddressBase L m N Q := by
        unfold cursorAddressBase offsetAddress countAddress tableAddress inputLimit
        omega
      rw [hlow _ (by omega), hlow _ ha]
      exact hz.2.2.1 i hi
    · intro gh
      have hr : (MaskTable.pairRank gh).val < 2 ^ L :=
        (MaskTable.pairRank gh).isLt.trans_le (Nat.choose_le_two_pow L m)
      have ha : tableAddress L Q + (MaskTable.pairRank gh).val <
          cursorAddressBase L m N Q := by
        unfold cursorAddressBase offsetAddress countAddress
        omega
      rw [hlow _ ha]
      exact hz.2.2.2.1 gh
    · intro t ht
      rw [hidx]
      exact hcur t ht
    · intro i hi
      rw [hidx] at hi
      by_cases h : i = z.regs index
      · subst i
        exact ⟨hcode, horig⟩
      · have hip : i < z.regs index := by omega
        have hiQ : i < Q := hip.trans hn
        have hp : CountingSort.position key Q i < Q := CountingSort.position_lt key hiQ
        have hne : CountingSort.position key Q i ≠ CountingSort.position key Q (z.regs index) := by
          intro heq
          have hfin : (⟨i, hiQ⟩ : Fin Q) = ⟨z.regs index, hn⟩ :=
            CountingSort.position_injective key Q heq
          exact h (congrArg (fun j : Fin Q => j.val) hfin)
        have hop : originalAddress L m N Q = codeAddress L m N Q + Q := rfl
        rw [hf _ (by omega) (by omega) (by omega), hf _ (by omega) (by omega) (by omega)]
        exact hz.2.2.2.2.2.1 i hip
    · intro a ha
      rw [hf _ (by rcases ha with ha | ha <;> omega)
        (by rcases ha with ha | ha <;> omega) (by rcases ha with ha | ha <;> omega)]
      exact hz.2.2.2.2.2.2 a ha
  obtain ⟨y, he, hy, hc⟩ := ExecWithin.loop_invariant I (fun z => Q - z.regs index) hb hi
  have hn : y.regs index = Q := by
    have hle := hy.2.1
    simp only [Cond.holds_lt, hy.1.queryCount] at hc
    omega
  refine ⟨y, ?_, hy.1, ?_, ?_, hy.2.2.2.2.2.2⟩
  · apply (hs.seq he).mono
    have h0 : start.regs index = 0 := by simp [start]
    rw [h0, Nat.sub_zero]
    nlinarith
  · intro i hi
    exact hy.2.2.2.2.2.1 i (hn ▸ hi)
  · intro t ht
    have hv := hy.2.2.2.2.1 t ht
    rw [hn] at hv
    exact hv.trans (CountingSort.count_lt_succ key Q t).symm

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted
