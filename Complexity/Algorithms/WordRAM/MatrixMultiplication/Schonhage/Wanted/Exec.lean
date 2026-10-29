/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted.Count
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted.Prefix
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted.Scatter
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted.Cost

/-!
# Complete native routing from original scalar and coordinate inputs

## Main results

* `Wanted.exec_program`: compute tables, counts, prefix offsets, query codes and stable
  scatter positions in the fixed native program, retaining the original input and outside frame.

All table and cursor premises of the internal stages are established by actual preceding code.
The caller supplies only the original scalar headers and the ordinary coordinate list.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- The complete native program, with no table, query-code, prefix or permutation oracle.
Every original query occurrence has one computed stable destination and retains its index. -/
theorem exec_program {w L m N Q : ℕ} (hm : m ≤ L) (pairs : ℕ → ℕ × ℕ)
    (hpairs : ∀ i < Q, (pairs i).1 < N ∧ (pairs i).2 < N) (x : Data 96)
    (hL : x.mem 1 = L) (hmemory : x.mem 2 = m) (hN : x.mem 3 = N) (hQ : x.mem 4 = Q)
    (hinput : ∀ i < Q, x.mem (5 + 2 * i) = (pairs i).1 ∧
      x.mem (5 + 2 * i + 1) = (pairs i).2)
    (hfit : Fits w (wordBudget L m N Q)) :
    ∃ y, ExecWithin w program x y (timeBound L m N Q) ∧ Parameters L m N Q y ∧
      (∀ i < Q,
        y.mem (codeAddress L m N Q + CountingSort.position (tileKey L m N ∘ pairs) Q i) =
            (PrunedQuery.queryIndex
              (outStrOfPos (MaskTable.layout hm) (pairs i).1 (pairs i).2)).val ∧
          y.mem (originalAddress L m N Q + CountingSort.position (tileKey L m N ∘ pairs) Q i) = i) ∧
      (∀ t ≤ numBands L m N ^ 2,
        y.mem (offsetAddress L m N Q + t) = Nat.count (fun k => (tileKey L m N ∘ pairs) k < t) Q) ∧
      y.mem (offsetAddress L m N Q + numBands L m N ^ 2) = Q ∧
      (∀ a, a < inputLimit Q ∨ memoryLimit L m N Q ≤ a → y.mem a = x.mem a) := by
  let key := tileKey L m N ∘ pairs
  have h2 := Nat.zero_le (2 ^ L)
  have hT := Nat.zero_le (numBands L m N ^ 2)
  have horder : inputLimit Q ≤ countAddress L Q ∧
      countAddress L Q + numBands L m N ^ 2 = offsetAddress L m N Q ∧
      offsetAddress L m N Q ≤ cursorAddressBase L m N Q ∧
      cursorAddressBase L m N Q ≤ codeAddress L m N Q ∧
      codeAddress L m N Q ≤ memoryLimit L m N Q := by
    simp only [countAddress, tableAddress, offsetAddress, cursorAddressBase,
      codeAddress, memoryLimit, originalAddress]
    exact ⟨by omega, trivial, by omega, by omega, by omega⟩
  obtain ⟨a, ha, ap, atable, af⟩ := exec_tables hm x hL hmemory hN hQ hfit
  obtain ⟨b, hb, bp, bz, bf⟩ := exec_clearCounts a ap hfit
  have bin (i : ℕ) (hi : i < Q) : b.mem (5 + 2 * i) = (pairs i).1 ∧
      b.mem (5 + 2 * i + 1) = (pairs i).2 := by
    have hbound : 5 + 2 * i + 1 < inputLimit Q := by unfold inputLimit; omega
    rw [bf _ (Or.inl (by omega)), af _ (Or.inl (by omega)),
      bf _ (Or.inl (by omega)), af _ (Or.inl hbound)]
    exact hinput i hi
  obtain ⟨c, hc, cp, ccounts, cf⟩ := exec_countQueries hm pairs hpairs b bp bin bz hfit
  have hkeys : ∀ i < Q, key i < numBands L m N ^ 2 := by
    intro i hi
    exact tileKey_lt hm _ (hpairs i hi).1 (hpairs i hi).2
  obtain ⟨p, hp, pp, poff, pcur, plast, pf⟩ := exec_prefix key hkeys c cp ccounts hfit
  have pinput (addr : ℕ) (hi : addr < inputLimit Q) : p.mem addr = x.mem addr := by
    rw [pf _ (Or.inl (by omega)), cf _ (Or.inl (by omega)),
      bf _ (Or.inl (by omega)), af _ (Or.inl hi)]
  have pin (i : ℕ) (hi : i < Q) : p.mem (5 + 2 * i) = (pairs i).1 ∧
      p.mem (5 + 2 * i + 1) = (pairs i).2 := by
    have hbound : 5 + 2 * i + 1 < inputLimit Q := by unfold inputLimit; omega
    rw [pinput _ (by omega), pinput _ hbound]
    exact hinput i hi
  have ptable (gh : Fin (K0 L m) × Fin (K0 L m)) :
      p.mem (tableAddress L Q + (MaskTable.pairRank gh).val) = (MaskTable.selectedMask gh).val := by
    have hr : (MaskTable.pairRank gh).val < 2 ^ L :=
      (MaskTable.pairRank gh).isLt.trans_le (Nat.choose_le_two_pow L m)
    have htable : tableAddress L Q + (MaskTable.pairRank gh).val < countAddress L Q := by
      unfold countAddress
      omega
    rw [pf _ (Or.inl (by omega)), cf _ (Or.inl htable), bf _ (Or.inl htable)]
    exact atable gh
  obtain ⟨y, hy, yp, yout, _, yf⟩ := exec_scatter hm pairs hpairs p pp pin ptable pcur hfit
  refine ⟨y, ?_, yp, yout, ?_, ?_, ?_⟩
  · have hrest := hb.seq (hc.seq (hp.seq hy))
    have hfull := ha.seq hrest
    apply hfull.mono
    unfold timeBound
    nlinarith
  · intro t ht
    have hlow : offsetAddress L m N Q + t < cursorAddressBase L m N Q := by
      unfold cursorAddressBase
      omega
    rw [yf _ (Or.inl hlow)]
    exact poff t ht
  · rw [yf _ (Or.inl (by unfold cursorAddressBase; omega))]
    exact plast
  · intro addr hi
    rw [yf _ (by rcases hi with hi | hi <;> omega),
      pf _ (by rcases hi with hi | hi <;> omega),
      cf _ (by rcases hi with hi | hi <;> omega),
      bf _ (by rcases hi with hi | hi <;> omega)]
    apply af addr
    rcases hi with hi | hi
    · exact Or.inl hi
    · exact Or.inr (by unfold countAddress at horder; omega)

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted
