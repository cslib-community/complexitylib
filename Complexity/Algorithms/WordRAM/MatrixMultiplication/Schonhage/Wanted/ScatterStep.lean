/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted.ScatterWrite
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted.CountStep

/-!
# One computed wanted-query scatter

## Main results

* `Wanted.exec_scatterStep`: the actual coordinate loads, table lookup, output-digit loop
  and three scatter stores preserve the exact stable-counting cursor invariant.

This stage contract is an internal implementation API; the query code is calculated from the
original pair, rather than supplied as a source memory word or an output certificate.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Load, compute and scatter one original query, preserving the original input and exact
per-tile cursors. Every loop in the digit computation and every address instruction is charged. -/
theorem exec_scatterStep {w L m N Q n : ℕ} (hm : m ≤ L) (pairs : ℕ → ℕ × ℕ)
    (hn : n < Q) (hpair : (pairs n).1 < N ∧ (pairs n).2 < N) (x : Data 96)
    (hx : Parameters L m N Q x) (hi : x.regs index = n)
    (hinput : x.mem (5 + 2 * n) = (pairs n).1 ∧
      x.mem (5 + 2 * n + 1) = (pairs n).2)
    (htable : ∀ gh : Fin (K0 L m) × Fin (K0 L m),
      x.mem (tableAddress L Q + (MaskTable.pairRank gh).val) = (MaskTable.selectedMask gh).val)
    (hcursors : ∀ t < numBands L m N ^ 2,
      x.mem (cursorAddressBase L m N Q + t) = Nat.count (fun k => (tileKey L m N ∘ pairs) k < t) Q +
        Nat.count (fun k => (tileKey L m N ∘ pairs) k = t) n)
    (hfit : Fits w (wordBudget L m N Q)) :
    ∃ y, ExecWithin w scatterStep x y (15 * L + 39) ∧ Parameters L m N Q y ∧
      y.regs index = n + 1 ∧
      (∀ t < numBands L m N ^ 2,
        y.mem (cursorAddressBase L m N Q + t) =
          Nat.count (fun k => (tileKey L m N ∘ pairs) k < t) Q +
            Nat.count (fun k => (tileKey L m N ∘ pairs) k = t) (n + 1)) ∧
      y.mem (codeAddress L m N Q + CountingSort.position (tileKey L m N ∘ pairs) Q n) =
        (PrunedQuery.queryIndex (outStrOfPos (MaskTable.layout hm) (pairs n).1 (pairs n).2)).val ∧
      y.mem (originalAddress L m N Q + CountingSort.position (tileKey L m N ∘ pairs) Q n) = n ∧
      (∀ a, a ≠ cursorAddressBase L m N Q + (tileKey L m N ∘ pairs) n →
        a ≠ codeAddress L m N Q + CountingSort.position (tileKey L m N ∘ pairs) Q n →
        a ≠ originalAddress L m N Q + CountingSort.position (tileKey L m N ∘ pairs) Q n →
          y.mem a = x.mem a) := by
  let key := tileKey L m N ∘ pairs
  let p := CountingSort.position key Q n
  let I : Fin N := ⟨(pairs n).1, hpair.1⟩
  let J : Fin N := ⟨(pairs n).2, hpair.2⟩
  have hk : key n < numBands L m N ^ 2 := tileKey_lt hm _ hpair.1 hpair.2
  have hl := local_fits hfit
  have hend := memoryLimit_eq L m N Q
  have h10 := Nat.zero_le (10 ^ L)
  have h2 := Nat.zero_le (2 ^ L)
  have hn2 : Fits w (n * 2) := hl.of_le (by omega)
  have ha : Fits w (n * 2 + 5) := hl.of_le (by omega)
  have ha1 : Fits w (n * 2 + 5 + 1) := hl.of_le (by omega)
  have hI : x.mem (n * 2 + 5) = I.val :=
    (congrArg x.mem (by omega : n * 2 + 5 = 5 + 2 * n)).trans hinput.1
  have hJ : x.mem (n * 2 + 5 + 1) = J.val :=
    (congrArg x.mem (by omega : n * 2 + 5 + 1 = 5 + 2 * n + 1)).trans hinput.2
  let loaded := ((((x.set pointer (n * 2)).set pointer (n * 2 + 5)).set queryRow I.val).set
    pointer (n * 2 + 5 + 1)).set queryCol J.val
  have hload : ExecWithin w loadQuery x loaded 5 := by
    ram_eval [loadQuery, loaded, hx.queries, hx.tables.two, hx.tables.one, hi, hI, hJ,
      hn2, ha, ha1, pointer, index, queries, queryRow, queryCol,
      BandPreparation.one, BandPreparation.two, Fin.mk.injEq]
  have lp : Parameters L m N Q loaded := hx.reframe (by
    intro i hi
    apply hload.regs_eq
    have hp : ∀ i ∈ parameterRegisters, loadQuery.Preserves i := by decide +kernel
    exact hp i hi)
  have hrfit : Fits w (routeBudget L m N (tableAddress L Q)) := hfit.of_le (by
    unfold wordBudget
    omega)
  obtain ⟨routed, hr, _, _, htile, hvalue, hrmem, hrregs⟩ := exec_route hm I J loaded lp.route
    (by simp [loaded, queryRow, queryCol, pointer]) (by simp [loaded]) htable hrfit
  change routed.mem = x.mem at hrmem
  have rp : Parameters L m N Q routed := lp.reframe (by
    intro i hi
    have hf : ∀ i ∈ parameterRegisters, ¬RouteLocal i := by decide +kernel
    exact hrregs i (hf i hi))
  have hidx : routed.regs index = n :=
    (hrregs index (by decide)).trans (by simp [loaded, index, pointer, queryRow, queryCol, hi])
  have hcursor : routed.mem (cursorAddressBase L m N Q + key n) = p := by
    rw [hrmem]
    exact hcursors _ hk
  obtain ⟨y, hy, yp, hiy, hcode, horig, hcur, hf⟩ := exec_scatterWrite key hn hk routed rp hidx
    htile hvalue hcursor hfit
  refine ⟨y, ?_, yp, hiy, ?_, hcode, horig, ?_⟩
  · exact (hload.seq (hr.seq hy)).mono (by omega)
  · intro t ht
    change y.mem (cursorAddressBase L m N Q + t) =
      Nat.count (fun k => key k < t) Q + Nat.count (fun k => key k = t) (n + 1)
    rw [Nat.count_succ]
    by_cases h : key n = t
    · subst t
      rw [hcur]
      simp only [↓reduceIte]
      rfl
    · have hlow : cursorAddressBase L m N Q + t < codeAddress L m N Q := by
        unfold codeAddress
        omega
      have horiglow : codeAddress L m N Q ≤ originalAddress L m N Q := by
        unfold originalAddress
        omega
      rw [hf _ (by omega) (by omega) (by omega), hrmem, hcursors t ht, ite_eq_right h]
      rfl
  · intro a hc hv ho
    exact (hf a hc hv ho).trans (congrFun hrmem a)

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted
