/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PointerInput.Program
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Product.Routing

/-!
# Routing from an executed snapshot gather

The snapshot and ordinary header readback are explicit premises at this internal continuation
boundary. The public pointer caller establishes them by charged physical loads and stores.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PointerInput

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open QueriedProduct

/-- Continue actual routing from computed parameters and actual original snapshot words. -/
theorem exec_routing {w L m N : ℕ} (hm : m ≤ L) (qs : List (Fin N × Fin N))
    (x : Data 160) (xp : Parameters L m N qs.length x)
    (original : ℕ → ℕ)
    (hsnapshot : ∀ j < inputEnd m N qs.length,
      x.mem (snapshotBase L m N qs.length + j) = original j)
    (hL : x.mem 1 = L) (hmemory : x.mem 2 = m) (hN : x.mem 3 = N)
    (hQ : x.mem 4 = qs.length)
    (hqueries : ∀ i < qs.length,
      original (queryInputBase m N + 2 * i) = (Wanted.inputPairs qs i).1 ∧
        original (queryInputBase m N + 2 * i + 1) = (Wanted.inputPairs qs i).2)
    (hfit : Fits w (wordBudget L m N qs.length)) :
    ∃ (y : Data 160) (old : ℕ → ℕ),
      ExecWithin w routing x y (routingTime L m N qs.length) ∧
      Parameters L m N qs.length y ∧ SavedGroups L m N qs.length old y.mem ∧
      (∀ i : Fin qs.length,
        old (Wanted.codeAddress L m N qs.length +
            CountingSort.position (Wanted.tileKey L m N ∘ Wanted.inputPairs qs) qs.length i) =
            (PrunedQuery.queryIndex
              (outStrOfPos (MaskTable.layout hm) (qs.get i).1 (qs.get i).2)).val ∧
          old (Wanted.originalAddress L m N qs.length +
            CountingSort.position (Wanted.tileKey L m N ∘ Wanted.inputPairs qs) qs.length i) =
              i.val) ∧
      (∀ t ≤ numBands L m N ^ 2,
        old (Wanted.offsetAddress L m N qs.length + t) =
          Nat.count (fun k => (Wanted.tileKey L m N ∘ Wanted.inputPairs qs) k < t) qs.length) ∧
      (∀ j < inputEnd m N qs.length,
        y.mem (snapshotBase L m N qs.length + j) = original j) ∧
      (∀ a, a < 5 ∨ groupedBase L m N qs.length ≤ a → y.mem a = x.mem a) := by
  have hgeom : 5 ≤ inputEnd m N qs.length ∧
      5 + 2 * qs.length ≤ inputEnd m N qs.length ∧
      inputEnd m N qs.length ≤ snapshotBase L m N qs.length ∧
      snapshotBase L m N qs.length + inputEnd m N qs.length ≤ groupedBase L m N qs.length := by
    simp only [inputEnd, snapshotBase, groupedBase, originalBase, codeBase, offsetBase]
    omega
  obtain ⟨q, hq, qp, qm⟩ := exec_prepareQueries x xp hfit
  have qsnapshot (j : ℕ) (hj : j < inputEnd m N qs.length) :
      q.mem (snapshotBase L m N qs.length + j) = original j := by
    rw [qm, ArrayCopy.copyPrefix_outside (by omega)]
    exact hsnapshot j hj
  have qframe (a : ℕ) (ha : a < 5 ∨ groupedBase L m N qs.length ≤ a) : q.mem a = x.mem a := by
    rw [qm, ArrayCopy.copyPrefix_outside (by rcases ha with ha | ha <;> omega)]
  have qinput (i : ℕ) (hi : i < qs.length) :
      q.mem (5 + 2 * i) = (Wanted.inputPairs qs i).1 ∧
        q.mem (5 + 2 * i + 1) = (Wanted.inputPairs qs i).2 := by
    have hr := ArrayCopy.copyPrefix_read (mem := x.mem)
      (src := snapshotBase L m N qs.length + queryInputBase m N) (dst := 5)
      (k := 2 * qs.length) (j := 2 * i) (by omega)
    have hc := ArrayCopy.copyPrefix_read (mem := x.mem)
      (src := snapshotBase L m N qs.length + queryInputBase m N) (dst := 5)
      (k := 2 * qs.length) (j := 2 * i + 1) (by omega)
    have hrow := hsnapshot (queryInputBase m N + 2 * i) (query_address_lt hi (by decide : 0 < 2))
    have hcol := hsnapshot (queryInputBase m N + 2 * i + 1)
      (query_address_lt hi (by decide : 1 < 2))
    constructor
    · rw [qm, hr]
      simpa only [Nat.add_assoc] using hrow.trans (hqueries i hi).1
    · rw [qm, show 5 + 2 * i + 1 = 5 + (2 * i + 1) by omega, hc]
      simpa only [Nat.add_assoc] using hcol.trans (hqueries i hi).2
  obtain ⟨w, hw, wp, wparams, wv, wo, _, wf⟩ := exec_wanted hm qs q qp
    ((qframe 1 (Or.inl (by decide))).trans hL)
    ((qframe 2 (Or.inl (by decide))).trans hmemory)
    ((qframe 3 (Or.inl (by decide))).trans hN)
    ((qframe 4 (Or.inl (by decide))).trans hQ) qinput hfit
  obtain ⟨y, hy, yp, yo, yc, yi, yf⟩ := exec_saveGroups w wp wparams hfit
  have hlow : Wanted.memoryLimit L m N qs.length ≤ snapshotBase L m N qs.length :=
    (producers_le_snapshot L m N qs.length).2.1
  have hoff : snapshotBase L m N qs.length + inputEnd m N qs.length =
      offsetBase L m N qs.length := rfl
  have hg : originalBase L m N qs.length + qs.length = groupedBase L m N qs.length := rfl
  refine ⟨y, w.mem, ?_, yp, ⟨yo, yc, yi⟩, wv, wo, ?_, ?_⟩
  · apply (hq.seq (hw.seq hy)).mono
    unfold routingTime
    omega
  · intro j hj
    rw [yf _ (Or.inl (by omega)), wf _ (Or.inr (by omega))]
    exact qsnapshot j hj
  · intro a ha
    rw [yf _ (by rcases ha with ha | ha <;> omega), wf _ (by
      rcases ha with ha | ha
      · exact Or.inl (by unfold Wanted.inputLimit; omega)
      · exact Or.inr (by omega))]
    exact qframe a ha


end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PointerInput
