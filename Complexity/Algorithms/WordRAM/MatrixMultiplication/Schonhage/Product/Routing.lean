/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Product.Header
import Complexity.Computability.WordRAM.Sequence
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Product.Route
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Product.SavedGroups

/-!
# Native routing preparation from original coordinates

## Main results

* `QueriedProduct.exec_prepareSnapshot`: execute parameters, layout and the original snapshot.
* `QueriedProduct.exec_routingFromSnapshot`: share actual routing after an executed snapshot copy
  or physical gather, with explicit original readback and ordinary scalar headers.
* `QueriedProduct.exec_prepareRouting`: establish that boundary from contiguous original words.

The earlier router memory in the conclusion is an existential witness produced by its
actual execution. It is not a catalogue, layout or run certificate supplied by the caller.
-/

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Compute parameters and layout, then preserve the complete original input. -/
@[expose] public def prepareSnapshot : Code .standard 160 :=
  .seq parameters (.seq layout saveInput)

/-- Actual coordinate adaptation, routing and protected group copies after a snapshot. -/
@[expose] public def routingFromSnapshot : Code .standard 160 :=
  .seq prepareQueries (.seq (Wanted.program.rename bank) saveGroups)

/-- The sum of the actual preparation phases, before matrix adaptation and encoding. -/
@[expose] public def routingTimeBound (L m N Q : ℕ) : ℕ :=
  ((16 * L + 49) + ((6 * L + 16) * 2 ^ L + 16)) + 50 +
    (7 * inputEnd m N Q + 10) + (14 * Q + 10) + Wanted.timeBound L m N Q +
      (7 * numBands L m N ^ 2 + 14 * Q + 37)

/-- Charge parameter/layout calculation and the complete original snapshot copy. -/
@[expose] public def snapshotTime (L m N Q : ℕ) : ℕ :=
  ((16 * L + 49) + ((6 * L + 16) * 2 ^ L + 16)) + 50 + (7 * inputEnd m N Q + 10)

/-- Charge only coordinate adaptation, routing and protected group copies. -/
@[expose] public def routingFromSnapshotTime (L m N Q : ℕ) : ℕ :=
  (14 * Q + 10) + Wanted.timeBound L m N Q + (7 * numBands L m N ^ 2 + 14 * Q + 37)

/-- Execute the ordinary contiguous-input prefix; the snapshot may initially be dirty. -/
public theorem exec_prepareSnapshot {w L m N Q : ℕ} (hm : m ≤ L) (x : Data 160)
    (hL : x.mem 1 = L) (hmemory : x.mem 2 = m) (hN : x.mem 3 = N) (hQ : x.mem 4 = Q)
    (hfit : Fits w (wordBudget L m N Q)) :
    ∃ y, ExecWithin w prepareSnapshot x y (snapshotTime L m N Q) ∧ Parameters L m N Q y ∧
      (∀ j < inputEnd m N Q, y.mem (snapshotBase L m N Q + j) = x.mem j) ∧
      (∀ a, a < snapshotBase L m N Q ∨ snapshotBase L m N Q + inputEnd m N Q ≤ a →
        y.mem a = x.mem a) := by
  obtain ⟨p, hp, pp, pm, _⟩ := exec_parameters hm x hL hmemory hN hfit
  obtain ⟨l, hl, lp, lm⟩ := exec_layout p pp (by rw [pm]; exact hQ) hfit
  obtain ⟨y, hy, yp, ym⟩ := exec_saveInput l lp hfit
  refine ⟨y, (hp.seq (hl.seq hy)).mono (by unfold snapshotTime; omega), yp, ?_, ?_⟩
  · intro j hj
    rw [ym, ArrayCopy.copyPrefix_read hj, Nat.zero_add, lm, pm]
  · intro a ha
    rw [ym, ArrayCopy.copyPrefix_outside (by rcases ha with ha | ha <;> omega), lm, pm]

/-- Continue actual routing from computed parameters and actual original snapshot words. -/
public theorem exec_routingFromSnapshot {w L m N : ℕ} (hm : m ≤ L) (qs : List (Fin N × Fin N))
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
      ExecWithin w routingFromSnapshot x y (routingFromSnapshotTime L m N qs.length) ∧
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
    unfold routingFromSnapshotTime
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

/-- Real original coordinates suffice to establish all routing invariants and a protected
copy of the entire original input. Header zero and outside memory may be arbitrary. -/
public theorem exec_prepareRouting {w L m N : ℕ} (hm : m ≤ L) (qs : List (Fin N × Fin N))
    (x : Data 160) (hL : x.mem 1 = L) (hmemory : x.mem 2 = m) (hN : x.mem 3 = N)
    (hQ : x.mem 4 = qs.length)
    (hqueries : ∀ i < qs.length,
      x.mem (queryInputBase m N + 2 * i) = (Wanted.inputPairs qs i).1 ∧
        x.mem (queryInputBase m N + 2 * i + 1) = (Wanted.inputPairs qs i).2)
    (hfit : Fits w (wordBudget L m N qs.length)) :
    ∃ (y : Data 160) (old : ℕ → ℕ),
      ExecWithin w prepareRouting x y (routingTimeBound L m N qs.length) ∧
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
        y.mem (snapshotBase L m N qs.length + j) = x.mem j) ∧
      (∀ a, a < 5 ∨ groupedBase L m N qs.length ≤ a → y.mem a = x.mem a) := by
  have hgeom : 5 ≤ snapshotBase L m N qs.length ∧
      snapshotBase L m N qs.length + inputEnd m N qs.length ≤ groupedBase L m N qs.length := by
    simp only [snapshotBase, groupedBase, originalBase, codeBase, offsetBase, inputEnd]
    omega
  obtain ⟨s, hs, sp, ss, sf⟩ := exec_prepareSnapshot hm x hL hmemory hN hQ hfit
  obtain ⟨y, old, hy, yp, yg, yv, yo, ys, yf⟩ := exec_routingFromSnapshot hm qs s sp x.mem ss
    ((sf 1 (Or.inl (by omega))).trans hL) ((sf 2 (Or.inl (by omega))).trans hmemory)
    ((sf 3 (Or.inl (by omega))).trans hN) ((sf 4 (Or.inl (by omega))).trans hQ) hqueries hfit
  refine ⟨y, old, ?_, yp, yg, yv, yo, ys, ?_⟩
  · obtain ⟨p, A, B, hp, hr, hAB⟩ := ExecWithin.seq_iff.mp hs
    obtain ⟨l, C, E, hl, hs, hCE⟩ := ExecWithin.seq_iff.mp hr
    exact (hp.seq (hl.seq (hs.seq hy))).mono (by
      unfold snapshotTime routingFromSnapshotTime routingTimeBound at *
      omega)
  · intro a ha
    rw [yf a ha]
    exact sf a (by rcases ha with ha | ha <;> omega)

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct
