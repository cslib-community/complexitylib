/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Product.Groups
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted.Groups

/-!
# Memory invariants for the saved routing arrays

## Main definitions

* `QueriedProduct.SavedGroups`: protected words agree with an earlier actual router state.

## Main results

* `QueriedProduct.SavedGroups.reframe`: kernel and producer frames retain the saved arrays.
* `QueriedProduct.router_code_lt`: executed stable scatter gives a valid query code at every
  grouped position, including duplicate requests.
* `QueriedProduct.SavedGroups.span_bounds`: actual saved offsets form admitted kernel spans.

The earlier memory is a proof reference to an executed state, not program input. The native
copy theorem establishes these equalities before any low-memory reuse occurs.
-/

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Values copied from the actual router state into protected caller-owned arrays. -/
public structure SavedGroups (L m N Q : ℕ) (old μ : ℕ → ℕ) : Prop where
  /-- All actual offsets, including the terminal offset. -/
  offsets : ∀ t ≤ numBands L m N ^ 2,
    μ (offsetBase L m N Q + t) = old (Wanted.offsetAddress L m N Q + t)
  /-- All actual grouped codes. -/
  codes : ∀ j < Q, μ (codeBase L m N Q + j) = old (Wanted.codeAddress L m N Q + j)
  /-- All actual original-position words. -/
  originals : ∀ j < Q,
    μ (originalBase L m N Q + j) = old (Wanted.originalAddress L m N Q + j)

/-- Preserving the protected readonly interval preserves the saved routing arrays. -/
public theorem SavedGroups.reframe {L m N Q : ℕ} {old μ ν : ℕ → ℕ}
    (h : SavedGroups L m N Q old μ)
    (hf : ∀ a, offsetBase L m N Q ≤ a → a < groupedBase L m N Q → ν a = μ a) :
    SavedGroups L m N Q old ν := by
  have hc : offsetBase L m N Q + numBands L m N ^ 2 + 1 = codeBase L m N Q := by
    unfold codeBase
    omega
  have ho : codeBase L m N Q + Q = originalBase L m N Q := rfl
  have hg : originalBase L m N Q + Q = groupedBase L m N Q := rfl
  constructor
  · intro t ht
    exact (hf _ (by omega) (by omega)).trans (h.offsets t ht)
  · intro j hj
    exact (hf _ (by omega) (by omega)).trans (h.codes j hj)
  · intro j hj
    exact (hf _ (by omega) (by omega)).trans (h.originals j hj)

/-- Stable scatter covers every grouped cell, so every stored code is a valid query index.
The proof uses the existing permutation theorem rather than a supplied inverse table. -/
public theorem router_code_lt {L m N : ℕ} (hm : m ≤ L) (qs : List (Fin N × Fin N))
    (old : ℕ → ℕ)
    (hvalues : ∀ i : Fin qs.length,
      old (Wanted.codeAddress L m N qs.length +
          CountingSort.position (Wanted.tileKey L m N ∘ Wanted.inputPairs qs) qs.length i) =
        (PrunedQuery.queryIndex
          (outStrOfPos (MaskTable.layout hm) (qs.get i).1 (qs.get i).2)).val)
    (j : ℕ) (hj : j < qs.length) :
    old (Wanted.codeAddress L m N qs.length + j) < 10 ^ L := by
  obtain ⟨i, hi⟩ := (CountingSort.position_bijective
    (Wanted.tileKey L m N ∘ Wanted.inputPairs qs) qs.length).surjective ⟨j, hj⟩
  have hp := congrArg (fun k : Fin qs.length => k.val) hi
  change CountingSort.position (Wanted.tileKey L m N ∘ Wanted.inputPairs qs) qs.length i = j at hp
  have hv := hvalues i
  rw [hp] at hv
  rw [hv]
  exact (PrunedQuery.queryIndex _).isLt

/-- The actual protected offset words satisfy the kernel's monotone span and count bounds.
These inequalities follow from the executed prefix-count meanings, not input certificates. -/
public theorem SavedGroups.span_bounds {L m N Q : ℕ} {old μ : ℕ → ℕ}
    (h : SavedGroups L m N Q old μ) (key : ℕ → ℕ)
    (hoffsets : ∀ t ≤ numBands L m N ^ 2,
      old (Wanted.offsetAddress L m N Q + t) = Nat.count (fun k => key k < t) Q)
    {t : ℕ} (ht : t < numBands L m N ^ 2) :
    μ (offsetBase L m N Q + t) ≤ μ (offsetBase L m N Q + t + 1) ∧
      μ (offsetBase L m N Q + t + 1) ≤ Q := by
  rw [show offsetBase L m N Q + t + 1 = offsetBase L m N Q + (t + 1) by omega,
    h.offsets t ht.le, h.offsets (t + 1) (by omega), hoffsets t ht.le,
    hoffsets (t + 1) (by omega)]
  exact ⟨Nat.count_mono_left (fun k _ hk => by omega), Nat.count_le _⟩

/-- A typed view of the actual saved code span requests exactly the original finite tile
set. This uses the existing router's span theorem; the native caller constructs the view
by decoding its real words, rather than receiving a query-set or routing certificate. -/
public theorem SavedGroups.span_queries {L m N : ℕ} (hm : m ≤ L)
    (qs : List (Fin N × Fin N)) {old μ : ℕ → ℕ} (h : SavedGroups L m N qs.length old μ)
    (hvalues : ∀ i : Fin qs.length,
      old (Wanted.codeAddress L m N qs.length +
          CountingSort.position (Wanted.tileKey L m N ∘ Wanted.inputPairs qs) qs.length i) =
        (PrunedQuery.queryIndex
          (outStrOfPos (MaskTable.layout hm) (qs.get i).1 (qs.get i).2)).val)
    (hoffsets : ∀ t ≤ numBands L m N ^ 2,
      old (Wanted.offsetAddress L m N qs.length + t) =
        Nat.count (fun k => (Wanted.tileKey L m N ∘ Wanted.inputPairs qs) k < t) qs.length)
    (T : ℕ × ℕ) (hT : T ∈ Cslib.Algorithms.MatrixMultiplication.Schonhage.tiles L m N) (a b : ℕ)
    (ha : μ (offsetBase L m N qs.length + (T.1 * numBands L m N + T.2)) = a)
    (hb : μ (offsetBase L m N qs.length + (T.1 * numBands L m N + T.2 + 1)) = b)
    (queries : Fin (b - a) → OutStr L)
    (hinput : ∀ i, μ (codeBase L m N qs.length + (a + i.val)) =
      (PrunedQuery.queryIndex (queries i)).val) :
    Finset.univ.image queries = wantedStrings (MaskTable.layout hm) qs.toFinset T.1 T.2 := by
  have hband : T.1 < numBands L m N ∧ T.2 < numBands L m N := by
    simpa only [Cslib.Algorithms.MatrixMultiplication.Schonhage.tiles,
      Finset.mem_product, Finset.mem_range] using hT
  have ht : T.1 * numBands L m N + T.2 < numBands L m N ^ 2 := by
    nlinarith only [Nat.mul_le_mul_right (numBands L m N) (Nat.succ_le_of_lt hband.1), hband.2]
  have has : old (Wanted.offsetAddress L m N qs.length +
      (T.1 * numBands L m N + T.2)) = a := (h.offsets _ ht.le).symm.trans ha
  have hbs : old (Wanted.offsetAddress L m N qs.length +
      (T.1 * numBands L m N + T.2 + 1)) = b :=
    (h.offsets _ (by omega)).symm.trans hb
  have habQ : a ≤ b ∧ b ≤ qs.length := by
    have hs := h.span_bounds (Wanted.tileKey L m N ∘ Wanted.inputPairs qs) hoffsets ht
    simpa only [ha, show offsetBase L m N qs.length +
      (T.1 * numBands L m N + T.2) + 1 = offsetBase L m N qs.length +
        (T.1 * numBands L m N + T.2 + 1) by omega, hb] using hs
  have hword (i : Fin (b - a)) : old (Wanted.codeAddress L m N qs.length + (a + i.val)) =
      (PrunedQuery.queryIndex (queries i)).val := by
    rw [← h.codes (a + i.val) (by have hi := i.isLt; omega)]
    exact hinput i
  have hspan := Wanted.code_span_eq_wantedStrings hm qs old T hT hvalues hoffsets
  rw [has, hbs] at hspan
  have hinj : Function.Injective (fun v : OutStr L => (PrunedQuery.queryIndex v).val) := by
    intro u v he
    simpa only [PrunedQuery.queryAt_queryIndex] using
      congrArg PrunedQuery.queryAt (Fin.ext he)
  ext w
  constructor
  · intro hw
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hw
    have hcode : (PrunedQuery.queryIndex (queries i)).val ∈
        (wantedStrings (MaskTable.layout hm) qs.toFinset T.1 T.2).image
          (fun w => (PrunedQuery.queryIndex w).val) := by
      rw [← hspan]
      exact Finset.mem_image.mpr ⟨a + i.val, Finset.mem_Ico.mpr
        ⟨by omega, by have hi := i.isLt; omega⟩, hword i⟩
    obtain ⟨v, hv, he⟩ := Finset.mem_image.mp hcode
    exact hinj he ▸ hv
  · intro hw
    have hcode : (PrunedQuery.queryIndex w).val ∈
        (Finset.Ico a b).image (fun j => old (Wanted.codeAddress L m N qs.length + j)) := by
      rw [hspan]
      exact Finset.mem_image.mpr ⟨w, hw, rfl⟩
    obtain ⟨j, hj, he⟩ := Finset.mem_image.mp hcode
    have hj' := Finset.mem_Ico.mp hj
    let i : Fin (b - a) := ⟨j - a, by omega⟩
    have hai : a + i.val = j := by dsimp [i]; omega
    have hread := hword i
    rw [hai] at hread
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hinj (hread.symm.trans he)⟩

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct
