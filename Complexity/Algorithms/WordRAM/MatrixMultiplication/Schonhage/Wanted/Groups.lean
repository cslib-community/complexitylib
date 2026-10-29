/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted.Flat

/-!
# Consumer meaning of the computed query groups

## Main results

* `Wanted.code_span_eq_wantedStrings`: the actual stored offsets select exactly the
  original finite `wantedStrings` codes of each tile.
* `Wanted.originals_permutation`: the actual original-position words form a permutation,
  retaining all occurrences, including duplicate pairs.

These representation lemmas consume the memory equations returned by the initialized run.
They neither replace the native grouping code nor supply any input certificate to it.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open Finset

/-- An in-range tile key identifies exactly the original row and column bands. -/
theorem tileKey_eq_iff {L m N : ℕ} (hm : m ≤ L) (i j : Fin N) (T : ℕ × ℕ)
    (hT : T ∈ tiles L m N) :
    tileKey L m N (i.val, j.val) = T.1 * numBands L m N + T.2 ↔
      bandOf L m i.val = T.1 ∧ bandOf L m j.val = T.2 := by
  have hb : T.1 < numBands L m N ∧ T.2 < numBands L m N := by
    simpa only [tiles, mem_product, mem_range] using hT
  let u : Fin (numBands L m N) := ⟨bandOf L m i.val, bandOf_lt_numBands hm N i i.isLt⟩
  let v : Fin (numBands L m N) := ⟨bandOf L m j.val, bandOf_lt_numBands hm N j j.isLt⟩
  constructor
  · intro hk
    have he : finProdFinEquiv (u, v) = finProdFinEquiv
        ((⟨T.1, hb.1⟩ : Fin (numBands L m N)), ⟨T.2, hb.2⟩) := by
      apply Fin.ext
      change bandOf L m j.val + numBands L m N * bandOf L m i.val =
        T.2 + numBands L m N * T.1
      unfold tileKey at hk
      nlinarith only [hk]
    have hp := finProdFinEquiv.injective he
    exact ⟨congrArg (fun p => p.1.val) hp, congrArg (fun p => p.2.val) hp⟩
  · rintro ⟨hi, hj⟩
    simp only [tileKey, hi, hj]

/-- A tile's actual stored half-open span contains exactly the existing mathematical
`wantedStrings` codes. Duplicate list occurrences have the same set meaning and are
retained separately by the original-position permutation. -/
theorem code_span_eq_wantedStrings {L m N : ℕ} (hm : m ≤ L)
    (qs : List (Fin N × Fin N)) (μ : ℕ → ℕ) (T : ℕ × ℕ) (hT : T ∈ tiles L m N)
    (hvalues : ∀ i : Fin qs.length,
      μ (codeAddress L m N qs.length +
          CountingSort.position (tileKey L m N ∘ inputPairs qs) qs.length i.val) =
        (PrunedQuery.queryIndex
          (outStrOfPos (MaskTable.layout hm) (qs.get i).1 (qs.get i).2)).val)
    (hoffsets : ∀ t ≤ numBands L m N ^ 2,
      μ (offsetAddress L m N qs.length + t) =
        Nat.count (fun k => (tileKey L m N ∘ inputPairs qs) k < t) qs.length) :
    (Ico (μ (offsetAddress L m N qs.length + (T.1 * numBands L m N + T.2)))
      (μ (offsetAddress L m N qs.length + (T.1 * numBands L m N + T.2 + 1)))).image
        (fun j => μ (codeAddress L m N qs.length + j)) =
      (wantedStrings (MaskTable.layout hm) qs.toFinset T.1 T.2).image
        (fun w => (PrunedQuery.queryIndex w).val) := by
  let key := tileKey L m N ∘ inputPairs qs
  let values := fun i => (PrunedQuery.queryIndex
    (outStrOfPos (MaskTable.layout hm) (inputPairs qs i).1 (inputPairs qs i).2)).val
  let t := T.1 * numBands L m N + T.2
  have hb : T.1 < numBands L m N ∧ T.2 < numBands L m N := by
    simpa only [tiles, mem_product, mem_range] using hT
  have ht : t < numBands L m N ^ 2 := by
    dsimp [t]
    nlinarith only [Nat.mul_le_mul_right (numBands L m N) (Nat.succ_le_of_lt hb.1), hb.2]
  have hv (i : ℕ) (hi : i < qs.length) :
      μ (codeAddress L m N qs.length + CountingSort.position key qs.length i) = values i := by
    dsimp only [values]
    rw [inputPairs_get qs ⟨i, hi⟩]
    exact hvalues ⟨i, hi⟩
  rw [hoffsets _ ht.le, hoffsets _ (Nat.succ_le_of_lt ht)]
  rw [CountingSort.scatter_span_image key qs.length t _ values hv]
  simp only [wantedStrings, image_image, Function.comp_def]
  ext code
  constructor
  · intro hc
    obtain ⟨i, hi, hc⟩ := mem_image.mp hc
    obtain ⟨hin, hik⟩ := mem_filter.mp hi
    have hiQ := mem_range.mp hin
    have hp : inputPairs qs i = ((qs.get ⟨i, hiQ⟩).1.val, (qs.get ⟨i, hiQ⟩).2.val) :=
      inputPairs_get qs ⟨i, hiQ⟩
    have hk : tileKey L m N ((qs.get ⟨i, hiQ⟩).1.val, (qs.get ⟨i, hiQ⟩).2.val) = t := by
      simpa only [key, Function.comp_def, hp] using hik
    have hband := (tileKey_eq_iff hm (qs.get ⟨i, hiQ⟩).1 (qs.get ⟨i, hiQ⟩).2 T hT).mp hk
    exact mem_image.mpr ⟨qs.get ⟨i, hiQ⟩,
      mem_filter.mpr ⟨List.mem_toFinset.mpr (List.get_mem _ _), hband⟩,
      by simpa only [values, hp] using hc⟩
  · intro hc
    obtain ⟨q, hq, hc⟩ := mem_image.mp hc
    obtain ⟨hq, hband⟩ := mem_filter.mp hq
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp (List.mem_toFinset.mp hq)
    have hp := inputPairs_get qs i
    have hk : key i.val = t := by
      dsimp only [key, Function.comp_def]
      rw [hp]
      exact (tileKey_eq_iff hm (qs.get i).1 (qs.get i).2 T hT).mpr hband
    exact mem_image.mpr ⟨i.val, mem_filter.mpr ⟨mem_range.mpr i.isLt, hk⟩,
      by simpa only [values, hp] using hc⟩

/-- The actual stored original indices are in range, injective, and cover every input
position. Equal original coordinate pairs therefore retain their separate occurrences. -/
theorem originals_permutation {L m N : ℕ} (qs : List (Fin N × Fin N)) (μ : ℕ → ℕ)
    (h : ∀ i : Fin qs.length,
      μ (originalAddress L m N qs.length +
        CountingSort.position (tileKey L m N ∘ inputPairs qs) qs.length i.val) = i.val) :
    (∀ j < qs.length, μ (originalAddress L m N qs.length + j) < qs.length) ∧
      Function.Injective (fun j : Fin qs.length => μ (originalAddress L m N qs.length + j.val)) ∧
      (range qs.length).image (fun j => μ (originalAddress L m N qs.length + j)) =
        range qs.length := by
  let key := tileKey L m N ∘ inputPairs qs
  have inverse (j : Fin qs.length) : ∃ i : Fin qs.length,
      CountingSort.position key qs.length i.val = j.val ∧
        μ (originalAddress L m N qs.length + j.val) = i.val := by
    obtain ⟨i, hi⟩ := (CountingSort.position_bijective key qs.length).surjective j
    have hp := congrArg (fun k : Fin qs.length => k.val) hi
    exact ⟨i, hp, hp ▸ h i⟩
  have hrange (j : ℕ) (hj : j < qs.length) :
      μ (originalAddress L m N qs.length + j) < qs.length := by
    obtain ⟨i, _, hi⟩ := inverse ⟨j, hj⟩
    exact hi ▸ i.isLt
  refine ⟨hrange, ?_, ?_⟩
  · intro i j hij
    obtain ⟨a, ha, hia⟩ := inverse i
    obtain ⟨b, hb, hjb⟩ := inverse j
    have hab : a.val = b.val := hia.symm.trans (hij.trans hjb)
    exact Fin.ext (ha.symm.trans ((congrArg (CountingSort.position key qs.length) hab).trans hb))
  · ext i
    constructor
    · intro hi
      obtain ⟨j, hj, rfl⟩ := mem_image.mp hi
      exact mem_range.mpr (hrange j (mem_range.mp hj))
    · intro hi
      have hin := mem_range.mp hi
      exact mem_image.mpr ⟨CountingSort.position key qs.length i,
        mem_range.mpr (CountingSort.position_lt key hin), h ⟨i, hin⟩⟩

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted
