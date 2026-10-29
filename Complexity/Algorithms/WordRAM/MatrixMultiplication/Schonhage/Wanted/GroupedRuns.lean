/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted.Groups
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted.Width

/-!
# Initialized runs with the finite wanted-set interface

## Main results

* `Wanted.runs_grouped`: one actual initialized native run computes each tile's query-code
  span and a permutation retaining all original positions, within the charged bound.

This is the routing interface for subsequent shared-band and pruned-kernel composition.
It does not evaluate the product or reconstruct answers. Stage execution lemmas in the
supporting modules are internal implementation APIs; consumers use this theorem or `runs`.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open Finset

/-- Actual native grouping from the original raw coordinate list at every sufficiently
wide physical width. The same final memory supplies the tile spans, permutation and frame.
No layout, query-code, count or permutation certificate is supplied as input. -/
theorem runs_grouped {W L m N : ℕ} (hm : m ≤ L) (qs : List (Fin N × Fin N))
    (hW : admissionWidth L m N qs.length ≤ W) :
    InputFits W (input L m qs) ∧
    ∃ y n, n + 1 ≤ 128 * (L + 1) *
        (qs.length + numBands L m N ^ 2 + 2 ^ L + 1) ∧
      Runs W (program.program codes) (State.init (input L m qs)) ⟨program.size, y⟩ n ∧
      Executes W (program.program codes) (State.init (input L m qs))
        (codeAddress L m N qs.length) (n + 1) ∧ y.Bounded W ∧
      (∀ i : Fin qs.length,
        y.mem (codeAddress L m N qs.length +
            CountingSort.position (tileKey L m N ∘ inputPairs qs) qs.length i.val) =
            (PrunedQuery.queryIndex
              (outStrOfPos (MaskTable.layout hm) (qs.get i).1 (qs.get i).2)).val ∧
          y.mem (originalAddress L m N qs.length +
            CountingSort.position (tileKey L m N ∘ inputPairs qs) qs.length i.val) = i.val) ∧
      (∀ T ∈ tiles L m N,
        (Ico (y.mem (offsetAddress L m N qs.length + (T.1 * numBands L m N + T.2)))
          (y.mem (offsetAddress L m N qs.length + (T.1 * numBands L m N + T.2 + 1)))).image
            (fun j => y.mem (codeAddress L m N qs.length + j)) =
          (wantedStrings (MaskTable.layout hm) qs.toFinset T.1 T.2).image
            (fun w => (PrunedQuery.queryIndex w).val)) ∧
      (∀ j < qs.length, y.mem (codeAddress L m N qs.length + j) < 10 ^ L) ∧
      (∀ t < numBands L m N ^ 2,
        y.mem (offsetAddress L m N qs.length + t) ≤
          y.mem (offsetAddress L m N qs.length + (t + 1)) ∧
        y.mem (offsetAddress L m N qs.length + (t + 1)) ≤ qs.length) ∧
      (∀ j < qs.length, y.mem (originalAddress L m N qs.length + j) < qs.length) ∧
      Function.Injective
        (fun j : Fin qs.length => y.mem (originalAddress L m N qs.length + j.val)) ∧
      (range qs.length).image (fun j => y.mem (originalAddress L m N qs.length + j)) =
        range qs.length ∧
      y.mem (offsetAddress L m N qs.length + numBands L m N ^ 2) = qs.length ∧
      (∀ a, a < inputLimit qs.length ∨ memoryLimit L m N qs.length ≤ a →
        y.mem a = (State.init (input L m qs) : State 96).data.mem a) := by
  obtain ⟨hi, y, n, hn, hr, he, hb, hv, ho, ht, hf⟩ := runs_wide hm qs hW
  obtain ⟨hperm, hinj, hcover⟩ := originals_permutation qs y.mem (fun i => (hv i).2)
  refine ⟨hi, y, n, (Nat.succ_le_succ hn).trans (timeBound_add_one_le L m N qs.length),
    hr, he, hb, hv, ?_, ?_, ?_, hperm, hinj, hcover, ht, hf⟩
  · intro T hT
    exact code_span_eq_wantedStrings hm qs y.mem T hT (fun i => (hv i).1) ho
  · intro j hj
    obtain ⟨i, hi⟩ :=
      (CountingSort.position_bijective (tileKey L m N ∘ inputPairs qs) qs.length).surjective
        ⟨j, hj⟩
    have hp := congrArg (fun k : Fin qs.length => k.val) hi
    change CountingSort.position (tileKey L m N ∘ inputPairs qs) qs.length i.val = j at hp
    have hvj := (hv i).1
    rw [hp] at hvj
    rw [hvj]
    exact (PrunedQuery.queryIndex _).isLt
  · intro t ht
    rw [ho t ht.le, ho (t + 1) (Nat.succ_le_of_lt ht)]
    exact ⟨Nat.count_mono_left (fun _ _ hk => Nat.lt_succ_of_lt hk), Nat.count_le _⟩

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted
