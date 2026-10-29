/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted.Exec
public import Complexity.Foundations.Data.List.RowMajor
import Mathlib.Data.List.GetD

/-!
# Ordinary initialized wanted-position inputs

## Main definitions

* `Wanted.input`: four raw headers followed by the ordinary interleaved coordinate words.
* `Wanted.inputPairs`: a zero extension of that original finite list for natural-index invariants.

## Main results

* `Wanted.input_fits`: the original header, length and coordinate words fit the admitted width.
* `Wanted.input_word`: initialized memory contains each original coordinate at its actual address.
* `Wanted.exec_input`: the fixed program computes the grouped arrays from actual `State.init`.

No powers, valid masks, tile keys, offsets, query codes or permutation words occur in the input.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Four unsigned scalar headers followed by each row/column pair in original list order.
The standard `State.init` length word precedes this payload at address zero. -/
def input {N : ℕ} (L m : ℕ) (qs : List (Fin N × Fin N)) : List ℕ :=
  [L, m, N, qs.length] ++ (List.finRange qs.length).flatMap (fun i =>
    List.ofFn (fun s : Fin 2 => if s = 0 then (qs.get i).1.val else (qs.get i).2.val))

/-- Ordinary input positions extended by zero outside the supplied list. This is a
mathematical view of original words, not a query-code or layout certificate. -/
def inputPairs {N : ℕ} (qs : List (Fin N × Fin N)) (i : ℕ) : ℕ × ℕ :=
  if hi : i < qs.length then ((qs.get ⟨i, hi⟩).1.val, (qs.get ⟨i, hi⟩).2.val) else (0, 0)

/-- Every in-range position is exactly its original pair. -/
@[simp]
theorem inputPairs_get {N : ℕ} (qs : List (Fin N × Fin N)) (i : Fin qs.length) :
    inputPairs qs i.val = ((qs.get i).1.val, (qs.get i).2.val) := by
  simp [inputPairs, i.isLt]

/-- The native length header and coordinate input end at the concrete allocation boundary. -/
theorem input_length {N : ℕ} (L m : ℕ) (qs : List (Fin N × Fin N)) :
    (input L m qs).length + 1 = inputLimit qs.length := by
  simp only [input, List.flatMap_ofFn_prod, List.length_append, List.length_ofFn,
    List.length_cons, List.length_nil, inputLimit]
  omega

/-- Both original coordinates are below the original matrix dimension. -/
theorem inputPairs_lt {N : ℕ} (qs : List (Fin N × Fin N)) (i : ℕ) (hi : i < qs.length) :
    (inputPairs qs i).1 < N ∧ (inputPairs qs i).2 < N := by
  have he := inputPairs_get qs ⟨i, hi⟩
  rw [he]
  exact ⟨(qs.get ⟨i, hi⟩).1.isLt, (qs.get ⟨i, hi⟩).2.isLt⟩

/-- The exact initialized row/column word, with address calculations in original list order. -/
theorem input_word {N : ℕ} (L m : ℕ) (qs : List (Fin N × Fin N)) (i : Fin qs.length)
    (s : Fin 2) :
    (State.init (input L m qs) : State 96).data.mem (5 + 2 * i.val + s.val) =
      if s = 0 then (qs.get i).1.val else (qs.get i).2.val := by
  change (Data.init (input L m qs) : Data 96).mem _ = _
  rw [show 5 + 2 * i.val + s.val = (4 + (i.val * 2 + s.val)) + 1 by omega,
    Data.init_mem_succ]
  unfold input
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.add_sub_cancel_left]
  exact List.getD_flatMap_ofFn (fun j t =>
    if t = (0 : Fin 2) then (qs.get j).1.val else (qs.get j).2.val) 0 i s

/-- Header, length and every coordinate word fit from the same original numerical budget. -/
theorem input_fits {w L m N : ℕ} (hm : m ≤ L) (qs : List (Fin N × Fin N))
    (hfit : Fits w (wordBudget L m N qs.length)) : InputFits w (input L m qs) := by
  have hl := local_fits hfit
  have hend := memoryLimit_eq L m N qs.length
  have h2 := Nat.zero_le (2 ^ L)
  have h10 := Nat.zero_le (10 ^ L)
  have hfN : Fits w N := hl.of_le (by omega)
  refine ⟨?_, ?_⟩
  · have hi := input_length L m qs
    apply hl.of_le
    unfold inputLimit at hi
    omega
  · intro v hv
    simp only [input, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with (rfl | rfl | rfl | rfl) | hv
    · exact hl.of_le (by omega)
    · exact hl.of_le (by omega)
    · exact hfN
    · exact hl.of_le (by omega)
    · obtain ⟨i, _, hv⟩ := List.mem_flatMap.mp hv
      obtain ⟨s, rfl⟩ := List.mem_ofFn.mp hv
      split
      · exact hfN.of_le (qs.get i).1.isLt.le
      · exact hfN.of_le (qs.get i).2.isLt.le

/-- Complete execution from the actual initialized list, with guaranteed input fit and a
bounded returned state. All auxiliary tables, counts, offsets and codes are computed natively. -/
theorem exec_input {w L m N : ℕ} (hm : m ≤ L) (qs : List (Fin N × Fin N))
    (hfit : Fits w (wordBudget L m N qs.length)) :
    InputFits w (input L m qs) ∧
    ∃ y, ExecWithin w program (State.init (input L m qs) : State 96).data y
        (timeBound L m N qs.length) ∧ Parameters L m N qs.length y ∧ y.Bounded w ∧
      (∀ i : Fin qs.length,
        y.mem (codeAddress L m N qs.length +
            CountingSort.position (tileKey L m N ∘ inputPairs qs) qs.length i.val) =
            (PrunedQuery.queryIndex
              (outStrOfPos (MaskTable.layout hm) (qs.get i).1 (qs.get i).2)).val ∧
          y.mem (originalAddress L m N qs.length +
            CountingSort.position (tileKey L m N ∘ inputPairs qs) qs.length i.val) = i.val) ∧
      (∀ t ≤ numBands L m N ^ 2, y.mem (offsetAddress L m N qs.length + t) =
        Nat.count (fun k => (tileKey L m N ∘ inputPairs qs) k < t) qs.length) ∧
      y.mem (offsetAddress L m N qs.length + numBands L m N ^ 2) = qs.length ∧
      (∀ a, a < inputLimit qs.length ∨ memoryLimit L m N qs.length ≤ a →
        y.mem a = (State.init (input L m qs) : State 96).data.mem a) := by
  have hfitInput := input_fits hm qs hfit
  let x : Data 96 := (State.init (input L m qs)).data
  have hL : x.mem 1 = L := by simp [x, State.init, Data.init, input]
  have hM : x.mem 2 = m := by simp [x, State.init, Data.init, input]
  have hN : x.mem 3 = N := by simp [x, State.init, Data.init, input]
  have hQ : x.mem 4 = qs.length := by simp [x, State.init, Data.init, input]
  have hwords (i : ℕ) (hi : i < qs.length) :
      x.mem (5 + 2 * i) = (inputPairs qs i).1 ∧
        x.mem (5 + 2 * i + 1) = (inputPairs qs i).2 := by
    have hr := input_word L m qs ⟨i, hi⟩ 0
    have hc := input_word L m qs ⟨i, hi⟩ 1
    rw [inputPairs_get qs ⟨i, hi⟩]
    simpa only [Fin.val_zero, Fin.val_one, Nat.add_zero,
      ↓reduceIte, Fin.isValue, Fin.reduceEq] using And.intro hr hc
  obtain ⟨y, he, hp, hv, ho, hlast, hf⟩ := exec_program hm (inputPairs qs)
    (inputPairs_lt qs) x hL hM hN hQ hwords hfit
  refine ⟨hfitInput, y, he, hp, he.bounded (Data.Bounded.init hfitInput), ?_, ho, hlast, hf⟩
  intro i
  simpa only [inputPairs_get] using hv i.val i.isLt

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted
