/-
Copyright (c) 2026 Samuel Schlesinger, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Init

/-!
# One-hot bit lists

`listSingle dimension index` is the bit list of length `dimension` whose only `true` coordinate
is `index`; an index outside the dimension gives all zeros. It is the list form of a one-hot row
in an explicit relation table (`CSP.Table.exactlyOne`) and of the basis vector
`Pi.single index true` (`listSingle_eq_ofFn_single` in `BitString.List.Operations`).

## Main definitions

* `Cslib.BitString.listSingle`: the one-hot list of a given length.

## Main results

* `Cslib.BitString.listSingle_eq_ofFn`: an in-range one-hot list as `List.ofFn`.
* `Cslib.BitString.listSingle_succ_zero`, `Cslib.BitString.listSingle_succ_succ`: the recursive
  description by the first coordinate.
* `Cslib.BitString.count_true_listSingle`, `Cslib.BitString.exists_listSingle_of_count_true`:
  the one-hot lists of a given length are exactly the lists with one `true` coordinate.
-/

@[expose] public section

namespace Cslib.BitString

/-- A coordinate mask, with all zeros when the index is outside the requested dimension. -/
def listSingle (dimension index : ℕ) : List Bool :=
  (List.range dimension).map (fun coordinate => decide (index = coordinate))

/-- An in-range one-hot list is the list of the indicator of its index. -/
theorem listSingle_eq_ofFn {n : ℕ} (index : Fin n) :
    listSingle n index = List.ofFn (fun j : Fin n => decide (j = index)) := by
  apply List.ext_getElem (by simp [listSingle])
  intro j _ _
  simp [listSingle, Fin.ext_iff, eq_comm]

/-- A one-hot list at position zero starts with `true`. -/
theorem listSingle_succ_zero (dimension : ℕ) :
    listSingle (dimension + 1) 0 = true :: List.replicate dimension false := by
  simp [listSingle, List.range_succ_eq_map, List.map_map, Function.comp_def, List.map_const']

/-- Shifting the selected position prepends a zero. -/
theorem listSingle_succ_succ (dimension index : ℕ) :
    listSingle (dimension + 1) (index + 1) = false :: listSingle dimension index := by
  simp [listSingle, List.range_succ_eq_map, List.map_map, Function.comp_def]

/-- An in-range one-hot list has precisely one true coordinate. -/
theorem count_true_listSingle {dimension index : ℕ} (h : index < dimension) :
    (listSingle dimension index).count true = 1 := by
  induction dimension generalizing index with
  | zero => omega
  | succ dimension ih =>
    cases index with
    | zero => simp [listSingle_succ_zero, List.count_replicate]
    | succ index => simpa [listSingle_succ_succ] using ih (by omega)

/-- Every list with exactly one true coordinate is a one-hot list. -/
theorem exists_listSingle_of_count_true {row : List Bool} (h : row.count true = 1) :
    ∃ index < row.length, listSingle row.length index = row := by
  induction row with
  | nil => simp at h
  | cons bit row ih =>
    cases bit with
    | false =>
      have ht : row.count true = 1 := by simpa using h
      obtain ⟨index, hi, hr⟩ := ih ht
      exact ⟨index + 1, by simpa using Nat.succ_lt_succ hi,
        by simpa only [List.length_cons, listSingle_succ_succ] using congrArg (false :: ·) hr⟩
    | true =>
      have ht : true ∉ row := List.count_eq_zero.mp (by simpa using h)
      have hr : row = List.replicate row.length false := List.eq_replicate_of_mem
        (fun bit hb => by cases bit <;> simp_all)
      exact ⟨0, by simp, by simp only [List.length_cons, listSingle_succ_zero, ← hr]⟩

end Cslib.BitString
