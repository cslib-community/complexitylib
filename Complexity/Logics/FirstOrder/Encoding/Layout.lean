/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Encoding
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Frame

/-!
# The positions of the bits of an encoded structure

The encoding `encStructure (n, tables)` of an input is the framed cardinality in unary followed by
the framed truth tables (`Cslib.Logic.encStructure_eq`). This file locates its bits: the markers of
the unary cardinality, and for each table its start (`Cslib.Logic.tableStart`), its markers, its
bits and its terminator. Past the last table there is nothing to read. These are the facts an
algorithm with random access to the encoding needs, such as the logarithmic-space model checker
`Cslib.Logic.Vocabulary.modelChecker`.

## Main definitions

* `Cslib.Logic.tableStart`: the position of a truth table in the encoding of an input.

## Main results

* `Cslib.Logic.encStructure_eq`: the encoding of an input as a concatenation of frames.
* `Cslib.Logic.drop_tableStart`: the encoding from the start of a table on.
* `Cslib.Logic.getElem?_encStructure_two_mul`, `Cslib.Logic.getElem?_encStructure_two_mul_card`:
  the markers of the cardinality.
* `Cslib.Logic.getElem?_encStructure_tableStart_two_mul`,
  `Cslib.Logic.getElem?_encStructure_tableStart_two_mul_add_one`,
  `Cslib.Logic.getElem?_encStructure_tableStart_two_mul_length`: the markers, bits and terminator
  of a table.
* `Cslib.Logic.getElem?_encStructure_tableStart_length_add`: nothing follows the last table.

## References

* [N. Immerman, *Descriptive Complexity*, Section 2.1][Immerman1999]
-/

@[expose] public section

namespace Cslib.Logic

open Turing.MultiTapeTM

/-- The encoding of an input: its framed cardinality in unary, then its framed tables. -/
theorem encStructure_eq (a : EncodedStructure) :
    encStructure a = frame (List.replicate a.1 true) ++ a.2.flatMap frame := by
  simp only [encStructure, encList, encPair_apply, encUnary_apply, encBits]
  rfl

/-- The position of the `i`-th truth table in the encoding of an input; past the last table, the
length of the encoding. -/
def tableStart (a : EncodedStructure) (i : ℕ) : ℕ :=
  2 * a.1 + 1 + ((a.2.take i).map fun t => 2 * t.length + 1).sum

/-- The encoding from the `i`-th table on. -/
theorem drop_tableStart (a : EncodedStructure) (i : ℕ) :
    (encStructure a).drop (tableStart a i) = (a.2.drop i).flatMap frame := by
  have h : a.2.flatMap frame = (a.2.take i).flatMap frame ++ (a.2.drop i).flatMap frame := by
    rw [← List.flatMap_append, List.take_append_drop]
  rw [encStructure_eq, tableStart, ← List.drop_drop, List.drop_left' (by simp [length_frame]), h]
  exact List.drop_left' (length_flatMap_frame _)

/-- Indexing `encStructure a` at `tableStart a i + q` reads position `q` in the framed tables
starting at index `i`. -/
theorem getElem?_encStructure_tableStart_add (a : EncodedStructure) (i q : ℕ) :
    (encStructure a)[tableStart a i + q]? = ((a.2.drop i).flatMap frame)[q]? := by
  rw [← drop_tableStart, List.getElem?_drop]

/-- The total length of `encStructure a` equals `tableStart a a.2.length`. -/
theorem length_encStructure (a : EncodedStructure) :
    (encStructure a).length = tableStart a a.2.length := by
  rw [encStructure_eq, tableStart, List.take_length, List.length_append, length_frame,
    length_flatMap_frame, List.length_replicate]

/-- For `i < a.2.length`, `tableStart a (i + 1)` advances past the framed `i`-th table of length
`2 * a.2[i].length + 1`. -/
theorem tableStart_succ {a : EncodedStructure} {i : ℕ} (hi : i < a.2.length) :
    tableStart a (i + 1) = tableStart a i + 2 * a.2[i].length + 1 := by
  simp only [tableStart, List.take_succ_eq_append_getElem hi, List.map_append, List.sum_append,
    List.map_singleton, List.sum_singleton]
  omega

/-- `tableStart a` is monotone in the table index. -/
theorem tableStart_mono (a : EncodedStructure) {i j : ℕ} (h : i ≤ j) :
    tableStart a i ≤ tableStart a j := by
  induction j, h using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih =>
    rcases lt_or_ge j a.2.length with hj | hj
    · rw [tableStart_succ hj]
      omega
    · simp only [tableStart, List.take_of_length_le hj,
        List.take_of_length_le (show a.2.length ≤ j + 1 by omega)] at ih ⊢
      exact ih

/-- Every table start position is at most `(encStructure a).length`. -/
theorem tableStart_le_length (a : EncodedStructure) (i : ℕ) :
    tableStart a i ≤ (encStructure a).length := by
  rcases le_or_gt i a.2.length with h | h
  · rw [length_encStructure]
    exact tableStart_mono a h
  · simp only [tableStart, List.take_of_length_le h.le]
    rw [length_encStructure, tableStart, List.take_length]

/-- The framed unary cardinality prefix of length `2 * a.1 + 1` fits within `encStructure a`. -/
theorem two_mul_card_add_one_le_length (a : EncodedStructure) :
    2 * a.1 + 1 ≤ (encStructure a).length :=
  (Nat.le_add_right _ _).trans (tableStart_le_length a 0)

/-! ### The bits -/

/-- The markers of the cardinality. -/
theorem getElem?_encStructure_two_mul {a : EncodedStructure} {k : ℕ} (hk : k < a.1) :
    (encStructure a)[2 * k]? = some true := by
  rw [encStructure_eq, List.getElem?_append_left
      (by simp only [length_frame, List.length_replicate]; omega),
    getElem?_frame_two_mul (by simpa using hk)]

/-- The terminator of the cardinality. -/
theorem getElem?_encStructure_two_mul_card (a : EncodedStructure) :
    (encStructure a)[2 * a.1]? = some false := by
  rw [encStructure_eq, List.getElem?_append_left (by simp [length_frame])]
  simpa using getElem?_frame_two_mul_length (List.replicate a.1 true)

private theorem flatMap_frame_drop {a : EncodedStructure} {i : ℕ} (hi : i < a.2.length) :
    (a.2.drop i).flatMap frame = frame a.2[i] ++ (a.2.drop (i + 1)).flatMap frame := by
  rw [List.drop_eq_getElem_cons hi, List.flatMap_cons]

/-- The markers of a table. -/
theorem getElem?_encStructure_tableStart_two_mul {a : EncodedStructure} {i j : ℕ}
    (hi : i < a.2.length) (hj : j < a.2[i].length) :
    (encStructure a)[tableStart a i + 2 * j]? = some true := by
  rw [getElem?_encStructure_tableStart_add, flatMap_frame_drop hi,
    List.getElem?_append_left (by simp only [length_frame]; omega), getElem?_frame_two_mul hj]

/-- The bits of a table. -/
theorem getElem?_encStructure_tableStart_two_mul_add_one {a : EncodedStructure} {i j : ℕ}
    (hi : i < a.2.length) (hj : j < a.2[i].length) :
    (encStructure a)[tableStart a i + 2 * j + 1]? = some a.2[i][j] := by
  rw [Nat.add_assoc, getElem?_encStructure_tableStart_add, flatMap_frame_drop hi,
    List.getElem?_append_left (by simp only [length_frame]; omega),
    getElem?_frame_two_mul_add_one hj, List.getElem?_eq_getElem hj]

/-- The terminator of a table. -/
theorem getElem?_encStructure_tableStart_two_mul_length {a : EncodedStructure} {i : ℕ}
    (hi : i < a.2.length) :
    (encStructure a)[tableStart a i + 2 * a.2[i].length]? = some false := by
  rw [getElem?_encStructure_tableStart_add, flatMap_frame_drop hi,
    List.getElem?_append_left (by simp [length_frame]), getElem?_frame_two_mul_length]

/-- Nothing follows the last table. -/
theorem getElem?_encStructure_tableStart_length_add (a : EncodedStructure) (q : ℕ) :
    (encStructure a)[tableStart a a.2.length + q]? = none := by
  rw [List.getElem?_eq_none]
  rw [length_encStructure]
  omega

/-- There is a bit at the start of every table. -/
theorem getElem?_encStructure_tableStart_isSome {a : EncodedStructure} {i : ℕ}
    (hi : i < a.2.length) : ((encStructure a)[tableStart a i]?).isSome := by
  have h := getElem?_encStructure_tableStart_add a i 0
  rw [Nat.add_zero] at h
  rw [h, flatMap_frame_drop hi, List.getElem?_append_left (by simp [length_frame])]
  simp [length_frame]

end Cslib.Logic
