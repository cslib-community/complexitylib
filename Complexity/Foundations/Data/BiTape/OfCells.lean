/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.BiTape

/-!
# Tapes holding a finite list of cells

`Cslib.Turing.BiTape.ofCells cells pos` is the tape that holds the list `cells` of optional
symbols, blanks allowed anywhere, with its head on cell `pos`: cell `i` of the list is at
displacement `i - pos` from the head and every other cell is blank
(`Cslib.Turing.BiTape.read_ofCells`). It loads a finite window of a tape, such as the blocks
around a head, into finite storage.

## Main definitions

* `Cslib.Turing.BiTape.ofCells`: the tape holding a list of cells.

## Main results

* `Cslib.Turing.StackTape.read_ofList`: a stack tape built from a list reads the list.
* `Cslib.Turing.BiTape.read_ofCells`: the cells of the tape.
-/

public section

namespace Cslib.Turing

namespace StackTape

variable {Symbol : Type*}

/-- A stack tape built from a list reads the list, and blank past its end. -/
@[simp] lemma read_ofList (l : List (Option Symbol)) (position : ℕ) :
    (ofList l).read position = l.getD position none := by
  induction l generalizing position with
  | nil => simp
  | cons a l ih =>
    cases position with
    | zero => simp [head_cons]
    | succ position => simp [tail_cons, ih]

end StackTape

namespace BiTape

variable {Symbol : Type*}

/-- The tape holding `cells` with its head on cell `pos`: cell `i` of `cells` is at displacement
`i - pos` from the head, and every other cell is blank. -/
@[expose] def ofCells (cells : List (Option Symbol)) (pos : ℕ) : BiTape Symbol :=
  ⟨cells.getD pos none,
    StackTape.ofList ((List.range pos).map fun i => cells.getD (pos - 1 - i) none),
    StackTape.ofList (cells.drop (pos + 1))⟩

/-- **The cells of `ofCells cells pos`**: the cell at displacement `z` is cell `pos + z` of
`cells`, blank when that is negative or past the end. -/
lemma read_ofCells (cells : List (Option Symbol)) (pos : ℕ) (z : ℤ) :
    (ofCells cells pos).read z =
      if 0 ≤ (pos : ℤ) + z then cells.getD ((pos : ℤ) + z).toNat none else none := by
  rcases z with (_ | n) | n
  · simp [read, ofCells]
  · have h : ((pos : ℤ) + Int.ofNat (n + 1)).toNat = pos + 1 + n := by
      simp only [Int.ofNat_eq_natCast]
      omega
    have h0 : 0 ≤ (pos : ℤ) + Int.ofNat (n + 1) := by
      simp only [Int.ofNat_eq_natCast]
      omega
    simp only [h0, ↓reduceIte, h]
    simp [read, ofCells, List.getD_eq_getElem?_getD, List.getElem?_drop]
  · simp only [read, ofCells, StackTape.read_ofList, List.getD_eq_getElem?_getD,
      List.getElem?_map]
    by_cases hn : n < pos
    · have h : ((pos : ℤ) + Int.negSucc n).toNat = pos - 1 - n := by
        simp only [Int.negSucc_eq]
        omega
      have h0 : 0 ≤ (pos : ℤ) + Int.negSucc n := by
        simp only [Int.negSucc_eq]
        omega
      simp only [h0, ↓reduceIte, h, List.getElem?_range hn]
      rfl
    · have h0 : ¬ 0 ≤ (pos : ℤ) + Int.negSucc n := by
        simp only [Int.negSucc_eq]
        omega
      simp only [h0, ↓reduceIte,
        List.getElem?_eq_none (by simpa using hn : (List.range pos).length ≤ n)]
      rfl

end BiTape

end Cslib.Turing
