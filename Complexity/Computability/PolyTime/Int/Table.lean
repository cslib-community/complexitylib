/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger, Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger, Karn Seth, Anton Kovsharov
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Mathlib.Data.List.GetD

/-!
# Polynomial-time lookup and tabulation on rectangular integer row tables

Executable two-dimensional tables of integers with runtime-varying dimensions are represented as
lists of rows `List (List ℤ)` encoded under `encList (encList encIntBin)`. This module provides
shared total entry lookup (`Cslib.rowEntry`, defaulting out-of-bounds indices to `0`), rectangular
`r × c` table construction (`Cslib.tabulateTable`), rectangular shape predicates and extensionality
(`Cslib.IsTableShape`, `Cslib.eq_of_isTableShape_of_rowEntry_eq`), and plain polynomial-time
composition rules (`Cslib.computableInPolyTime_rowEntry`,
`Cslib.computableInPolyTime_tabulateTable`) with dimensions and indices in unary.

## Main definitions

* `Cslib.IsTableShape`: predicate asserting `rows.length = r` and every row of `rows` has length
  `c`.
* `Cslib.rowEntry`: total `(i, j)` entry lookup on `List (List ℤ)` returning `0` when missing.
* `Cslib.tabulateTable`: construct the `r × c` list of rows whose `(i, j)` entry is `g i j`.

## Main results

* `Cslib.isTableShape_tabulateTable`, `Cslib.rowEntry_tabulateTable`,
  `Cslib.rowEntry_tabulateTable_of_lt`: shape and entry lookup of `tabulateTable`.
* `Cslib.exists_rowEntry_eq_of_mem`, `Cslib.exists_rowEntry_eq`, `Cslib.rowEntry_rel_of_mem`:
  correspondence between stored list elements and indexed `rowEntry` values.
* `Cslib.eq_of_isTableShape_of_rowEntry_eq`, `Cslib.tabulateTable_rowEntry`: extensionality and
  re-tabulation on `(r, c)`-shaped tables.
* `Cslib.computableInPolyTime_rowEntry`, `Cslib.computableInPolyTime_tabulateTable`: plain
  `@[fun_prop]` polynomial-time certificates over unary indices/dimensions and `encIntBin` entries.
-/

@[expose] public section

namespace Cslib

/-! ### Shape, lookup, and rectangular tabulation -/

/-- Shape predicate for a dense `r × c` integer table: `r` rows, each of length `c`. -/
def IsTableShape (r c : ℕ) (rows : List (List ℤ)) : Prop :=
  rows.length = r ∧ ∀ row ∈ rows, row.length = c

/-- Entry `(i, j)` of a table stored as a list of integer rows; missing entries read as `0`. -/
def rowEntry (rows : List (List ℤ)) (i j : ℕ) : ℤ :=
  (rows.getD i []).getD j 0

/-- Construct the `r × c` list of rows whose `(i, j)` entry is `g i j` for `i < r` and `j < c`. -/
def tabulateTable (r c : ℕ) (g : ℕ → ℕ → ℤ) : List (List ℤ) :=
  (List.range r).map fun i => (List.range c).map fun j => g i j

/-- Tabulating an `r × c` table produces `r` rows. -/
@[simp]
lemma length_tabulateTable (r c : ℕ) (g : ℕ → ℕ → ℤ) :
    (tabulateTable r c g).length = r := by
  simp [tabulateTable]

/-- Every row in `tabulateTable r c g` has length `c`. -/
lemma length_of_mem_tabulateTable {r c : ℕ} {g : ℕ → ℕ → ℤ} {row : List ℤ}
    (hrow : row ∈ tabulateTable r c g) : row.length = c := by
  obtain ⟨_, -, rfl⟩ := List.mem_map.mp hrow
  simp

/-- Every tabulated `r × c` table has shape `(r, c)`. -/
theorem isTableShape_tabulateTable (r c : ℕ) (g : ℕ → ℕ → ℤ) :
    IsTableShape r c (tabulateTable r c g) :=
  ⟨length_tabulateTable r c g, fun _ hrow => length_of_mem_tabulateTable hrow⟩

/-- Looking up entry `(i, j)` of `tabulateTable r c g` returns `g i j` when `i < r` and `j < c`,
and `0` otherwise. -/
lemma rowEntry_tabulateTable (r c : ℕ) (g : ℕ → ℕ → ℤ) (i j : ℕ) :
    rowEntry (tabulateTable r c g) i j = if i < r ∧ j < c then g i j else 0 := by
  by_cases hi : i < r <;> by_cases hj : j < c <;>
    simp [rowEntry, tabulateTable, List.getD_eq_getElem?_getD, hi, hj]

/-- In-bounds lookup on `tabulateTable r c g` returns `g i j`. -/
lemma rowEntry_tabulateTable_of_lt {r c : ℕ} (g : ℕ → ℕ → ℤ) {i j : ℕ}
    (hi : i < r) (hj : j < c) :
    rowEntry (tabulateTable r c g) i j = g i j := by
  rw [rowEntry_tabulateTable, ite_eq_left ⟨hi, hj⟩]

/-- Outside `i < r ∧ j < c`, an `(r, c)`-shaped table reads as `0`. -/
lemma rowEntry_eq_zero_of_isTableShape {r c : ℕ} {rows : List (List ℤ)}
    (hrows : IsTableShape r c rows) {i j : ℕ} (h : ¬(i < r ∧ j < c)) :
    rowEntry rows i j = 0 := by
  unfold rowEntry
  rcases Nat.lt_or_ge i rows.length with hi | hi
  · rw [List.getD_eq_getElem _ _ hi]
    have hir : i < r := hrows.1 ▸ hi
    have hlen : rows[i].length = c := hrows.2 _ (List.getElem_mem hi)
    have hj : rows[i].length ≤ j := by omega
    exact List.getD_eq_default _ _ hj
  · rw [List.getD_eq_default _ _ hi, List.getD_nil]

/-- Every stored entry of a list of rows occurs as `rowEntry rows i j` at valid in-bounds
indices. -/
lemma exists_rowEntry_eq_of_mem {rows : List (List ℤ)} {row : List ℤ} {z : ℤ}
    (hrow : row ∈ rows) (hz : z ∈ row) :
    ∃ i j, i < rows.length ∧ j < row.length ∧ rowEntry rows i j = z := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hrow
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hz
  exact ⟨i, j, hi, hj, by simp [rowEntry, List.getD_eq_getElem?_getD, hi, hj]⟩

/-- Every stored entry of a list of rows is one of its indexed entries. -/
lemma exists_rowEntry_eq {rows : List (List ℤ)} {row : List ℤ} {z : ℤ}
    (hrow : row ∈ rows) (hz : z ∈ row) : ∃ i j, rowEntry rows i j = z := by
  obtain ⟨i, j, -, -, h⟩ := exists_rowEntry_eq_of_mem hrow hz
  exact ⟨i, j, h⟩

/-- Any predicate holding for `0` and for every stored entry holds for every `rowEntry`. -/
lemma rowEntry_rel_of_mem {P : ℤ → Prop} (h0 : P 0) {rows : List (List ℤ)}
    (h : ∀ row ∈ rows, ∀ z ∈ row, P z) (i j : ℕ) : P (rowEntry rows i j) := by
  unfold rowEntry
  rcases Nat.lt_or_ge i rows.length with hi | hi
  · rw [List.getD_eq_getElem _ _ hi]
    rcases Nat.lt_or_ge j rows[i].length with hj | hj
    · rw [List.getD_eq_getElem _ _ hj]
      exact h _ (List.getElem_mem hi) _ (List.getElem_mem hj)
    · rw [List.getD_eq_default _ _ hj]
      exact h0
  · rw [List.getD_eq_default _ _ hi, List.getD_nil]
    exact h0

/-- Two `(r, c)`-shaped tables are equal when their in-bounds entries agree. -/
theorem eq_of_isTableShape_of_rowEntry_eq {r c : ℕ} {A B : List (List ℤ)}
    (hA : IsTableShape r c A) (hB : IsTableShape r c B)
    (h : ∀ i < r, ∀ j < c, rowEntry A i j = rowEntry B i j) : A = B := by
  apply List.ext_getElem (hA.1.trans hB.1.symm)
  intro i hiA hiB
  have hi : i < r := hA.1 ▸ hiA
  have hlenA : A[i].length = c := hA.2 _ (List.getElem_mem hiA)
  have hlenB : B[i].length = c := hB.2 _ (List.getElem_mem hiB)
  apply List.ext_getElem (hlenA.trans hlenB.symm)
  intro j hjA hjB
  have hj : j < c := hlenA ▸ hjA
  have hij := h i hi j hj
  simpa only [rowEntry, List.getD_eq_getElem _ _ hiA, List.getD_eq_getElem _ _ hiB,
    List.getD_eq_getElem _ _ hjA, List.getD_eq_getElem _ _ hjB] using hij

/-- Re-tabulating an `(r, c)`-shaped table from `rowEntry` recovers it unchanged. -/
lemma tabulateTable_rowEntry {r c : ℕ} {rows : List (List ℤ)} (hrows : IsTableShape r c rows) :
    tabulateTable r c (rowEntry rows) = rows :=
  eq_of_isTableShape_of_rowEntry_eq (isTableShape_tabulateTable r c _) hrows fun _ hi _ hj =>
    rowEntry_tabulateTable_of_lt _ hi hj

/-! ### Plain polynomial-time certificates -/

section PolyTime

open Turing MultiTapeTM

variable {α : Type} {encIn : α ↪ List Bool}

/-- Entry lookup `rowEntry` on a list of integer rows is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_rowEntry {rows : α → List (List ℤ)} {i j : α → ℕ}
    (hrows : ComputableInPolyTime rows encIn (encList (encList encIntBin)))
    (hi : ComputableInPolyTime i encIn encUnary)
    (hj : ComputableInPolyTime j encIn encUnary) :
    ComputableInPolyTime (fun x => rowEntry (rows x) (i x) (j x)) encIn encIntBin :=
  ((ComputableInPolyTime.listGetD (encA := encIntBin) 0).comp
    (((ComputableInPolyTime.listGetD (encA := encList encIntBin) []).comp
      (hrows.prod hi)).prod hj))

/-- Tabulating an `r × c` table of binary integers from unary dimensions `(r, c)` is computable
in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_tabulateTable {r c : α → ℕ} {g : α → ℕ → ℕ → ℤ}
    (hr : ComputableInPolyTime r encIn encUnary)
    (hc : ComputableInPolyTime c encIn encUnary)
    (hg : ComputableInPolyTime (fun p : (α × ℕ) × ℕ => g p.1.1 p.1.2 p.2)
      (encPair (encPair encIn encUnary) encUnary) encIntBin) :
    ComputableInPolyTime (fun x => tabulateTable (r x) (c x) (g x))
      encIn (encList (encList encIntBin)) :=
  ComputableInPolyTime.mapWithInput
    (ComputableInPolyTime.range.comp hr)
    (ComputableInPolyTime.mapWithInput
      (ComputableInPolyTime.range.comp
        (hc.comp (ComputableInPolyTime.fst encIn encUnary))) hg)

end PolyTime

end Cslib
