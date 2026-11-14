/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.PolyTime.Int.Table
public import CslibFrontier.Foundations.LinearAlgebra.Matrix.Bareiss
public import CslibFrontier.Foundations.Data.Nat.BinarySize
public import CslibFrontier.Foundations.Data.Rat.Basic
import CslibFrontier.Foundations.Data.List.Lookup
import Mathlib.Data.List.GetD
import Mathlib.Data.List.NodupEquivFin
import Mathlib.LinearAlgebra.Matrix.Diagonal
import Mathlib.Logic.Equiv.Fintype

/-!
# Executable Bareiss–Jordan elimination over `ℚ` and coefficient bit-length bounds

This module provides executable list-matrix Bareiss–Jordan elimination over `ℤ` and `ℚ`, proved
equivalent to the minor-scaled Bareiss–Jordan matrix `Matrix.bareissMatrix` from
`CslibFrontier.Foundations.LinearAlgebra.Matrix.Bareiss`.

## References and local adaptations

* Alexander Schrijver, *Theory of Linear and Integer Programming* (Wiley, 1986), Section 3.2,
  Theorem 3.2 (pp. 29–30, determinant encoding-size bound) and Section 3.3, Theorem 3.3
  (pp. 32–33), Corollary 3.3a (pp. 33–34), and the Gauss–Jordan discussion with Equations
  (28)–(30) (p. 35).
* **Local adaptation:** Whereas Schrijver's Section 3.3 analyzes normalized rational Gaussian and
  Gauss–Jordan elimination directly over `ℚ`, this module clears row denominators upfront
  (`clearDenoms`) and runs fraction-free Sylvester–Bareiss minor-scaled Gauss–Jordan updates over
  `ℤ` (`bareissElimCols`), bounding all intermediate integer entries and output numerators and
  denominators via the explicit Hadamard/factorial bound `stageEntryBound`.

## Main definitions

* `IntTable`, `RatTable`, `BareissState`, `RationalElimResult`, `LinearSystemInput`,
  `LinearSolveResult`: explicit row-major matrix and elimination records.
* `clearDenoms`: clears row denominators of a `RatTable` to produce an exact `IntTable`.
* `bareissStep`, `bareissElimCols`, `bareissElim`: column-by-column fraction-free Bareiss–Jordan
  integer elimination.
* `rationalElim`, `ratRref`, `ratRank`, `ratRowBasis`, `ratKernelBasis`, `ratSolve`: rational
  reduced row echelon form, exact rank, linearly independent row and kernel bases, and canonical
  linear system solving with certified inconsistency.
* `stageEntryBound`: uniform Hadamard/factorial bound on intermediate integer entries and output
  rational numerators and denominators.

## Main results

* `bareissElimCols_inv`: loop invariant equating executable `Int.ediv` updates with
  `Matrix.bareissMatrix` and certifying exact divisibility, echelon zeroes, and pivot determinants.
* `rationalElim_spec`, `ratRref_isReducedRowEchelon`, `ratRank_eq`: `rationalElim` produces a
  genuine `Matrix.IsPivotedBy` / `Matrix.IsReducedRowEchelon` matrix over `ℚ` preserving row space
  and rank, with linearly independent spanning row and kernel bases.
* `ratSolve_spec`: `ratSolve` returns a canonical solution vector iff `A *ᵥ x = b` is consistent.
* `bareissInv_entry_bound`, `size_stageEntryBound_le`, `rationalElim_entry_bounds`,
  `ratSolve_entry_bounds`: polynomial Hadamard/factorial entry magnitude and `Nat.size`
  bit-length bounds for all intermediate states and rational outputs.
-/

public section

namespace Cslib.LinearAlgebra

open Finset Submodule Matrix
open scoped Matrix BigOperators

/-! ### Explicit table and elimination record types -/

/-- Explicit row-major integer matrix. -/
structure IntTable where
  /-- Number of rows. -/
  numRows : ℕ
  /-- Number of columns. -/
  numCols : ℕ
  /-- Row-major integer entries. -/
  rows : List (List ℤ)
  deriving Repr

/-- Explicit row-major rational matrix. -/
structure RatTable where
  /-- Number of rows. -/
  numRows : ℕ
  /-- Number of columns. -/
  numCols : ℕ
  /-- Row-major rational entries. -/
  rows : List (List ℚ)
  deriving Repr

/-- Intermediate state of column-by-column Bareiss–Jordan integer elimination. -/
structure BareissState where
  /-- Current minor-scaled integer table. -/
  table : IntTable
  /-- Current nonzero pivot determinant (`1` initially). -/
  pivotDet : ℤ
  /-- Ordered distinct pivot row indices selected so far. -/
  pivotRows : List ℕ
  /-- Strictly increasing pivot column indices selected so far. -/
  pivotCols : List ℕ
  deriving Repr

/-- Complete output of Bareiss–Jordan elimination on a rational matrix. -/
structure RationalElimResult where
  /-- Reduced row echelon rational matrix of the same shape, pivot rows first. -/
  rref : RatTable
  /-- Exact rank (`= pivotRows.length = pivotCols.length`). -/
  rank : ℕ
  /-- Pivot row indices in the original matrix forming a basis of the row space. -/
  pivotRows : List ℕ
  /-- Strictly increasing pivot column indices. -/
  pivotCols : List ℕ
  /-- Non-pivot column indices in ascending order. -/
  nonPivotCols : List ℕ
  /-- Kernel basis vectors, one per non-pivot column. -/
  kernelBasis : List (List ℚ)
  deriving Repr

/-- Input linear system `A x = b` over `ℚ`. -/
structure LinearSystemInput where
  /-- Coefficient matrix `A`. -/
  matrix : RatTable
  /-- Right-hand side vector `b`. -/
  rhs : List ℚ
  deriving Repr

/-- Output of Bareiss–Jordan linear solving for `A x = b`. -/
structure LinearSolveResult where
  /-- Canonical solution vector supported on pivot columns if consistent, or `none`. -/
  solution : Option (List ℚ)
  /-- Pivot row indices selected during elimination. -/
  pivotRows : List ℕ
  /-- Pivot column indices selected during elimination. -/
  pivotCols : List ℕ
  deriving Repr

deriving instance DecidableEq for IntTable, RatTable, BareissState, RationalElimResult,
  LinearSystemInput, LinearSolveResult

/-! ### Table indexing, well-formedness, and `Matrix` bridges -/

/-- Entry `(i, j)` of an `IntTable`, defaulting to `0` out of bounds. -/
@[expose] def IntTable.entry (T : IntTable) (i j : ℕ) : ℤ :=
  Cslib.rowEntry T.rows i j

/-- Entry `(i, j)` of a `RatTable`, defaulting to `0` out of bounds. -/
@[expose] def RatTable.entry (M : RatTable) (i j : ℕ) : ℚ :=
  (M.rows.getD i []).getD j 0

/-- Rectangular shape invariant for `IntTable`. -/
@[expose] def IntTable.WellFormed (T : IntTable) : Prop :=
  Cslib.IsTableShape T.numRows T.numCols T.rows

/-- Rectangular shape invariant for `RatTable`. -/
@[expose] def RatTable.WellFormed (M : RatTable) : Prop :=
  M.rows.length = M.numRows ∧ ∀ r ∈ M.rows, r.length = M.numCols

/-- Interpret an `IntTable` as a `Matrix (Fin T.numRows) (Fin T.numCols) ℤ`. -/
@[expose] def IntTable.toMatrix (T : IntTable) : Matrix (Fin T.numRows) (Fin T.numCols) ℤ :=
  Matrix.of fun i j => T.entry i.val j.val

/-- Interpret a `RatTable` as a `Matrix (Fin M.numRows) (Fin M.numCols) ℚ`. -/
@[expose] def RatTable.toMatrix (M : RatTable) : Matrix (Fin M.numRows) (Fin M.numCols) ℚ :=
  Matrix.of fun i j => M.entry i.val j.val

@[simp]
theorem IntTable.toMatrix_apply (T : IntTable) (i : Fin T.numRows) (j : Fin T.numCols) :
    T.toMatrix i j = T.entry i.val j.val := rfl

@[simp]
theorem RatTable.toMatrix_apply (M : RatTable) (i : Fin M.numRows) (j : Fin M.numCols) :
    M.toMatrix i j = M.entry i.val j.val := rfl

/-! ### Row denominator clearing -/

/-- Product of denominators of all entries in a rational row. -/
@[expose] def rowDenomProd (r : List ℚ) : ℕ :=
  r.foldl (fun acc q => acc * q.den) 1

/-- Scale a rational row by `rowDenomProd r`, producing an exact integer row. -/
@[expose] def clearRow (r : List ℚ) : List ℤ :=
  let d := rowDenomProd r
  r.map fun q => q.num * Int.ofNat (d / q.den)

/-- Normalized rational row extracted at row index `i` of length `M.numCols`. -/
@[expose] def normalizedRatRow (M : RatTable) (i : ℕ) : List ℚ :=
  (List.range M.numCols).map fun j => M.entry i j

/-- Normalize and clear row denominators of a `RatTable`, unconditionally producing a well-formed
`IntTable` of identical dimensions. -/
@[expose] def clearDenoms (M : RatTable) : IntTable :=
  ⟨M.numRows, M.numCols, (List.range M.numRows).map fun i => clearRow (normalizedRatRow M i)⟩

/-- Per-row positive integer multiplier produced by `clearDenoms M`. -/
def rowMultiplier (M : RatTable) (i : Fin M.numRows) : ℕ :=
  rowDenomProd (normalizedRatRow M i.val)

private theorem foldl_mul_den_pos (r : List ℚ) :
    ∀ acc : ℕ, 0 < acc → 0 < r.foldl (fun a q => a * q.den) acc := by
  induction r with
  | nil => intro acc h; exact h
  | cons q qs ih =>
    intro acc h
    exact ih (acc * q.den) (Nat.mul_pos h q.den_nz.bot_lt)

theorem rowDenomProd_pos (r : List ℚ) : 0 < rowDenomProd r :=
  foldl_mul_den_pos r 1 Nat.one_pos

private theorem foldl_dvd_left (r : List ℚ) :
    ∀ acc : ℕ, acc ∣ r.foldl (fun a q => a * q.den) acc := by
  induction r with
  | nil => intro acc; exact dvd_refl acc
  | cons q qs ih =>
    intro acc
    exact (Nat.dvd_mul_right acc q.den).trans (ih (acc * q.den))

private theorem mem_den_dvd_foldl (r : List ℚ) {q : ℚ} (hq : q ∈ r) :
    ∀ acc : ℕ, q.den ∣ r.foldl (fun a x => a * x.den) acc := by
  induction r with
  | nil => cases hq
  | cons x xs ih =>
    intro acc
    rcases List.mem_cons.mp hq with rfl | hxs
    · exact (Nat.dvd_mul_left q.den acc).trans (foldl_dvd_left xs (acc * q.den))
    · exact ih hxs (acc * x.den)

theorem den_dvd_rowDenomProd {r : List ℚ} {q : ℚ} (hq : q ∈ r) :
    q.den ∣ rowDenomProd r :=
  mem_den_dvd_foldl r hq 1

theorem cast_clearRow_mem {r : List ℚ} {q : ℚ} (hq : q ∈ r) :
    ((q.num * Int.ofNat (rowDenomProd r / q.den) : ℤ) : ℚ) = (rowDenomProd r : ℚ) * q := by
  have hdvd : q.den ∣ rowDenomProd r := den_dvd_rowDenomProd hq
  have hden : (q.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.den_nz
  have hmul : (rowDenomProd r : ℚ) = ((rowDenomProd r / q.den : ℕ) : ℚ) * (q.den : ℚ) := by
    exact_mod_cast (Nat.div_mul_cancel hdvd).symm
  calc ((q.num * Int.ofNat (rowDenomProd r / q.den) : ℤ) : ℚ)
      = (q.num : ℚ) * ((rowDenomProd r / q.den : ℕ) : ℚ) := by push_cast; rfl
    _ = ((rowDenomProd r / q.den : ℕ) : ℚ) * (q.den : ℚ) * ((q.num : ℚ) / (q.den : ℚ)) := by
        field_simp [hden]
    _ = (rowDenomProd r : ℚ) * q := by
        rw [← hmul, Rat.num_div_den]

theorem clearDenoms_wellFormed (M : RatTable) : (clearDenoms M).WellFormed := by
  refine ⟨?_, ?_⟩
  · simp only [clearDenoms, List.length_map, List.length_range]
  · intro r hr
    simp only [clearDenoms, List.mem_map, List.mem_range] at hr
    obtain ⟨i, _, rfl⟩ := hr
    simp only [clearRow, normalizedRatRow, List.length_map, List.length_range]
    rfl

theorem rowMultiplier_pos (M : RatTable) (i : Fin M.numRows) : 0 < rowMultiplier M i :=
  rowDenomProd_pos _

private theorem clearDenoms_entry_eq (M : RatTable) (i : Fin M.numRows) (j : Fin M.numCols) :
    (clearDenoms M).toMatrix i j =
      (M.toMatrix i j).num * Int.ofNat (rowMultiplier M i / (M.toMatrix i j).den) := by
  simp only [IntTable.toMatrix_apply, RatTable.toMatrix_apply, IntTable.entry, Cslib.rowEntry,
    clearDenoms]
  rw [List.getD_map_range _ [] i.isLt]
  simp only [clearRow, normalizedRatRow, List.map_map, Function.comp_def]
  exact List.getD_map_range _ 0 j.isLt

theorem clearDenoms_toMatrix_apply (M : RatTable) (i : Fin M.numRows) (j : Fin M.numCols) :
    ((clearDenoms M).toMatrix i j : ℚ) = (rowMultiplier M i : ℚ) * M.toMatrix i j := by
  rw [clearDenoms_entry_eq M i j]
  have hmem : M.toMatrix i j ∈ normalizedRatRow M i.val := by
    simp only [normalizedRatRow, List.mem_map, List.mem_range]
    exact ⟨j.val, j.isLt, rfl⟩
  exact cast_clearRow_mem hmem

private theorem foldl_mul_den_le_pow (r : List ℚ) {b : ℕ}
    (hb : ∀ q ∈ r, q.den ≤ 2 ^ b) :
    ∀ acc : ℕ, r.foldl (fun a q => a * q.den) acc ≤ acc * 2 ^ (r.length * b) := by
  induction r with
  | nil => intro acc; simp only [List.foldl_nil, List.length_nil, zero_mul, pow_zero, mul_one,
      le_refl]
  | cons q qs ih =>
    intro acc
    have hq : q.den ≤ 2 ^ b := hb q List.mem_cons_self
    have hqs : ∀ x ∈ qs, x.den ≤ 2 ^ b := fun x hx => hb x (List.mem_cons_of_mem q hx)
    refine (ih hqs (acc * q.den)).trans ?_
    calc acc * q.den * 2 ^ (qs.length * b)
        ≤ acc * 2 ^ b * 2 ^ (qs.length * b) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left acc hq)
      _ = acc * 2 ^ ((qs.length + 1) * b) := by
          rw [Nat.add_mul, Nat.one_mul, Nat.pow_add, mul_assoc, mul_comm (2 ^ (qs.length * b))]

theorem rowDenomProd_le_pow {r : List ℚ} {b : ℕ} (hb : ∀ q ∈ r, q.den ≤ 2 ^ b) :
    rowDenomProd r ≤ 2 ^ (r.length * b) := by
  unfold rowDenomProd
  simpa only [one_mul] using foldl_mul_den_le_pow r hb 1

theorem clearDenoms_abs_le (M : RatTable) {b : ℕ}
    (hb : ∀ i : Fin M.numRows, ∀ j : Fin M.numCols,
      (M.toMatrix i j).num.natAbs ≤ 2 ^ b ∧ (M.toMatrix i j).den ≤ 2 ^ b)
    (i : Fin M.numRows) (j : Fin M.numCols) :
    |(clearDenoms M).toMatrix i j| ≤ ((2 ^ ((M.numCols + 1) * b) : ℕ) : ℤ) := by
  rw [← Int.natCast_natAbs, Int.ofNat_le, clearDenoms_entry_eq M i j, Int.natAbs_mul]
  change (M.toMatrix i j).num.natAbs * (rowMultiplier M i / (M.toMatrix i j).den) ≤ _
  have hden : ∀ q ∈ normalizedRatRow M i.val, q.den ≤ 2 ^ b := by
    intro q hq
    simp only [normalizedRatRow, List.mem_map, List.mem_range] at hq
    obtain ⟨c, hc, rfl⟩ := hq
    exact (hb i ⟨c, hc⟩).2
  have hprod : rowMultiplier M i ≤ 2 ^ (M.numCols * b) := by
    simpa only [rowMultiplier, normalizedRatRow, List.length_map, List.length_range] using
      rowDenomProd_le_pow hden
  have hq : (M.toMatrix i j).num.natAbs ≤ 2 ^ b := (hb i j).1
  have hdiv : rowMultiplier M i / (M.toMatrix i j).den ≤ rowMultiplier M i := Nat.div_le_self _ _
  calc (M.toMatrix i j).num.natAbs * (rowMultiplier M i / (M.toMatrix i j).den)
      ≤ 2 ^ b * rowMultiplier M i := Nat.mul_le_mul hq hdiv
    _ ≤ 2 ^ b * 2 ^ (M.numCols * b) := Nat.mul_le_mul_left _ hprod
    _ = 2 ^ ((M.numCols + 1) * b) := by
        rw [Nat.add_mul, Nat.one_mul, Nat.pow_add, mul_comm]

/-! ### Executable Bareiss–Jordan elimination over `ℤ` -/

/-- Find the first unpivoted row index `< st.table.numRows` with a nonzero entry in column `c`. -/
@[expose] def findPivotRow (st : BareissState) (c : ℕ) : Option ℕ :=
  (List.range st.table.numRows).find? fun r =>
    !st.pivotRows.contains r && decide (st.table.entry r c ≠ 0)

/-- Perform one column step of Bareiss–Jordan elimination on column `c`. -/
@[expose] def bareissStep (st : BareissState) (c : ℕ) : BareissState :=
  match findPivotRow st c with
  | none => st
  | some p =>
    let pivVal := st.table.entry p c
    let prevDet := st.pivotDet
    let m := st.table.numRows
    let n := st.table.numCols
    let nextRows : List (List ℤ) :=
      Cslib.tabulateTable m n fun i j =>
        if i = p then st.table.entry p j
        else
          (pivVal * st.table.entry i j - st.table.entry i c * st.table.entry p j) / prevDet
    { table := ⟨m, n, nextRows⟩
      pivotDet := pivVal
      pivotRows := st.pivotRows ++ [p]
      pivotCols := st.pivotCols ++ [c] }

/-- Initial state of Bareiss–Jordan elimination on an integer table. -/
@[expose] def bareissInit (T : IntTable) : BareissState :=
  ⟨T, 1, [], []⟩

/-- Run Bareiss–Jordan elimination across columns `0, …, colLimit - 1`. -/
@[expose] def bareissElimCols (T : IntTable) (colLimit : ℕ) : BareissState :=
  (List.range colLimit).foldl bareissStep (bareissInit T)

/-- Run full Bareiss–Jordan elimination across all columns of `T`. -/
@[expose] def bareissElim (T : IntTable) : BareissState :=
  bareissElimCols T T.numCols

/-- Map a bounded list of row or column indices to `Fin k → Fin m`. -/
def finSel {m k : ℕ} (idxs : List ℕ) (hk : k = idxs.length) (hidxs : ∀ i ∈ idxs, i < m) :
    Fin k → Fin m :=
  fun a => ⟨idxs[a.val]'(hk ▸ a.isLt), hidxs _ (List.getElem_mem _)⟩

private theorem finSel_snoc {m k : ℕ} (idxs : List ℕ) (hk : k = idxs.length) (x : ℕ)
    (hx : x < m) (hidxs : ∀ i ∈ idxs, i < m) (hx' : ∀ i ∈ idxs ++ [x], i < m)
    {hk' : k + 1 = (idxs ++ [x]).length} :
    finSel (idxs ++ [x]) hk' hx' = Fin.snoc (finSel idxs hk hidxs) (⟨x, hx⟩ : Fin m) := by
  subst hk
  ext a
  by_cases ha : a.val < idxs.length
  · have ha' : a = Fin.castSucc ⟨a.val, ha⟩ := rfl
    rw [ha', Fin.snoc_castSucc]
    exact List.getElem_append_left ha
  · have ha' : a = Fin.last idxs.length :=
      Fin.ext (by have := a.isLt; rw [Fin.val_last]; omega)
    rw [ha', Fin.snoc_last]
    have hlen : idxs.length ≤ (Fin.last idxs.length : Fin (idxs.length + 1)).val := by
      rw [Fin.val_last]
    dsimp only [finSel]
    rw [List.getElem_append_right hlen]
    simp only [Fin.val_last, Nat.sub_self, List.getElem_singleton]

private theorem pairwise_lt_strictMono {n k : ℕ} {cols : List ℕ} (hk : k = cols.length)
    (hpw : cols.Pairwise (· < ·)) (hcols : ∀ c ∈ cols, c < n) :
    StrictMono (finSel cols hk hcols) := by
  intro a b hab
  change cols[a.val] < cols[b.val]
  exact (List.pairwise_iff_getElem.mp hpw) a.val b.val (hk ▸ a.isLt) (hk ▸ b.isLt) hab

/-- Loop invariant linking `BareissState` to `Matrix.bareissMatrix`. -/
structure BareissInv (T : IntTable) (stepCols : ℕ) (st : BareissState) : Prop where
  wellFormed : st.table.WellFormed
  dims : st.table.numRows = T.numRows ∧ st.table.numCols = T.numCols
  len_eq : st.pivotRows.length = st.pivotCols.length
  row_lt : ∀ r ∈ st.pivotRows, r < T.numRows
  col_lt : ∀ c ∈ st.pivotCols, c < stepCols
  col_dim : ∀ c ∈ st.pivotCols, c < T.numCols
  row_nodup : st.pivotRows.Nodup
  col_strict : st.pivotCols.Pairwise (· < ·)
  pivotDet_ne_zero : st.pivotDet ≠ 0
  pivotDet_eq :
    st.pivotDet = Matrix.pivotDet T.toMatrix
      (finSel st.pivotRows rfl row_lt) (finSel st.pivotCols len_eq col_dim)
  table_eq :
    ∀ (i : Fin T.numRows) (j : Fin T.numCols),
      st.table.entry i.val j.val =
        Matrix.bareissMatrix T.toMatrix
          (finSel st.pivotRows rfl row_lt) (finSel st.pivotCols len_eq col_dim) i j
  term_cols :
    ∀ (i : Fin T.numRows), (∀ a, finSel st.pivotRows rfl row_lt a ≠ i) →
      ∀ (j : Fin T.numCols), j.val < stepCols →
        Matrix.bareissMatrix T.toMatrix
          (finSel st.pivotRows rfl row_lt) (finSel st.pivotCols len_eq col_dim) i j = 0
  echelon_zero :
    ∀ (a : Fin st.pivotRows.length) (j : Fin T.numCols),
      j.val < st.pivotCols[a.val]'(len_eq ▸ a.isLt) →
        Matrix.bareissMatrix T.toMatrix
          (finSel st.pivotRows rfl row_lt) (finSel st.pivotCols len_eq col_dim)
          (finSel st.pivotRows rfl row_lt a) j = 0

private theorem findPivotRow_none {st : BareissState} {c : ℕ}
    (hnone : findPivotRow st c = none) :
    ∀ r < st.table.numRows, r ∉ st.pivotRows → st.table.entry r c = 0 := by
  intro r hr hnr
  by_contra hnz
  have hmem : r ∈ List.range st.table.numRows := List.mem_range.mpr hr
  have hp := List.find?_eq_none.mp hnone r hmem
  have htrue : (!st.pivotRows.contains r && decide (st.table.entry r c ≠ 0)) = true := by
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not,
      decide_eq_true_eq]
    exact ⟨hnr, hnz⟩
  exact absurd htrue hp

private theorem findPivotRow_some {st : BareissState} {c p : ℕ}
    (hsome : findPivotRow st c = some p) :
    p < st.table.numRows ∧ p ∉ st.pivotRows ∧ st.table.entry p c ≠ 0 := by
  have hmem := List.mem_range.mp (List.mem_of_find?_eq_some hsome)
  have hpred := List.find?_some hsome
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not,
    decide_eq_true_eq] at hpred
  exact ⟨hmem, hpred.1, hpred.2⟩

theorem bareissInv_init {T : IntTable} (hT : T.WellFormed) :
    BareissInv T 0 (bareissInit T) := by
  refine
    { wellFormed := hT
      dims := ⟨rfl, rfl⟩
      len_eq := rfl
      row_lt := fun _ h => nomatch h
      col_lt := fun _ h => nomatch h
      col_dim := fun _ h => nomatch h
      row_nodup := List.nodup_nil
      col_strict := List.Pairwise.nil
      pivotDet_ne_zero := one_ne_zero
      pivotDet_eq := (Matrix.pivotDet_zero T.toMatrix _ _).symm
      table_eq := fun i j => ?_
      term_cols := fun _ _ _ hj => absurd hj (Nat.not_lt_zero _)
      echelon_zero := fun a _ _ => a.elim0 }
  change T.entry i.val j.val = Matrix.bareissMatrix T.toMatrix
    (finSel ([] : List ℕ) rfl _) (finSel ([] : List ℕ) rfl _) i j
  rw [Matrix.bareissMatrix_zero]
  rfl

private theorem bareissMatrix_snoc_congr {R : Type*} [CommRing R] {m n k₁ k₂ : ℕ}
    (A : Matrix (Fin m) (Fin n) R) (S₁ : Fin k₁ → Fin m) (C₁ : Fin k₁ → Fin n)
    (S₂ : Fin k₂ → Fin m) (C₂ : Fin k₂ → Fin n) (hk : k₁ = k₂)
    (hS : S₂ ∘ finCongr hk = S₁) (hC : C₂ ∘ finCongr hk = C₁)
    (i : Fin m) (j : Fin n) :
    Matrix.bareissMatrix A S₁ C₁ i j = Matrix.bareissMatrix A S₂ C₂ i j := by
  subst hk
  simp only [finCongr_refl] at hS hC
  subst hS hC
  rfl

private theorem pivotDet_snoc_congr {R : Type*} [CommRing R] {m n k₁ k₂ : ℕ}
    (A : Matrix (Fin m) (Fin n) R) (S₁ : Fin k₁ → Fin m) (C₁ : Fin k₁ → Fin n)
    (S₂ : Fin k₂ → Fin m) (C₂ : Fin k₂ → Fin n) (hk : k₁ = k₂)
    (hS : S₂ ∘ finCongr hk = S₁) (hC : C₂ ∘ finCongr hk = C₁) :
    Matrix.pivotDet A S₁ C₁ = Matrix.pivotDet A S₂ C₂ := by
  subst hk
  simp only [finCongr_refl] at hS hC
  subst hS hC
  rfl

theorem bareissInv_step {T : IntTable} {c : ℕ} (hc : c < T.numCols) {st : BareissState}
    (hinv : BareissInv T c st) : BareissInv T (c + 1) (bareissStep st c) := by
  by_cases hfind : findPivotRow st c = none
  · have hstep : bareissStep st c = st := by simp only [bareissStep, hfind]
    rw [hstep]
    have hnone := findPivotRow_none hfind
    refine
      { wellFormed := hinv.wellFormed
        dims := hinv.dims
        len_eq := hinv.len_eq
        row_lt := hinv.row_lt
        col_lt := fun x hx => (hinv.col_lt x hx).trans (Nat.lt_succ_self c)
        col_dim := hinv.col_dim
        row_nodup := hinv.row_nodup
        col_strict := hinv.col_strict
        pivotDet_ne_zero := hinv.pivotDet_ne_zero
        pivotDet_eq := hinv.pivotDet_eq
        table_eq := hinv.table_eq
        term_cols := fun i hi j hj => ?_
        echelon_zero := fun a j hj => hinv.echelon_zero a j hj }
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hjlt | hjeq
    · exact hinv.term_cols i hi j hjlt
    · have hjc : j = ⟨c, hc⟩ := Fin.ext hjeq
      subst hjc
      rw [← hinv.table_eq i ⟨c, hc⟩]
      refine hnone i.val (hinv.dims.1.symm ▸ i.isLt) fun hmem => ?_
      obtain ⟨idx, hidx, hval⟩ := List.mem_iff_getElem.mp hmem
      exact hi ⟨idx, hidx⟩ (Fin.ext hval)
  · obtain ⟨p, hpfind⟩ := Option.ne_none_iff_exists'.mp hfind
    have ⟨hp_lt, hp_notMem, hp_nz⟩ := findPivotRow_some hpfind
    have hp_m : p < T.numRows := hinv.dims.1 ▸ hp_lt
    have hp_fin : ∀ a, finSel st.pivotRows rfl hinv.row_lt a ≠ ⟨p, hp_m⟩ := by
      intro a ha
      apply hp_notMem
      have hp_eq : st.pivotRows[a.val] = p := congrArg Fin.val ha
      rw [← hp_eq]
      exact List.getElem_mem _
    have hstep : bareissStep st c =
        { table := ⟨st.table.numRows, st.table.numCols,
            Cslib.tabulateTable st.table.numRows st.table.numCols fun i j =>
              if i = p then st.table.entry p j
              else (st.table.entry p c * st.table.entry i j -
                st.table.entry i c * st.table.entry p j) / st.pivotDet⟩
          pivotDet := st.table.entry p c
          pivotRows := st.pivotRows ++ [p]
          pivotCols := st.pivotCols ++ [c] } := by
      simp only [bareissStep, hpfind]
    rw [hstep]
    have hrow_lt' : ∀ r ∈ st.pivotRows ++ [p], r < T.numRows := by
      intro r hr
      rcases List.mem_append.mp hr with h1 | h2
      · exact hinv.row_lt r h1
      · rw [List.mem_singleton.mp h2]; exact hp_m
    have hcol_lt' : ∀ x ∈ st.pivotCols ++ [c], x < c + 1 := by
      intro x hx
      rcases List.mem_append.mp hx with h1 | h2
      · exact (hinv.col_lt x h1).trans (Nat.lt_succ_self c)
      · rw [List.mem_singleton.mp h2]; exact Nat.lt_succ_self c
    have hcol_dim' : ∀ x ∈ st.pivotCols ++ [c], x < T.numCols := by
      intro x hx
      rcases List.mem_append.mp hx with h1 | h2
      · exact hinv.col_dim x h1
      · rw [List.mem_singleton.mp h2]; exact hc
    have hlen' : (st.pivotRows ++ [p]).length = (st.pivotCols ++ [c]).length := by
      simp only [List.length_append, List.length_singleton, hinv.len_eq]
    let S := finSel st.pivotRows rfl hinv.row_lt
    let C := finSel st.pivotCols hinv.len_eq hinv.col_dim
    let S' := finSel (st.pivotRows ++ [p]) rfl hrow_lt'
    let C' := finSel (st.pivotCols ++ [c]) hlen' hcol_dim'
    have hk_eq : st.pivotRows.length + 1 = (st.pivotRows ++ [p]).length := by
      rw [List.length_append, List.length_singleton]
    have hS'_eq : S' ∘ finCongr hk_eq = Fin.snoc S ⟨p, hp_m⟩ := by
      rw [← finSel_snoc st.pivotRows rfl p hp_m hinv.row_lt hrow_lt']
      · rfl
      · simp only [List.length_append, List.length_singleton]
    have hC'_eq : C' ∘ finCongr hk_eq = Fin.snoc C ⟨c, hc⟩ := by
      rw [← finSel_snoc st.pivotCols hinv.len_eq c hc hinv.col_dim hcol_dim']
      · rfl
      · simp only [List.length_append, List.length_singleton, hinv.len_eq]
    have hΔ : Matrix.pivotDet T.toMatrix S C ≠ 0 := by
      rw [← hinv.pivotDet_eq]
      exact hinv.pivotDet_ne_zero
    have hΔ' : Matrix.bareissMatrix T.toMatrix S C ⟨p, hp_m⟩ ⟨c, hc⟩ ≠ 0 := by
      rw [← hinv.table_eq ⟨p, hp_m⟩ ⟨c, hc⟩]
      exact hp_nz
    have hwf' : IntTable.WellFormed
        { numRows := st.table.numRows, numCols := st.table.numCols,
          rows := Cslib.tabulateTable st.table.numRows st.table.numCols fun i j =>
            if i = p then st.table.entry p j
            else (st.table.entry p c * st.table.entry i j -
              st.table.entry i c * st.table.entry p j) / st.pivotDet } :=
      Cslib.isTableShape_tabulateTable _ _ _
    have htable' : ∀ (i : Fin T.numRows) (j : Fin T.numCols),
        IntTable.entry
          { numRows := st.table.numRows, numCols := st.table.numCols,
            rows := Cslib.tabulateTable st.table.numRows st.table.numCols fun r col =>
              if r = p then st.table.entry p col
              else (st.table.entry p c * st.table.entry r col -
                st.table.entry r c * st.table.entry p col) / st.pivotDet }
          i.val j.val = Matrix.bareissMatrix T.toMatrix S' C' i j := by
      intro i j
      rw [IntTable.entry, Cslib.rowEntry_tabulateTable_of_lt _ (hinv.dims.1.symm ▸ i.isLt)
        (hinv.dims.2.symm ▸ j.isLt)]
      rw [← bareissMatrix_snoc_congr T.toMatrix (Fin.snoc S ⟨p, hp_m⟩) (Fin.snoc C ⟨c, hc⟩)
        S' C' hk_eq hS'_eq hC'_eq i j]
      by_cases hip : i.val = p
      · have hieq : i = ⟨p, hp_m⟩ := Fin.ext hip
        simp only [hip, ↓reduceIte]
        rw [hieq, hinv.table_eq ⟨p, hp_m⟩ j]
        exact (Matrix.pivotDet_mul_bareissMatrix_snoc_int T.toMatrix hΔ hp_fin ⟨c, hc⟩ hΔ'
          ⟨p, hp_m⟩ j).1 rfl |>.symm
      · have hine : i ≠ ⟨p, hp_m⟩ := fun h => hip (congrArg Fin.val h)
        simp only [hip, ↓reduceIte]
        rw [hinv.table_eq ⟨p, hp_m⟩ ⟨c, hc⟩,
          hinv.table_eq i j, hinv.table_eq i ⟨c, hc⟩, hinv.table_eq ⟨p, hp_m⟩ j, hinv.pivotDet_eq]
        exact Matrix.bareissStep_ediv_eq_int T.toMatrix hΔ hp_fin ⟨c, hc⟩ hΔ' hine j
    -- Columns left of the new pivot column vanish in the extended elimination matrix at every
    -- row that is not a pivot row, or is the pivot row of a later column.
    have hzero : ∀ j : Fin T.numCols, j.val < c → ∀ r : Fin T.numRows,
        ((∀ a, S a ≠ r) ∨ ∃ a, S a = r ∧ j.val < (C a).val) →
        Matrix.bareissMatrix T.toMatrix (Fin.snoc S ⟨p, hp_m⟩) (Fin.snoc C ⟨c, hc⟩) r j = 0 := by
      intro j hjlt r hr
      let f := Int.castRingHom ℚ
      have hΔQ : Matrix.pivotDet (T.toMatrix.map f) S C ≠ 0 := by
        rw [← Matrix.map_pivotDet]; exact Int.cast_ne_zero.mpr hΔ
      have hΔ'Q : Matrix.bareissMatrix (T.toMatrix.map f) S C ⟨p, hp_m⟩ ⟨c, hc⟩ ≠ 0 := by
        rw [← Matrix.map_bareissMatrix]; change f _ ≠ 0; exact Int.cast_ne_zero.mpr hΔ'
      let Q : Fin T.numRows → Prop := fun r =>
        (∀ a, S a ≠ r) ∨ ∃ a, S a = r ∧ j.val < (C a).val
      have hQzero : ∀ r, Q r → Matrix.bareissMatrix (T.toMatrix.map f) S C r j = 0 := by
        intro r hr
        rw [← Matrix.map_bareissMatrix, Matrix.map_apply]
        rcases hr with hnr | ⟨a, rfl, hja⟩
        · rw [hinv.term_cols r hnr j hjlt]; rfl
        · rw [hinv.echelon_zero a j hja]; rfl
      have hres := Matrix.bareissMatrix_snoc_zero_of_forall (T.toMatrix.map f) hΔQ hp_fin
        ⟨c, hc⟩ hΔ'Q j Q (Or.inl hp_fin) hQzero r hr
      rw [← Matrix.map_bareissMatrix, Matrix.map_apply] at hres
      exact Int.cast_eq_zero.mp hres
    refine
      { wellFormed := hwf'
        dims := hinv.dims
        len_eq := hlen'
        row_lt := hrow_lt'
        col_lt := hcol_lt'
        col_dim := hcol_dim'
        row_nodup := List.nodup_append.mpr ⟨hinv.row_nodup, List.nodup_singleton p,
          fun x hx z hz => by
            rw [List.mem_singleton.mp hz]
            rintro rfl
            exact hp_notMem hx⟩
        col_strict := List.pairwise_append.2 ⟨hinv.col_strict, List.pairwise_singleton _ _,
          fun x hx z hz => by rw [List.mem_singleton.mp hz]; exact hinv.col_lt x hx⟩
        pivotDet_ne_zero := hp_nz
        pivotDet_eq := ?_
        table_eq := htable'
        term_cols := fun i hi j hj => ?_
        echelon_zero := fun a j hj => ?_ }
    · rw [hinv.table_eq ⟨p, hp_m⟩ ⟨c, hc⟩,
        ← pivotDet_snoc_congr T.toMatrix (Fin.snoc S ⟨p, hp_m⟩) (Fin.snoc C ⟨c, hc⟩)
          S' C' hk_eq hS'_eq hC'_eq]
      change Matrix.bareissMatrix T.toMatrix S C ⟨p, hp_m⟩ ⟨c, hc⟩ =
        (T.toMatrix.submatrix (Fin.snoc S ⟨p, hp_m⟩) (Fin.snoc C ⟨c, hc⟩)).det
      exact Matrix.bareissMatrix_nonPivot T.toMatrix C hp_fin ⟨c, hc⟩
    · have heq := bareissMatrix_snoc_congr T.toMatrix (Fin.snoc S ⟨p, hp_m⟩) (Fin.snoc C ⟨c, hc⟩)
        S' C' hk_eq hS'_eq hC'_eq i j
      rw [← heq]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hjlt | hjeq
      · refine hzero j hjlt i (Or.inl fun a ha => ?_)
        have ha' : S' ⟨a.val, by simp only [List.length_append, List.length_singleton]; omega⟩ =
            S a := Fin.ext (List.getElem_append_left a.isLt)
        exact hi _ (ha' ▸ ha)
      · have hjc : j = ⟨c, hc⟩ := Fin.ext hjeq
        subst hjc
        have hlast : (⟨c, hc⟩ : Fin T.numCols) =
            (Fin.snoc C ⟨c, hc⟩ : Fin (st.pivotRows.length + 1) → Fin T.numCols)
              (Fin.last st.pivotRows.length) := by rw [Fin.snoc_last]
        nth_rw 2 [hlast]
        refine Matrix.bareissMatrix_nonPivot_col T.toMatrix (Fin.snoc C ⟨c, hc⟩) (fun x => ?_) _
        have hx : (Fin.snoc S ⟨p, hp_m⟩ : Fin (st.pivotRows.length + 1) → Fin T.numRows) x =
            S' (finCongr hk_eq x) := by
          simpa only [Function.comp_apply] using (congrFun hS'_eq x).symm
        rw [hx]
        exact hi _
    · have heq := bareissMatrix_snoc_congr T.toMatrix (Fin.snoc S ⟨p, hp_m⟩) (Fin.snoc C ⟨c, hc⟩)
        S' C' hk_eq hS'_eq hC'_eq (S' a) j
      rw [← heq]
      change j.val < (st.pivotCols ++ [c])[a.val]'_ at hj
      have hcol_bound : (st.pivotCols ++ [c])[a.val]'(hlen' ▸ a.isLt) < c + 1 :=
        hcol_lt' _ (List.getElem_mem _)
      have hjlt : j.val < c := by omega
      exact hzero j hjlt (S' a) <| by
        by_cases hal : a.val < st.pivotRows.length
        · have haS : S' a = S ⟨a.val, hal⟩ :=
            Fin.ext (List.getElem_append_left hal)
          have haC : (C ⟨a.val, hal⟩).val = (st.pivotCols ++ [c])[a.val]'(hlen' ▸ a.isLt) := by
            change st.pivotCols[a.val]'(hinv.len_eq ▸ hal) = _
            rw [List.getElem_append_left (hinv.len_eq ▸ hal)]
          exact Or.inr ⟨⟨a.val, hal⟩, haS.symm, haC ▸ hj⟩
        · have heq_last : a.val = st.pivotRows.length := by
            have := a.isLt
            simp only [List.length_append, List.length_singleton] at this
            omega
          have haS : S' a = ⟨p, hp_m⟩ := Fin.ext (by
            change (st.pivotRows ++ [p])[a.val] = p
            simp only [heq_last, List.getElem_append_right (le_refl _), Nat.sub_self,
              List.getElem_singleton])
          rw [haS]
          exact Or.inl hp_fin

private theorem bareissElimCols_inv_aux {T : IntTable} (hT : T.WellFormed) :
    ∀ k ≤ T.numCols, BareissInv T k ((List.range k).foldl bareissStep (bareissInit T))
  | 0, _ => bareissInv_init hT
  | k + 1, hk => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact bareissInv_step hk (bareissElimCols_inv_aux hT k (Nat.le_of_succ_le hk))

/-- Correctness invariant for `bareissElimCols` across columns `< colLimit ≤ T.numCols`. -/
theorem bareissElimCols_inv {T : IntTable} (hT : T.WellFormed) {colLimit : ℕ}
    (hlim : colLimit ≤ T.numCols) :
    BareissInv T colLimit (bareissElimCols T colLimit) :=
  bareissElimCols_inv_aux hT colLimit hlim

/-- Correctness invariant for full `bareissElim`. -/
theorem bareissElim_inv {T : IntTable} (hT : T.WellFormed) :
    BareissInv T T.numCols (bareissElim T) :=
  bareissElimCols_inv hT (le_refl _)

/-! ### Executable rational RREF, rank, row basis, kernel basis, and linear solver -/

/-- Build a rational row from an `IntTable` row divided by `Δ`. -/
@[expose] def scaledIntRow (T : IntTable) (Δ : ℤ) (r : ℕ) : List ℚ :=
  (List.range T.numCols).map fun j => Rat.divInt (T.entry r j) Δ

/-- Extract normalized original rows of `M` at row indices `idxs`. -/
@[expose] def selectRatRows (M : RatTable) (idxs : List ℕ) : List (List ℚ) :=
  idxs.map fun r => normalizedRatRow M r

/-- Non-pivot column indices `< n` in ascending order. -/
@[expose] def computeNonPivotCols (n : ℕ) (pivotCols : List ℕ) : List ℕ :=
  (List.range n).filter fun c => !pivotCols.contains c

/-- Kernel basis vector associated with non-pivot column `j`. -/
@[expose] def buildKernelVec (st : BareissState) (j : ℕ) : List ℚ :=
  let pairs := st.pivotRows.zip st.pivotCols
  (List.range st.table.numCols).map fun c =>
    match pairs.find? (fun pc => pc.2 == c) with
    | some (p, _) => Rat.divInt (-st.table.entry p j) st.pivotDet
    | none => if c = j then 1 else 0

/-- Complete Bareiss–Jordan elimination on a rational matrix `M`: RREF, rank, row basis indices,
pivot/non-pivot columns, and kernel basis. -/
@[expose] def rationalElim (M : RatTable) : RationalElimResult :=
  let T := clearDenoms M
  let st := bareissElim T
  let k := st.pivotRows.length
  let pivRows := st.pivotRows.map (scaledIntRow st.table st.pivotDet)
  let zeroRows := List.replicate (M.numRows - k) (List.replicate M.numCols (0 : ℚ))
  let nonPiv := computeNonPivotCols M.numCols st.pivotCols
  { rref := ⟨M.numRows, M.numCols, pivRows ++ zeroRows⟩
    rank := k
    pivotRows := st.pivotRows
    pivotCols := st.pivotCols
    nonPivotCols := nonPiv
    kernelBasis := nonPiv.map (buildKernelVec st) }

/-- Executable rational reduced row echelon form. -/
@[expose] def ratRref (M : RatTable) : RatTable :=
  (rationalElim M).rref

/-- Exact rational matrix rank via Bareiss–Jordan elimination. -/
@[expose] def ratRank (M : RatTable) : ℕ :=
  (rationalElim M).rank

/-- Linearly independent spanning subset of rows of `M`. -/
@[expose] def ratRowBasis (M : RatTable) : List (List ℚ) :=
  selectRatRows M (rationalElim M).pivotRows

/-- Linearly independent spanning basis of `ker M.toMatrix.mulVecLin`. -/
@[expose] def ratKernelBasis (M : RatTable) : List (List ℚ) :=
  (rationalElim M).kernelBasis

/-- Augmented matrix `[A | b]` of shape `A.numRows × (A.numCols + 1)`. -/
@[expose] def augmentRatTable (A : RatTable) (b : List ℚ) : RatTable :=
  ⟨A.numRows, A.numCols + 1,
    (List.range A.numRows).map fun i => normalizedRatRow A i ++ [b.getD i 0]⟩

/-- Solve `A x = b` canonically via augmented Bareiss–Jordan elimination. -/
@[expose] def ratSolve (sys : LinearSystemInput) : LinearSolveResult :=
  let A := sys.matrix
  let aug := clearDenoms (augmentRatTable A sys.rhs)
  let st := bareissElimCols aug A.numCols
  let consistent :=
    (List.range A.numRows).all fun r =>
      st.pivotRows.contains r || decide (st.table.entry r A.numCols = 0)
  if consistent then
    let pairs := st.pivotRows.zip st.pivotCols
    let x :=
      (List.range A.numCols).map fun c =>
        match pairs.find? (fun pc => pc.2 == c) with
        | some (p, _) => Rat.divInt (st.table.entry p A.numCols) st.pivotDet
        | none => 0
    ⟨some x, st.pivotRows, st.pivotCols⟩
  else
    ⟨none, st.pivotRows, st.pivotCols⟩

/-! ### Row-scaling invariance and correctness of `rationalElim` / `ratSolve` -/

section ScaleAndCorrectness

private def rowScaled {m n : ℕ} (d : Fin m → ℚ) (A : Matrix (Fin m) (Fin n) ℚ) :
    Matrix (Fin m) (Fin n) ℚ :=
  Matrix.of fun i j => d i * A i j

private theorem span_row_rowScaled {m n : ℕ} {d : Fin m → ℚ} (hd : ∀ i, d i ≠ 0)
    (A : Matrix (Fin m) (Fin n) ℚ) :
    Submodule.span ℚ (Set.range (rowScaled d A)) = Submodule.span ℚ (Set.range A) := by
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨i, rfl⟩
    have heq : rowScaled d A i = d i • A i := rfl
    rw [heq]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rintro _ ⟨i, rfl⟩
    have heq : A i = (d i)⁻¹ • rowScaled d A i := by
      ext j
      change A i j = (d i)⁻¹ * (d i * A i j)
      rw [inv_mul_cancel_left₀ (hd i)]
    rw [heq]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

private theorem rank_rowScaled {m n : ℕ} {d : Fin m → ℚ} (hd : ∀ i, d i ≠ 0)
    (A : Matrix (Fin m) (Fin n) ℚ) :
    (rowScaled d A).rank = A.rank := by
  rw [rank_eq_finrank_span_row, rank_eq_finrank_span_row]
  change Module.finrank ℚ (Submodule.span ℚ (Set.range (rowScaled d A))) =
    Module.finrank ℚ (Submodule.span ℚ (Set.range A))
  rw [span_row_rowScaled hd A]

private theorem ker_mulVecLin_rowScaled {m n : ℕ} {d : Fin m → ℚ} (hd : ∀ i, d i ≠ 0)
    (A : Matrix (Fin m) (Fin n) ℚ) :
    LinearMap.ker (rowScaled d A).mulVecLin = LinearMap.ker A.mulVecLin := by
  ext v
  simp only [LinearMap.mem_ker, mulVecLin_apply, funext_iff, mulVec, dotProduct, Pi.zero_apply]
  refine forall_congr' fun i => ?_
  have hsum : ∑ j : Fin n, rowScaled d A i j * v j = d i * ∑ j : Fin n, A i j * v j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    change d i * A i j * v j = d i * (A i j * v j)
    rw [mul_assoc]
  rw [hsum, mul_eq_zero, or_iff_right (hd i)]

private theorem span_rowSel_rowScaled {m n k : ℕ} {d : Fin m → ℚ} (hd : ∀ i, d i ≠ 0)
    (A : Matrix (Fin m) (Fin n) ℚ) (S : Fin k → Fin m) :
    Submodule.span ℚ (Set.range fun a => rowScaled d A (S a)) =
      Submodule.span ℚ (Set.range fun a => A (S a)) := by
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨a, rfl⟩
    change rowScaled d A (S a) ∈ _
    have heq : rowScaled d A (S a) = d (S a) • A (S a) := rfl
    rw [heq]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  · rintro _ ⟨a, rfl⟩
    change A (S a) ∈ _
    have heq : A (S a) = (d (S a))⁻¹ • rowScaled d A (S a) := by
      ext j
      change A (S a) j = (d (S a))⁻¹ * (d (S a) * A (S a) j)
      rw [inv_mul_cancel_left₀ (hd (S a))]
    rw [heq]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

private theorem map_pivotDet_dim {m₁ m₂ n₁ n₂ k : ℕ}
    (A : Matrix (Fin m₁) (Fin n₁) ℤ) (B : Matrix (Fin m₂) (Fin n₂) ℚ)
    (S₁ : Fin k → Fin m₁) (C₁ : Fin k → Fin n₁) (S₂ : Fin k → Fin m₂) (C₂ : Fin k → Fin n₂)
    (hm : m₁ = m₂) (hn : n₁ = n₂)
    (hAB : ∀ i j, B ⟨i.val, hm ▸ i.isLt⟩ ⟨j.val, hn ▸ j.isLt⟩ = (A i j : ℚ))
    (hS : ∀ a, (S₂ a).val = (S₁ a).val) (hC : ∀ a, (C₂ a).val = (C₁ a).val) :
    Matrix.pivotDet B S₂ C₂ = (↑(Matrix.pivotDet A S₁ C₁) : ℚ) := by
  subst hm hn
  have hS' : S₂ = S₁ := funext fun a => Fin.ext (hS a)
  have hC' : C₂ = C₁ := funext fun a => Fin.ext (hC a)
  have hB' : B = A.map (Int.castRingHom ℚ) := by
    ext i j
    rw [Matrix.map_apply]
    change B i j = (A i j : ℚ)
    have := hAB i j
    simpa only [Fin.eta] using this
  subst hS' hC' hB'
  rw [← Matrix.map_pivotDet (Int.castRingHom ℚ)]
  rfl

private theorem map_bareissMatrix_dim {m₁ m₂ n₁ n₂ k : ℕ}
    (A : Matrix (Fin m₁) (Fin n₁) ℤ) (B : Matrix (Fin m₂) (Fin n₂) ℚ)
    (S₁ : Fin k → Fin m₁) (C₁ : Fin k → Fin n₁) (S₂ : Fin k → Fin m₂) (C₂ : Fin k → Fin n₂)
    (i₁ : Fin m₁) (j₁ : Fin n₁) (i₂ : Fin m₂) (j₂ : Fin n₂)
    (hm : m₁ = m₂) (hn : n₁ = n₂)
    (hAB : ∀ i j, B ⟨i.val, hm ▸ i.isLt⟩ ⟨j.val, hn ▸ j.isLt⟩ = (A i j : ℚ))
    (hS : ∀ a, (S₂ a).val = (S₁ a).val) (hC : ∀ a, (C₂ a).val = (C₁ a).val)
    (hi : i₂.val = i₁.val) (hj : j₂.val = j₁.val) :
    Matrix.bareissMatrix B S₂ C₂ i₂ j₂ = (↑(Matrix.bareissMatrix A S₁ C₁ i₁ j₁) : ℚ) := by
  subst hm hn
  have hS' : S₂ = S₁ := funext fun a => Fin.ext (hS a)
  have hC' : C₂ = C₁ := funext fun a => Fin.ext (hC a)
  have hB' : B = A.map (Int.castRingHom ℚ) := by
    ext i j
    rw [Matrix.map_apply]
    change B i j = (A i j : ℚ)
    have := hAB i j
    simpa only [Fin.eta] using this
  have hi' : i₂ = i₁ := Fin.ext hi
  have hj' : j₂ = j₁ := Fin.ext hj
  subst hS' hC' hB' hi' hj'
  rw [← Matrix.map_bareissMatrix (Int.castRingHom ℚ), Matrix.map_apply]
  rfl

private theorem mem_zip_find?_some {xs ys : List ℕ}
    (hlen : xs.length = ys.length) (hy_nodup : ys.Nodup) {c : ℕ} {a : Fin xs.length}
    (hca : ys[a.val]'(hlen ▸ a.isLt) = c) :
    ∃ p ∈ xs, (xs.zip ys).find? (fun pc => pc.2 == c) = some (p, c) ∧ p = xs[a.val] := by
  have hzip_len : (xs.zip ys).length = xs.length := by rw [List.length_zip, hlen, min_self]
  have hmem : (xs[a.val], c) ∈ xs.zip ys := by
    rw [List.mem_iff_getElem]
    refine ⟨a.val, by omega, ?_⟩
    rw [List.getElem_zip]
    exact Prod.ext rfl hca
  have hne : (xs.zip ys).find? (fun pc => pc.2 == c) ≠ none := by
    intro hnone
    have hf := List.find?_eq_none.mp hnone _ hmem
    simp only [beq_self_eq_true, not_true_eq_false] at hf
  obtain ⟨⟨p, y⟩, hpy⟩ := Option.ne_none_iff_exists'.mp hne
  have hp_mem := List.mem_of_find?_eq_some hpy
  have hpred := List.find?_some (p := fun pc : ℕ × ℕ => pc.2 == c) hpy
  have hyc : y = c := beq_iff_eq.mp hpred
  subst hyc
  obtain ⟨b, hb_len, hbp⟩ := List.mem_iff_getElem.mp hp_mem
  have hb_xs : b < xs.length := by omega
  rw [List.getElem_zip] at hbp
  have hyb : ys[b]'(by omega) = ys[a.val]'(by omega) :=
    (congrArg Prod.snd hbp).trans hca.symm
  have hidx : b = a.val := by
    have hinj := (List.nodup_iff_injective_getElem.mp hy_nodup) (a₁ := ⟨b, by omega⟩)
      (a₂ := ⟨a.val, by omega⟩) hyb
    exact congrArg Fin.val hinj
  have hp_eq : p = xs[a.val] := by
    have := (congrArg Prod.fst hbp).symm
    simpa only [hidx] using this
  exact ⟨p, hp_eq ▸ List.getElem_mem _, hpy, hp_eq⟩

private theorem find?_zip_none_iff {xs ys : List ℕ} (hlen : xs.length = ys.length) {c : ℕ} :
    (xs.zip ys).find? (fun pc => pc.2 == c) = none ↔ ∀ a : Fin ys.length, ys[a.val] ≠ c := by
  rw [List.find?_eq_none]
  have hzip_len : (xs.zip ys).length = ys.length := by rw [List.length_zip, hlen, min_self]
  constructor
  · intro h a ha
    have hmem : (xs[a.val]'(by omega), ys[a.val]) ∈ xs.zip ys := by
      rw [List.mem_iff_getElem]
      refine ⟨a.val, by omega, ?_⟩
      rw [List.getElem_zip]
    have hf := h _ hmem
    simp only [ha, beq_self_eq_true, not_true_eq_false] at hf
  · intro h ⟨p, y⟩ hmem hf
    obtain ⟨b, hb_len, hbp⟩ := List.mem_iff_getElem.mp hmem
    have hb_ys : b < ys.length := by omega
    rw [List.getElem_zip] at hbp
    have hne := h ⟨b, hb_ys⟩
    have hyc : y = c := beq_iff_eq.mp hf
    exact hne ((congrArg Prod.snd hbp).trans hyc)

theorem rationalElim_wellFormed (M : RatTable) : (rationalElim M).rref.WellFormed := by
  refine ⟨?_, ?_⟩
  · simp only [rationalElim, List.length_append, List.length_map, List.length_replicate]
    have hlen : (bareissElim (clearDenoms M)).pivotRows.length ≤ M.numRows := by
      have hinv := bareissElim_inv (clearDenoms_wellFormed M)
      rw [← List.toFinset_card_of_nodup hinv.row_nodup]
      have hsub : (bareissElim (clearDenoms M)).pivotRows.toFinset ⊆ Finset.range M.numRows := by
        intro r hr
        rw [List.mem_toFinset] at hr
        exact Finset.mem_range.mpr (by simpa only [clearDenoms] using hinv.row_lt r hr)
      exact (Finset.card_le_card hsub).trans_eq (Finset.card_range M.numRows)
    omega
  · intro r hr
    simp only [rationalElim, List.mem_append, List.mem_map, List.mem_replicate] at hr
    rcases hr with ⟨p, _, rfl⟩ | ⟨_, rfl⟩
    · simp only [scaledIntRow, List.length_map, List.length_range,
        (bareissElim_inv (clearDenoms_wellFormed M)).dims.2]
      rfl
    · simp only [List.length_replicate]
      rfl

private theorem clearDenoms_scaled_eq (M : RatTable) :
    (clearDenoms M).toMatrix.map (Int.cast : ℤ → ℚ) =
      rowScaled (fun i => (rowMultiplier M i : ℚ)) M.toMatrix := by
  ext i j
  exact clearDenoms_toMatrix_apply M i j

/-- Complete algebraic and reduced-echelon characterization of `rationalElim M` for any `M`. -/
theorem rationalElim_spec (M : RatTable) :
    let res := rationalElim M
    res.rref.WellFormed ∧
      res.rref.toMatrix.IsReducedRowEchelon ∧
      (∃ l, res.rref.toMatrix.IsPivotedBy l) ∧
      Submodule.span ℚ (Set.range res.rref.toMatrix) =
        Submodule.span ℚ (Set.range M.toMatrix) ∧
      res.rank = M.toMatrix.rank ∧
      res.pivotRows.length = res.rank ∧
      res.pivotCols.length = res.rank ∧
      res.nonPivotCols.length = M.numCols - res.rank ∧
      LinearIndependent ℚ (fun a : Fin res.pivotRows.length =>
        M.toMatrix ⟨res.pivotRows[a.val],
          (bareissElim_inv (clearDenoms_wellFormed M)).row_lt _ (List.getElem_mem _)⟩) ∧
      Submodule.span ℚ (Set.range fun a : Fin res.pivotRows.length =>
        M.toMatrix ⟨res.pivotRows[a.val],
          (bareissElim_inv (clearDenoms_wellFormed M)).row_lt _ (List.getElem_mem _)⟩) =
        Submodule.span ℚ (Set.range M.toMatrix) ∧
      res.kernelBasis.length = M.numCols - res.rank ∧
      LinearIndependent ℚ (fun idx : Fin res.kernelBasis.length =>
        (fun j : Fin M.numCols => res.kernelBasis[idx.val].getD j.val 0)) ∧
      Submodule.span ℚ (Set.range fun idx : Fin res.kernelBasis.length =>
        (fun j : Fin M.numCols => res.kernelBasis[idx.val].getD j.val 0)) =
        LinearMap.ker M.toMatrix.mulVecLin := by
  intro res
  set st := bareissElim (clearDenoms M)
  have hinv := bareissElim_inv (clearDenoms_wellFormed M)
  have hd : ∀ i : Fin M.numRows, (rowMultiplier M i : ℚ) ≠ 0 := fun i =>
    Nat.cast_ne_zero.mpr (rowMultiplier_pos M i).ne'
  let M' := rowScaled (fun i => (rowMultiplier M i : ℚ)) M.toMatrix
  have hM'_apply : ∀ (i : Fin (clearDenoms M).numRows) (j : Fin (clearDenoms M).numCols),
      M' ⟨i.val, i.isLt⟩ ⟨j.val, j.isLt⟩ = ((clearDenoms M).toMatrix i j : ℚ) := by
    intro i j
    have hrow : (clearDenoms M).toMatrix i j =
        (clearDenoms M).toMatrix (⟨i.val, i.isLt⟩ : Fin M.numRows)
          (⟨j.val, j.isLt⟩ : Fin M.numCols) := rfl
    rw [hrow, clearDenoms_toMatrix_apply M ⟨i.val, i.isLt⟩ ⟨j.val, j.isLt⟩]
    rfl
  let S : Fin st.pivotRows.length → Fin M.numRows := finSel st.pivotRows rfl hinv.row_lt
  let C : Fin st.pivotRows.length → Fin M.numCols := finSel st.pivotCols hinv.len_eq hinv.col_dim
  let S₀ : Fin st.pivotRows.length → Fin (clearDenoms M).numRows :=
    finSel st.pivotRows rfl hinv.row_lt
  let C₀ : Fin st.pivotRows.length → Fin (clearDenoms M).numCols :=
    finSel st.pivotCols hinv.len_eq hinv.col_dim
  have hΔ : Matrix.pivotDet M' S C ≠ 0 := by
    rw [map_pivotDet_dim (clearDenoms M).toMatrix M' S₀ C₀ S C rfl rfl hM'_apply
      (fun _ => rfl) (fun _ => rfl), ← hinv.pivotDet_eq]
    exact Int.cast_ne_zero.mpr hinv.pivotDet_ne_zero
  have hC : StrictMono C := fun a b hab =>
    pairwise_lt_strictMono hinv.len_eq hinv.col_strict hinv.col_dim hab
  have hterm : ∀ i : Fin M.numRows, (∀ a, S a ≠ i) →
      ∀ j : Fin M.numCols, Matrix.bareissMatrix M' S C i j = 0 := by
    intro i hi j
    rw [map_bareissMatrix_dim (clearDenoms M).toMatrix M' S₀ C₀ S C
      ⟨i.val, i.isLt⟩ ⟨j.val, j.isLt⟩ i j rfl rfl hM'_apply
      (fun _ => rfl) (fun _ => rfl) rfl rfl,
      hinv.term_cols ⟨i.val, i.isLt⟩ (fun a ha => hi a (Fin.ext (congrArg Fin.val ha)))
        ⟨j.val, j.isLt⟩ j.isLt]
    rfl
  have hzero : ∀ (a : Fin st.pivotRows.length) (j : Fin M.numCols),
      j < C a → Matrix.bareissMatrix M' S C (S a) j = 0 := by
    intro a j hj
    rw [map_bareissMatrix_dim (clearDenoms M).toMatrix M' S₀ C₀ S C
      (S₀ a) ⟨j.val, j.isLt⟩ (S a) j rfl rfl hM'_apply
      (fun _ => rfl) (fun _ => rfl) rfl rfl,
      hinv.echelon_zero a ⟨j.val, j.isLt⟩ hj]
    rfl
  have ⟨hSinj, hCinj⟩ := Matrix.injective_of_pivotDet_ne_zero hΔ
  have hkm : st.pivotRows.length ≤ M.numRows := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective S hSinj
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair
    (fun a : Fin st.pivotRows.length => (⟨a.val, a.isLt.trans_le hkm⟩ : Fin M.numRows)) S
    (fun a b hab => Fin.ext (congrArg (Fin.val : Fin M.numRows → ℕ) hab)) hSinj
  have ⟨hUpiv, hUrref⟩ := Matrix.isReducedRowEchelon_rrefOfBareiss hΔ hC hterm hzero σ hσ
  have hrref_eq : res.rref.toMatrix = (Matrix.rrefOfBareiss M' S C).submatrix σ id := by
    ext i j
    change res.rref.entry i.val j.val = Matrix.rrefOfBareiss M' S C (σ i) j
    have hΔ_rat : (st.pivotDet : ℚ) = Matrix.pivotDet M' S C := by
      rw [map_pivotDet_dim (clearDenoms M).toMatrix M' S₀ C₀ S C rfl rfl hM'_apply
        (fun _ => rfl) (fun _ => rfl), ← hinv.pivotDet_eq]
    by_cases hi : i.val < st.pivotRows.length
    · have hrow_i : res.rref.rows.getD i.val [] =
          scaledIntRow st.table st.pivotDet (st.pivotRows[i.val]) := by
        change ((st.pivotRows.map (scaledIntRow st.table st.pivotDet) ++
          List.replicate (M.numRows - st.pivotRows.length)
            (List.replicate M.numCols 0)).getD i.val []) = _
        rw [List.getD_append _ _ _ _ (by simp only [List.length_map]; exact hi),
          List.getD_eq_getElem _ _ (by simp only [List.length_map]; exact hi), List.getElem_map]
      have hpiv_row : res.rref.entry i.val j.val =
          Rat.divInt (st.table.entry (st.pivotRows[i.val]) j.val) st.pivotDet := by
        rw [RatTable.entry, hrow_i]
        exact List.getD_map_range _ 0 (by rw [hinv.dims.2]; exact j.isLt)
      rw [hpiv_row, Rat.divInt_eq_div]
      have hsi : S ⟨i.val, hi⟩ = σ i := (hσ ⟨i.val, hi⟩).symm
      rw [← hsi]
      change (st.table.entry (S ⟨i.val, hi⟩).val j.val : ℚ) / (st.pivotDet : ℚ) =
        (Matrix.pivotDet M' S C)⁻¹ * Matrix.bareissMatrix M' S C (S ⟨i.val, hi⟩) j
      rw [map_bareissMatrix_dim (clearDenoms M).toMatrix M' S₀ C₀ S C
        (S₀ ⟨i.val, hi⟩) ⟨j.val, j.isLt⟩ (S ⟨i.val, hi⟩) j rfl rfl hM'_apply
        (fun _ => rfl) (fun _ => rfl) rfl rfl,
        ← hinv.table_eq (S₀ ⟨i.val, hi⟩) ⟨j.val, j.isLt⟩, hΔ_rat, div_eq_mul_inv, mul_comm]
      rfl
    · have hrow_i : res.rref.rows.getD i.val [] = List.replicate M.numCols 0 := by
        change ((st.pivotRows.map (scaledIntRow st.table st.pivotDet) ++
          List.replicate (M.numRows - st.pivotRows.length)
            (List.replicate M.numCols 0)).getD i.val []) = _
        rw [List.getD_append_right _ _ _ _ (by simp only [List.length_map]; omega)]
        exact List.getD_replicate _
          (by have hi_lt : i.val < M.numRows := i.isLt; simp only [List.length_map]; omega)
      have hzero_row : res.rref.entry i.val j.val = 0 := by
        rw [RatTable.entry, hrow_i]
        exact List.getD_replicate _ j.isLt
      have hnot : ∀ a : Fin st.pivotRows.length, S a ≠ σ i := by
        intro a ha
        rw [← hσ a] at ha
        have hval := congrArg Fin.val (σ.injective ha)
        have ha_lt := a.isLt
        dsimp only at hval
        omega
      rw [hzero_row]
      change 0 = (Matrix.pivotDet M' S C)⁻¹ * Matrix.bareissMatrix M' S C (σ i) j
      rw [hterm (σ i) hnot j, mul_zero]
  have hspan_rref : Submodule.span ℚ (Set.range res.rref.toMatrix) =
      Submodule.span ℚ (Set.range M.toMatrix) := by
    rw [hrref_eq]
    have hperm : Set.range ((Matrix.rrefOfBareiss M' S C).submatrix σ id) =
        Set.range (Matrix.rrefOfBareiss M' S C) := by
      ext v
      constructor
      · rintro ⟨i, rfl⟩; exact ⟨σ i, rfl⟩
      · rintro ⟨i, rfl⟩; exact ⟨σ.symm i, funext fun j => by
          change Matrix.rrefOfBareiss M' S C (σ (σ.symm i)) j = Matrix.rrefOfBareiss M' S C i j
          rw [Equiv.apply_symm_apply]⟩
    change Submodule.span ℚ (Set.range ((Matrix.rrefOfBareiss M' S C).submatrix σ id)) = _
    rw [hperm, Matrix.span_row_rrefOfBareiss hΔ, span_row_rowScaled hd M.toMatrix]
  have hrank : res.rank = M.toMatrix.rank := by
    change st.pivotRows.length = M.toMatrix.rank
    rw [← rank_rowScaled hd M.toMatrix]
    exact (Matrix.rank_eq_of_bareiss_terminal hΔ hterm).symm
  have hrow_li : LinearIndependent ℚ (fun a : Fin st.pivotRows.length => M.toMatrix (S a)) := by
    refine (LinearIndependent.units_smul_iff (R := ℚ)
      (fun a : Fin st.pivotRows.length => M.toMatrix (S a))
      (fun a : Fin st.pivotRows.length =>
        Units.mk0 (rowMultiplier M (S a) : ℚ) (hd (S a)))).mp ?_
    exact Matrix.linearIndependent_row_of_pivotDet_ne_zero hΔ
  have hrow_span :
      Submodule.span ℚ (Set.range fun a : Fin st.pivotRows.length => M.toMatrix (S a)) =
      Submodule.span ℚ (Set.range M.toMatrix) := by
    rw [← span_rowSel_rowScaled hd M.toMatrix S, ← span_row_rowScaled hd M.toMatrix]
    exact Matrix.span_rowBasis_eq_of_bareiss_terminal hΔ hterm
  have hnonPiv_nodup : res.nonPivotCols.Nodup :=
    List.Nodup.filter _ List.nodup_range
  have hC_nodup : st.pivotCols.Nodup :=
    List.Pairwise.imp (fun h => Nat.ne_of_lt h) hinv.col_strict
  have hnonPiv_iff : ∀ c, c ∈ res.nonPivotCols ↔ c < M.numCols ∧ ∀ a, (C a).val ≠ c := by
    intro c
    simp only [res, rationalElim, computeNonPivotCols, List.mem_filter, List.mem_range,
      Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not]
    constructor
    · rintro ⟨hc, hnc⟩
      exact ⟨hc, fun a ha => hnc (by rw [← ha]; exact List.getElem_mem _)⟩
    · rintro ⟨hc, hnc⟩
      refine ⟨hc, fun hmem => ?_⟩
      obtain ⟨idx, hidx, hval⟩ := List.mem_iff_getElem.mp hmem
      exact hnc ⟨idx, hinv.len_eq ▸ hidx⟩ hval
  have hnonPiv_len : res.nonPivotCols.length = M.numCols - res.rank := by
    have hcard : res.nonPivotCols.length =
        (Finset.univ \ Finset.image C Finset.univ).card := by
      have h1 : res.nonPivotCols.length = (res.nonPivotCols.toFinset).card :=
        (List.toFinset_card_of_nodup hnonPiv_nodup).symm
      rw [h1]
      refine Finset.card_bij (fun c hc => ⟨c, (hnonPiv_iff c).mp (List.mem_toFinset.mp hc) |>.1⟩)
        ?_ ?_ ?_
      · intro c hc
        simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_image, true_and, not_exists]
        intro a ha
        exact ((hnonPiv_iff c).mp (List.mem_toFinset.mp hc)).2 a (congrArg Fin.val ha)
      · intro c₁ _ c₂ _ h
        exact congrArg Fin.val h
      · intro j hj
        simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_image, true_and, not_exists] at hj
        refine ⟨j.val, List.mem_toFinset.mpr ((hnonPiv_iff j.val).mpr ⟨j.isLt, fun a ha => ?_⟩),
          Fin.ext rfl⟩
        exact hj a (Fin.ext ha)
    rw [hcard, Finset.card_sdiff, Finset.inter_univ, Finset.card_fin,
      Finset.card_image_of_injective _ hCinj, Finset.card_fin]
    rfl
  have hker_len : res.kernelBasis.length = M.numCols - res.rank := by
    simpa only [res, rationalElim, List.length_map] using hnonPiv_len
  have hker_len_np : res.kernelBasis.length = res.nonPivotCols.length := by
    simp only [res, rationalElim, List.length_map]
  let kerEquiv : Fin res.kernelBasis.length ≃ { j : Fin M.numCols // ∀ a, C a ≠ j } :=
    ((finCongr hker_len_np).trans (List.Nodup.getEquiv res.nonPivotCols hnonPiv_nodup)).trans
      { toFun := fun ⟨c, hc⟩ =>
          ⟨⟨c, ((hnonPiv_iff c).mp hc).1⟩,
            fun a ha => ((hnonPiv_iff c).mp hc).2 a (congrArg Fin.val ha)⟩
        invFun := fun j =>
          ⟨j.1.val, (hnonPiv_iff j.1.val).mpr ⟨j.1.isLt, fun a ha => j.2 a (Fin.ext ha)⟩⟩
        left_inv := fun _ => rfl
        right_inv := fun ⟨⟨_, _⟩, _⟩ => rfl }
  have hker_vec : ∀ idx : Fin res.kernelBasis.length,
      (fun j : Fin M.numCols => res.kernelBasis[idx.val].getD j.val 0) =
        Matrix.kernelBasisVec M' S C (kerEquiv idx).1 := by
    intro idx
    ext c
    have hidx_len : idx.val < res.nonPivotCols.length := by
      simpa only [res, rationalElim, List.length_map] using idx.isLt
    have hk_eq :
        res.kernelBasis[idx.val] = buildKernelVec st (res.nonPivotCols[idx.val]'hidx_len) := by
      change (res.nonPivotCols.map (buildKernelVec st))[idx.val]'(by
        simp only [List.length_map]; exact hidx_len) = _
      rw [List.getElem_map]
    rw [hk_eq]
    simp only [buildKernelVec]
    rw [List.getD_map_range _ 0 (by rw [hinv.dims.2]; exact c.isLt)]
    by_cases hc : ∃ a, C a = c
    · obtain ⟨a, rfl⟩ := hc
      have hca : st.pivotCols[a.val]'(hinv.len_eq ▸ a.isLt) = (C a).val := rfl
      obtain ⟨p, _, hfind, hp_eq⟩ :=
        mem_zip_find?_some hinv.len_eq hC_nodup (a := ⟨a.val, a.isLt⟩) hca
      rw [hfind]
      dsimp only
      rw [Matrix.kernelBasisVec_pivot hΔ _ a, Rat.divInt_eq_div, Int.cast_neg, neg_div]
      congr 1
      have hΔ_rat : (st.pivotDet : ℚ) = Matrix.pivotDet M' S C := by
        rw [map_pivotDet_dim (clearDenoms M).toMatrix M' S₀ C₀ S C rfl rfl hM'_apply
          (fun _ => rfl) (fun _ => rfl), ← hinv.pivotDet_eq]
      have hp_S : p = (S a).val := hp_eq
      change (st.table.entry p (kerEquiv idx).1.val : ℚ) / (st.pivotDet : ℚ) =
        (Matrix.pivotDet M' S C)⁻¹ * Matrix.bareissMatrix M' S C (S a) (kerEquiv idx).1
      rw [map_bareissMatrix_dim (clearDenoms M).toMatrix M' S₀ C₀ S C
        (S₀ a) ⟨(kerEquiv idx).1.val, (kerEquiv idx).1.isLt⟩
        (S a) (kerEquiv idx).1 rfl rfl hM'_apply
        (fun _ => rfl) (fun _ => rfl) rfl rfl]
      dsimp only [S₀, C₀]
      rw [← hinv.table_eq (finSel st.pivotRows rfl hinv.row_lt a)
          ⟨(kerEquiv idx).1.val, (kerEquiv idx).1.isLt⟩,
        hp_S, hΔ_rat, div_eq_mul_inv, mul_comm]
      rfl
    · have hnc : ∀ a, C a ≠ c := fun a ha => hc ⟨a, ha⟩
      have hnone : (st.pivotRows.zip st.pivotCols).find? (fun pc => pc.2 == c.val) = none := by
        refine (find?_zip_none_iff hinv.len_eq).mpr fun a ha => ?_
        exact hnc ⟨a.val, hinv.len_eq.symm ▸ a.isLt⟩ (Fin.ext ha)
      rw [hnone, Matrix.kernelBasisVec_nonPivot S C _ c hnc]
      have hker_val : (kerEquiv idx).1.val = res.nonPivotCols[idx.val]'hidx_len :=
        List.get_eq_getElem
      simp only [Fin.ext_iff, hker_val]
  have hker_li : LinearIndependent ℚ (fun idx : Fin res.kernelBasis.length =>
      (fun j : Fin M.numCols => res.kernelBasis[idx.val].getD j.val 0)) := by
    have hli := (Matrix.linearIndependent_kernelBasisVec M' S C).comp kerEquiv kerEquiv.injective
    convert hli using 1
    ext idx j
    exact congrFun (hker_vec idx) j
  have hker_span : Submodule.span ℚ (Set.range fun idx : Fin res.kernelBasis.length =>
      (fun j : Fin M.numCols => res.kernelBasis[idx.val].getD j.val 0)) =
      LinearMap.ker M.toMatrix.mulVecLin := by
    rw [← ker_mulVecLin_rowScaled hd M.toMatrix, ← Matrix.span_kernelBasisVec hΔ hterm]
    congr 1
    ext v
    constructor
    · rintro ⟨idx, rfl⟩; exact ⟨kerEquiv idx, (hker_vec idx).symm⟩
    · rintro ⟨j, rfl⟩
      obtain ⟨idx, rfl⟩ := kerEquiv.surjective j
      exact ⟨idx, hker_vec idx⟩
  refine ⟨rationalElim_wellFormed M, ?_, ?_, hspan_rref, hrank, rfl, hinv.len_eq.symm,
    hnonPiv_len, hrow_li, hrow_span, hker_len, hker_li, hker_span⟩
  · rw [hrref_eq]; exact hUrref
  · refine ⟨fun i => if hi : i.val < st.pivotRows.length then
        ((⟨(C ⟨i.val, hi⟩).val, (C ⟨i.val, hi⟩).isLt⟩ : Fin res.rref.numCols) :
          WithTop (Fin res.rref.numCols)) else ⊤, ?_⟩
    rw [hrref_eq]
    exact hUpiv

/-- Convenience projection: `ratRref M` is in Mathlib's `Matrix.IsReducedRowEchelon`. -/
theorem ratRref_isReducedRowEchelon (M : RatTable) :
    (ratRref M).toMatrix.IsReducedRowEchelon :=
  (rationalElim_spec M).2.1

/-- Convenience projection: `ratRank M = M.toMatrix.rank`. -/
theorem ratRank_eq (M : RatTable) : ratRank M = M.toMatrix.rank :=
  (rationalElim_spec M).2.2.2.2.1

theorem augmentRatTable_toMatrix_apply (A : RatTable) (b : List ℚ)
    (i : Fin (augmentRatTable A b).numRows) (j : Fin (augmentRatTable A b).numCols) :
    (augmentRatTable A b).toMatrix i j =
      if hj : j.val < A.numCols then A.toMatrix ⟨i.val, i.isLt⟩ ⟨j.val, hj⟩
      else b.getD i.val 0 := by
  rw [RatTable.toMatrix_apply, RatTable.entry]
  dsimp only [augmentRatTable]
  rw [List.getD_map_range (n := A.numRows) _ [] i.isLt]
  have hnorm_len : (normalizedRatRow A i.val).length = A.numCols := by
    simp only [normalizedRatRow, List.length_map, List.length_range]
  by_cases hj : j.val < A.numCols
  · simp only [hj, ↓reduceDIte]
    rw [List.getD_append _ _ _ _ (by omega : j.val < (normalizedRatRow A i.val).length)]
    exact List.getD_map_range _ 0 hj
  · simp only [hj, ↓reduceDIte]
    have hjeq : j.val = (normalizedRatRow A i.val).length := by
      have hjlt : j.val < A.numCols + 1 := j.isLt
      omega
    rw [hjeq, List.getD_append_cons_length]

private theorem augmentRatTable_toMatrix (A : RatTable) (b : List ℚ) :
    (augmentRatTable A b).toMatrix = Matrix.augmentCol A.toMatrix (fun i => b.getD i.val 0) := by
  ext i j
  rw [augmentRatTable_toMatrix_apply A b ⟨i.val, i.isLt⟩ ⟨j.val, j.isLt⟩]
  change _ = Matrix.augmentCol A.toMatrix (fun i => b.getD i.val 0) ⟨i.val, i.isLt⟩ ⟨j.val, j.isLt⟩
  dsimp only [Matrix.augmentCol]
  rw [Matrix.of_apply]
  by_cases hj : j.val < A.numCols
  · have hjeq : (⟨j.val, j.isLt⟩ : Fin (A.numCols + 1)) = Fin.castSucc ⟨j.val, hj⟩ := rfl
    simp only [hj, ↓reduceDIte]
    rw [hjeq, Fin.snoc_castSucc]
  · have hjeq : (⟨j.val, j.isLt⟩ : Fin (A.numCols + 1)) = Fin.last A.numCols := by
      apply Fin.ext
      have hjlt : j.val < A.numCols + 1 := j.isLt
      rw [Fin.val_last]
      dsimp only
      omega
    simp only [hj, ↓reduceDIte]
    rw [hjeq, Fin.snoc_last]

/-- Soundness and completeness of `ratSolve sys` with respect to `sys.matrix.toMatrix *ᵥ x = b`. -/
theorem ratSolve_spec (sys : LinearSystemInput) :
    let A := sys.matrix
    let b : Fin A.numRows → ℚ := fun i => sys.rhs.getD i.val 0
    let res := ratSolve sys
    (∀ x, res.solution = some x →
      x.length = A.numCols ∧ A.toMatrix *ᵥ (fun j : Fin A.numCols => x.getD j.val 0) = b) ∧
    (res.solution = none ↔ ¬ ∃ x : Fin A.numCols → ℚ, A.toMatrix *ᵥ x = b) := by
  intro A b res
  set augRat := augmentRatTable A sys.rhs
  set st := bareissElimCols (clearDenoms augRat) A.numCols
  have hinv := bareissElimCols_inv (clearDenoms_wellFormed augRat) (colLimit := A.numCols)
    (show A.numCols ≤ (clearDenoms augRat).numCols by
      simp only [augRat, augmentRatTable, clearDenoms]; omega)
  have hd : ∀ i : Fin A.numRows, (rowMultiplier augRat ⟨i.val, i.isLt⟩ : ℚ) ≠ 0 := fun i =>
    Nat.cast_ne_zero.mpr (rowMultiplier_pos augRat ⟨i.val, i.isLt⟩).ne'
  let A' : Matrix (Fin A.numRows) (Fin A.numCols) ℚ :=
    rowScaled (fun i => (rowMultiplier augRat ⟨i.val, i.isLt⟩ : ℚ)) A.toMatrix
  let b' : Fin A.numRows → ℚ := fun i => (rowMultiplier augRat ⟨i.val, i.isLt⟩ : ℚ) * b i
  let M' : Matrix (Fin A.numRows) (Fin (A.numCols + 1)) ℚ := Matrix.augmentCol A' b'
  have hM'_apply : ∀ (i : Fin (clearDenoms augRat).numRows) (j : Fin (clearDenoms augRat).numCols),
      M' ⟨i.val, i.isLt⟩ ⟨j.val, j.isLt⟩ = ((clearDenoms augRat).toMatrix i j : ℚ) := by
    intro i j
    have hrow : (clearDenoms augRat).toMatrix i j =
        (clearDenoms augRat).toMatrix (⟨i.val, i.isLt⟩ : Fin augRat.numRows)
          (⟨j.val, j.isLt⟩ : Fin augRat.numCols) := rfl
    rw [hrow, clearDenoms_toMatrix_apply, augmentRatTable_toMatrix_apply]
    dsimp only [M', A', b', Matrix.augmentCol]
    rw [Matrix.of_apply]
    by_cases hj : j.val < A.numCols
    · have hjeq : (⟨j.val, j.isLt⟩ : Fin (A.numCols + 1)) = Fin.castSucc ⟨j.val, hj⟩ := rfl
      simp only [hj, ↓reduceDIte]
      rw [hjeq, Fin.snoc_castSucc]
      rfl
    · have hjeq : (⟨j.val, j.isLt⟩ : Fin (A.numCols + 1)) = Fin.last A.numCols := by
        apply Fin.ext
        have hjlt : j.val < A.numCols + 1 := j.isLt
        rw [Fin.val_last]
        dsimp only
        omega
      simp only [hj, ↓reduceDIte]
      rw [hjeq, Fin.snoc_last]
  let S : Fin st.pivotRows.length → Fin A.numRows := finSel st.pivotRows rfl hinv.row_lt
  let Caug : Fin st.pivotRows.length → Fin (A.numCols + 1) :=
    finSel st.pivotCols hinv.len_eq hinv.col_dim
  have hC_A_lt : ∀ c ∈ st.pivotCols, c < A.numCols := hinv.col_lt
  let C_A : Fin st.pivotRows.length → Fin A.numCols :=
    finSel st.pivotCols hinv.len_eq hC_A_lt
  let S₀ : Fin st.pivotRows.length → Fin (clearDenoms augRat).numRows :=
    finSel st.pivotRows rfl hinv.row_lt
  let Caug₀ : Fin st.pivotRows.length → Fin (clearDenoms augRat).numCols :=
    finSel st.pivotCols hinv.len_eq hinv.col_dim
  have hCaug_eq : Caug = Fin.castSucc ∘ C_A := by
    ext a
    rfl
  have hΔ_aug : Matrix.pivotDet M' S Caug ≠ 0 := by
    rw [map_pivotDet_dim (clearDenoms augRat).toMatrix M' S₀ Caug₀ S Caug rfl rfl hM'_apply
      (fun _ => rfl) (fun _ => rfl), ← hinv.pivotDet_eq]
    exact Int.cast_ne_zero.mpr hinv.pivotDet_ne_zero
  have hΔ_A : Matrix.pivotDet A' S C_A ≠ 0 := by
    have hsub : M'.submatrix S Caug = A'.submatrix S C_A := by
      ext u v
      rw [Matrix.submatrix_apply, Matrix.submatrix_apply, hCaug_eq, Function.comp_apply]
      dsimp only [M', Matrix.augmentCol]
      rw [Matrix.of_apply, Fin.snoc_castSucc]
    change (A'.submatrix S C_A).det ≠ 0
    rw [← hsub]
    exact hΔ_aug
  have hterm_A : ∀ i : Fin A.numRows, (∀ a, S a ≠ i) →
      ∀ j : Fin A.numCols, Matrix.bareissMatrix A' S C_A i j = 0 := by
    intro i hi j
    have hsub : Matrix.bareissMatrix A' S C_A i j =
        Matrix.bareissMatrix M' S (Fin.castSucc ∘ C_A) i j.castSucc := by
      have hm1 : (A'.submatrix (Fin.snoc S i) (Fin.snoc C_A j)).det =
          (M'.submatrix (Fin.snoc S i) (Fin.snoc (Fin.castSucc ∘ C_A) j.castSucc)).det := by
        congr 1
        ext u v
        by_cases hv : v.val < st.pivotRows.length
        · have hv' : v = Fin.castSucc ⟨v.val, hv⟩ := rfl
          rw [hv', Matrix.submatrix_apply, Matrix.submatrix_apply, Fin.snoc_castSucc,
            Fin.snoc_castSucc, Function.comp_apply]
          dsimp only [M', Matrix.augmentCol]
          rw [Matrix.of_apply, Fin.snoc_castSucc]
        · have hv' : v = Fin.last st.pivotRows.length :=
            Fin.ext (by have := v.isLt; rw [Fin.val_last]; omega)
          rw [hv', Matrix.submatrix_apply, Matrix.submatrix_apply, Fin.snoc_last,
            Fin.snoc_last]
          dsimp only [M', Matrix.augmentCol]
          rw [Matrix.of_apply, Fin.snoc_castSucc]
      rw [Matrix.bareissMatrix_nonPivot A' C_A hi j,
        Matrix.bareissMatrix_nonPivot M' (Fin.castSucc ∘ C_A) hi j.castSucc]
      exact hm1
    rw [hsub, ← hCaug_eq, map_bareissMatrix_dim (clearDenoms augRat).toMatrix M'
      S₀ Caug₀ S Caug ⟨i.val, i.isLt⟩ ⟨j.val, j.castSucc.isLt⟩ i j.castSucc rfl rfl
      hM'_apply (fun _ => rfl) (fun _ => rfl) rfl rfl,
      hinv.term_cols ⟨i.val, i.isLt⟩ (fun a ha => hi a (Fin.ext (congrArg Fin.val ha)))
        ⟨j.val, j.castSucc.isLt⟩ j.isLt]
    rfl
  have haug_res := Matrix.rrefOfBareiss_augmentCol hΔ_A hterm_A b'
  have hsolve_iff : ∀ x, A' *ᵥ x = b' ↔ A.toMatrix *ᵥ x = b := by
    intro x
    rw [funext_iff, funext_iff]
    refine forall_congr' fun i => ?_
    rw [Matrix.mulVec_apply, Matrix.mulVec_apply]
    have hsum : A'.row i ⬝ᵥ x = rowMultiplier augRat ⟨i.val, i.isLt⟩ * (A.toMatrix.row i ⬝ᵥ x) := by
      change ∑ j : Fin A.numCols, A' i j * x j =
        (rowMultiplier augRat ⟨i.val, i.isLt⟩ : ℚ) * ∑ j : Fin A.numCols, A.toMatrix i j * x j
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      dsimp only [A', rowScaled]
      rw [Matrix.of_apply, mul_assoc]
    rw [hsum]
    exact mul_right_inj' (hd i)
  let consistent := (List.range A.numRows).all fun r =>
    st.pivotRows.contains r || decide (st.table.entry r A.numCols = 0)
  have hcons_iff : consistent = true ↔
      ∀ i : Fin A.numRows, (∀ a, S a ≠ i) →
        Matrix.bareissMatrix M' S (Fin.castSucc ∘ C_A) i (Fin.last A.numCols) = 0 := by
    simp only [consistent, List.all_eq_true, List.mem_range, Bool.or_eq_true,
      List.contains_eq_mem, decide_eq_true_eq]
    constructor
    · intro h i hi
      rcases h i.val i.isLt with hmem | hzero
      · obtain ⟨idx, hidx, hval⟩ := List.mem_iff_getElem.mp hmem
        exact absurd (Fin.ext hval) (hi ⟨idx, hidx⟩)
      · rw [← hCaug_eq, map_bareissMatrix_dim (clearDenoms augRat).toMatrix M'
          S₀ Caug₀ S Caug ⟨i.val, i.isLt⟩
          ⟨A.numCols, by simp only [augRat, augmentRatTable, clearDenoms, Nat.lt_succ_self]⟩
          i (Fin.last A.numCols) rfl rfl hM'_apply (fun _ => rfl) (fun _ => rfl)
          rfl (Fin.val_last A.numCols).symm,
          ← hinv.table_eq ⟨i.val, i.isLt⟩ ⟨A.numCols, _⟩, hzero]
        rfl
    · intro h r hr
      by_cases hmem : r ∈ st.pivotRows
      · exact Or.inl hmem
      · right
        have hnot : ∀ a, S a ≠ ⟨r, hr⟩ := by
          intro a ha
          apply hmem
          have hval : (S a).val = r := congrArg Fin.val ha
          rw [← hval]
          exact List.getElem_mem _
        have hz := h ⟨r, hr⟩ hnot
        rw [← hCaug_eq, map_bareissMatrix_dim (clearDenoms augRat).toMatrix M'
          S₀ Caug₀ S Caug ⟨r, hr⟩
          ⟨A.numCols, by simp only [augRat, augmentRatTable, clearDenoms, Nat.lt_succ_self]⟩
          ⟨r, hr⟩ (Fin.last A.numCols) rfl rfl hM'_apply (fun _ => rfl) (fun _ => rfl)
          rfl (Fin.val_last A.numCols).symm,
          ← hinv.table_eq ⟨r, hr⟩ ⟨A.numCols, _⟩] at hz
        exact Int.cast_eq_zero.mp hz
  have hC_nodup : st.pivotCols.Nodup :=
    List.Pairwise.imp (fun h => Nat.ne_of_lt h) hinv.col_strict
  have hsol_vec :
      (fun c : Fin A.numCols =>
        match (st.pivotRows.zip st.pivotCols).find? (fun pc => pc.2 == c.val) with
        | some (p, _) => Rat.divInt (st.table.entry p A.numCols) st.pivotDet
        | none => 0) = Matrix.solveVec A' S C_A b' := by
    ext c
    have hΔ_rat : (st.pivotDet : ℚ) = Matrix.pivotDet M' S (Fin.castSucc ∘ C_A) := by
      rw [← hCaug_eq, map_pivotDet_dim (clearDenoms augRat).toMatrix M' S₀ Caug₀ S Caug
        rfl rfl hM'_apply (fun _ => rfl) (fun _ => rfl), ← hinv.pivotDet_eq]
    by_cases hc : ∃ a, C_A a = c
    · obtain ⟨a, rfl⟩ := hc
      have hca : st.pivotCols[a.val]'(hinv.len_eq ▸ a.isLt) = (C_A a).val := rfl
      obtain ⟨p, _, hfind, hp_eq⟩ := mem_zip_find?_some hinv.len_eq hC_nodup hca
      rw [hfind]
      dsimp only
      rw [Rat.divInt_eq_div, ← haug_res.1 a]
      change (st.table.entry p A.numCols : ℚ) / (st.pivotDet : ℚ) =
        (Matrix.pivotDet M' S (Fin.castSucc ∘ C_A))⁻¹ *
          Matrix.bareissMatrix M' S (Fin.castSucc ∘ C_A) (S a) (Fin.last A.numCols)
      have hp_S : p = (S a).val := hp_eq
      rw [← hCaug_eq, map_bareissMatrix_dim (clearDenoms augRat).toMatrix M'
        S₀ Caug₀ S Caug (S₀ a)
        ⟨A.numCols, by simp only [augRat, augmentRatTable, clearDenoms, Nat.lt_succ_self]⟩
        (S a) (Fin.last A.numCols) rfl rfl hM'_apply (fun _ => rfl) (fun _ => rfl)
        rfl (Fin.val_last A.numCols).symm,
        ← hinv.table_eq (S₀ a) ⟨A.numCols, _⟩, hp_S, hΔ_rat, div_eq_mul_inv, mul_comm]
      rfl
    · have hnc : ∀ a, C_A a ≠ c := fun a ha => hc ⟨a, ha⟩
      have hnone : (st.pivotRows.zip st.pivotCols).find? (fun pc => pc.2 == c.val) = none := by
        refine (find?_zip_none_iff hinv.len_eq).mpr fun a ha => ?_
        exact hnc ⟨a.val, hinv.len_eq.symm ▸ a.isLt⟩ (Fin.ext ha)
      rw [hnone, Matrix.solveVec_nonPivot A' S C_A b' hnc]
  constructor
  · intro x hx
    simp only [res, ratSolve] at hx
    split_ifs at hx with hcons'
    have hcons : consistent = true := hcons'
    simp only [Option.some.injEq] at hx
    subst hx
    refine ⟨by simp only [List.length_map, List.length_range]; rfl, ?_⟩
    have hvec : (fun j : Fin A.numCols =>
        ((List.range sys.matrix.numCols).map fun c =>
          match (st.pivotRows.zip st.pivotCols).find? (fun pc => pc.2 == c) with
          | some (p, _) => Rat.divInt (st.table.entry p A.numCols) st.pivotDet
          | none => 0).getD j.val 0) = Matrix.solveVec A' S C_A b' := by
      ext c
      rw [List.getD_map_range _ 0 c.isLt]
      exact congrFun hsol_vec c
    rw [hvec, ← hsolve_iff]
    exact haug_res.2.mpr (hcons_iff.mp hcons)
  · constructor
    · intro hnone hex
      simp only [res, ratSolve] at hnone
      split_ifs at hnone with hcons'
      obtain ⟨x, hx⟩ := hex
      have hx' : A' *ᵥ x = b' := (hsolve_iff x).mpr hx
      have hsol : A' *ᵥ Matrix.solveVec A' S C_A b' = b' :=
        (Matrix.mulVec_solveVec_eq_iff_exists_mulVec_eq hΔ_A hterm_A b').mpr ⟨x, hx'⟩
      exact hcons' (hcons_iff.mpr (haug_res.2.mp hsol))
    · intro hnex
      simp only [res, ratSolve]
      split_ifs with hcons'
      · exfalso
        apply hnex
        refine ⟨Matrix.solveVec A' S C_A b', (hsolve_iff _).mp ?_⟩
        exact haug_res.2.mpr (hcons_iff.mp hcons')
      · rfl

end ScaleAndCorrectness

/-! ### Bit-length and magnitude bounds -/

/-- Uniform Hadamard/factorial upper bound `(min m n + 1)! * (B + 1) ^ (min m n + 1)`. -/
@[expose] def stageEntryBound (m n B : ℕ) : ℕ :=
  (min m n + 1).factorial * (B + 1) ^ (min m n + 1)

theorem one_le_stageEntryBound (m n B : ℕ) : 1 ≤ stageEntryBound m n B :=
  Nat.mul_pos (Nat.factorial_pos _) (Nat.pow_pos (Nat.succ_pos B))

theorem stageEntryBound_mono_left {m n₁ n₂ B : ℕ} (h : n₁ ≤ n₂) :
    stageEntryBound m n₁ B ≤ stageEntryBound m n₂ B := by
  have hmin : min m n₁ ≤ min m n₂ :=
    Nat.le_min.mpr ⟨Nat.min_le_left _ _, (Nat.min_le_right _ _).trans h⟩
  exact Nat.mul_le_mul (Nat.factorial_le (Nat.add_le_add_right hmin 1))
    (Nat.pow_le_pow_right (Nat.succ_pos B) (Nat.add_le_add_right hmin 1))

theorem size_stageEntryBound_le (m n B : ℕ) :
    (stageEntryBound m n B).size ≤
      (min m n + 1) * ((min m n + 1).size + (B + 1).size) + 2 := by
  unfold stageEntryBound
  have h1 := Nat.size_mul_le ((min m n + 1).factorial) ((B + 1) ^ (min m n + 1))
  have h2 := Nat.size_factorial_le (min m n + 1)
  have h3 := Nat.size_pow_le (B + 1) (min m n + 1)
  calc ((min m n + 1).factorial * (B + 1) ^ (min m n + 1)).size
      ≤ ((min m n + 1) * (min m n + 1).size + 1) + ((min m n + 1) * (B + 1).size + 1) := by
        omega
    _ = (min m n + 1) * ((min m n + 1).size + (B + 1).size) + 2 := by
        rw [Nat.mul_add]; omega

theorem bareissInv_pivotRows_length_le {T : IntTable} {c : ℕ} {st : BareissState}
    (hinv : BareissInv T c st) : st.pivotRows.length ≤ min T.numRows T.numCols := by
  have hm : st.pivotRows.length ≤ T.numRows := by
    rw [← List.toFinset_card_of_nodup hinv.row_nodup]
    have hsub : st.pivotRows.toFinset ⊆ Finset.range T.numRows := fun r hr =>
      Finset.mem_range.mpr (hinv.row_lt r (List.mem_toFinset.mp hr))
    exact (Finset.card_le_card hsub).trans_eq (Finset.card_range T.numRows)
  have hn : st.pivotRows.length ≤ T.numCols := by
    have hC_nodup : st.pivotCols.Nodup :=
      List.Pairwise.imp (fun h => Nat.ne_of_lt h) hinv.col_strict
    rw [hinv.len_eq, ← List.toFinset_card_of_nodup hC_nodup]
    have hsub : st.pivotCols.toFinset ⊆ Finset.range T.numCols := fun col hcol =>
      Finset.mem_range.mpr (hinv.col_dim col (List.mem_toFinset.mp hcol))
    exact (Finset.card_le_card hsub).trans_eq (Finset.card_range T.numCols)
  exact Nat.le_min.mpr ⟨hm, hn⟩

/-- Every entry and pivot determinant in any state satisfying `BareissInv T c st` is bounded in
magnitude by `stageEntryBound T.numRows T.numCols B`. -/
theorem bareissInv_entry_bound {T : IntTable} {c : ℕ} {st : BareissState}
    (hinv : BareissInv T c st) {B : ℕ} (hB : ∀ i : Fin T.numRows, ∀ j : Fin T.numCols,
      |T.toMatrix i j| ≤ B) :
    (∀ i : Fin T.numRows, ∀ j : Fin T.numCols,
      |st.table.entry i.val j.val| ≤ (stageEntryBound T.numRows T.numCols B : ℤ)) ∧
      |st.pivotDet| ≤ (stageEntryBound T.numRows T.numCols B : ℤ) := by
  have hk_le : st.pivotRows.length ≤ min T.numRows T.numCols :=
    bareissInv_pivotRows_length_le hinv
  have hS_inj : Function.Injective (finSel st.pivotRows rfl hinv.row_lt) := by
    intro a₁ a₂ ha
    have hinj := List.nodup_iff_injective_getElem.mp hinv.row_nodup
    exact hinj (congrArg Fin.val ha)
  have hmono_k : ((st.pivotRows.length + 1).factorial * (B + 1) ^ (st.pivotRows.length + 1) : ℕ) ≤
      stageEntryBound T.numRows T.numCols B :=
    Nat.mul_le_mul (Nat.factorial_le (Nat.add_le_add_right hk_le 1))
      (Nat.pow_le_pow_right (Nat.succ_pos B) (Nat.add_le_add_right hk_le 1))
  constructor
  · intro i j
    rw [hinv.table_eq i j]
    have hle := Matrix.abs_bareissMatrix_le T.toMatrix hB hS_inj
      (finSel st.pivotCols hinv.len_eq hinv.col_dim) i j
    exact hle.trans (Int.ofNat_le.mpr hmono_k)
  · rw [hinv.pivotDet_eq]
    have hle := Matrix.abs_pivotDet_le T.toMatrix hB (finSel st.pivotRows rfl hinv.row_lt)
      (finSel st.pivotCols hinv.len_eq hinv.col_dim)
    have hmono : st.pivotRows.length.factorial * B ^ st.pivotRows.length ≤
        stageEntryBound T.numRows T.numCols B := by
      refine Nat.mul_le_mul (Nat.factorial_le (Nat.le_trans hk_le (Nat.le_succ _))) ?_
      exact (Nat.pow_le_pow_left (Nat.le_succ B) _).trans
        (Nat.pow_le_pow_right (Nat.succ_pos B) (Nat.le_trans hk_le (Nat.le_succ _)))
    exact hle.trans (Int.ofNat_le.mpr hmono)

private theorem divInt_bounds_of_le {a Δ : ℤ} {M : ℕ} (hΔ : Δ ≠ 0)
    (ha : |a| ≤ (M : ℤ)) (hΔle : |Δ| ≤ (M : ℤ)) :
    (Rat.divInt a Δ).num.natAbs ≤ M ∧ (Rat.divInt a Δ).den ≤ M := by
  have ha' : a.natAbs ≤ M := Int.ofNat_le.mp (by simpa only [Int.natCast_natAbs] using ha)
  have hΔ' : Δ.natAbs ≤ M := Int.ofNat_le.mp (by simpa only [Int.natCast_natAbs] using hΔle)
  exact ⟨(Rat.natAbs_num_divInt_le a Δ hΔ).trans ha', (Rat.den_divInt_le a Δ hΔ).trans hΔ'⟩

/-- Every rational entry produced in `(rationalElim M).rref` and `(rationalElim M).kernelBasis` has
magnitude and denominator bounded by `stageEntryBound M.numRows M.numCols (2^((n+1)*b))`. -/
theorem rationalElim_entry_bounds (M : RatTable) {b : ℕ}
    (hb : ∀ i : Fin M.numRows, ∀ j : Fin M.numCols,
      (M.toMatrix i j).num.natAbs ≤ 2 ^ b ∧ (M.toMatrix i j).den ≤ 2 ^ b) :
    let B := stageEntryBound M.numRows M.numCols (2 ^ ((M.numCols + 1) * b))
    (∀ r ∈ (rationalElim M).rref.rows, ∀ q ∈ r, q.num.natAbs ≤ B ∧ q.den ≤ B) ∧
      (∀ v ∈ (rationalElim M).kernelBasis, ∀ q ∈ v, q.num.natAbs ≤ B ∧ q.den ≤ B) := by
  intro B
  have hinv := bareissElim_inv (clearDenoms_wellFormed M)
  have hB_cle := clearDenoms_abs_le M hb
  have hbd := bareissInv_entry_bound hinv hB_cle
  have h1B : 1 ≤ B := one_le_stageEntryBound _ _ _
  have hB0 : 0 ≤ B := Nat.zero_le B
  constructor
  · intro r hr q hq
    simp only [rationalElim, List.mem_append, List.mem_map, List.mem_replicate] at hr
    rcases hr with ⟨p, hp, rfl⟩ | ⟨_, rfl⟩
    · simp only [scaledIntRow, List.mem_map, List.mem_range] at hq
      obtain ⟨j, hj, rfl⟩ := hq
      have hp_lt := hinv.row_lt p hp
      have hj_lt : j < M.numCols := by
        have hdim : (bareissElim (clearDenoms M)).table.numCols = M.numCols := hinv.dims.2
        omega
      exact divInt_bounds_of_le hinv.pivotDet_ne_zero (hbd.1 ⟨p, hp_lt⟩ ⟨j, hj_lt⟩) hbd.2
    · rw [List.mem_replicate] at hq
      rcases hq with ⟨_, rfl⟩
      exact ⟨by simpa only [Rat.num_zero, Int.natAbs_zero] using hB0,
        by simpa only [Rat.den_zero] using h1B⟩
  · intro v hv q hq
    simp only [rationalElim, List.mem_map] at hv
    obtain ⟨j, hj, rfl⟩ := hv
    have hj_lt : j < M.numCols := by
      simp only [computeNonPivotCols, List.mem_filter, List.mem_range] at hj
      exact hj.1
    simp only [buildKernelVec, List.mem_map, List.mem_range] at hq
    obtain ⟨c, _, hcq⟩ := hq
    rcases hmatch : ((bareissElim (clearDenoms M)).pivotRows.zip
        (bareissElim (clearDenoms M)).pivotCols).find? (fun pc => pc.2 == c) with
      _ | ⟨p, y⟩
    · rw [hmatch] at hcq
      dsimp only at hcq
      split_ifs at hcq
      · rw [← hcq]; exact ⟨by simp only [Rat.num_one, Int.natAbs_one]; exact h1B,
          by simp only [Rat.den_one]; exact h1B⟩
      · rw [← hcq]; exact ⟨by simp only [Rat.num_zero, Int.natAbs_zero]; exact hB0,
          by simp only [Rat.den_zero]; exact h1B⟩
    · rw [hmatch] at hcq
      dsimp only at hcq
      rw [← hcq]
      have hp_mem : p ∈ (bareissElim (clearDenoms M)).pivotRows := by
        have hm := List.mem_of_find?_eq_some hmatch
        exact (List.of_mem_zip hm).1
      have hp_lt := hinv.row_lt p hp_mem
      have hneg : |-(bareissElim (clearDenoms M)).table.entry p j| ≤ (B : ℤ) := by
        rw [abs_neg]
        exact hbd.1 ⟨p, hp_lt⟩ ⟨j, hj_lt⟩
      exact divInt_bounds_of_le hinv.pivotDet_ne_zero hneg hbd.2

/-- Every entry of the canonical solution returned by `ratSolve sys` has numerator magnitude and
denominator bounded by `stageEntryBound m (n + 1) (2 ^ ((n + 2) * b))`. -/
theorem ratSolve_entry_bounds (sys : LinearSystemInput) {b : ℕ}
    (hbA : ∀ i : Fin sys.matrix.numRows, ∀ j : Fin sys.matrix.numCols,
      (sys.matrix.toMatrix i j).num.natAbs ≤ 2 ^ b ∧
      (sys.matrix.toMatrix i j).den ≤ 2 ^ b)
    (hb_rhs : ∀ i : Fin sys.matrix.numRows,
      (sys.rhs.getD i.val 0).num.natAbs ≤ 2 ^ b ∧ (sys.rhs.getD i.val 0).den ≤ 2 ^ b) :
    let B := stageEntryBound sys.matrix.numRows (sys.matrix.numCols + 1)
      (2 ^ ((sys.matrix.numCols + 2) * b))
    ∀ x, (ratSolve sys).solution = some x → ∀ q ∈ x, q.num.natAbs ≤ B ∧ q.den ≤ B := by
  intro B x hx q hq
  set augRat := augmentRatTable sys.matrix sys.rhs
  have hinv := bareissElimCols_inv (clearDenoms_wellFormed augRat)
    (colLimit := sys.matrix.numCols)
    (show sys.matrix.numCols ≤ (clearDenoms augRat).numCols by
      simp only [augRat, augmentRatTable, clearDenoms]; omega)
  have hB_aug : ∀ i : Fin augRat.numRows, ∀ j : Fin augRat.numCols,
      (augRat.toMatrix i j).num.natAbs ≤ 2 ^ b ∧ (augRat.toMatrix i j).den ≤ 2 ^ b := by
    intro i j
    rw [augmentRatTable_toMatrix_apply]
    split_ifs with hj
    · exact hbA ⟨i.val, i.isLt⟩ ⟨j.val, hj⟩
    · exact hb_rhs ⟨i.val, i.isLt⟩
  have hB_cle := clearDenoms_abs_le augRat hB_aug
  have hbd := bareissInv_entry_bound hinv hB_cle
  have h1B : 1 ≤ B := one_le_stageEntryBound _ _ _
  have hB0 : 0 ≤ B := Nat.zero_le B
  simp only [ratSolve] at hx
  split_ifs at hx with hcons
  simp only [Option.some.injEq] at hx
  subst hx
  simp only [List.mem_map, List.mem_range] at hq
  obtain ⟨c, _, hcq⟩ := hq
  rcases hmatch : ((bareissElimCols (clearDenoms augRat) sys.matrix.numCols).pivotRows.zip
      (bareissElimCols (clearDenoms augRat) sys.matrix.numCols).pivotCols).find?
      (fun pc => pc.2 == c) with _ | ⟨p, y⟩
  · rw [hmatch] at hcq
    dsimp only at hcq
    rw [← hcq]
    exact ⟨by simpa only [Rat.num_zero, Int.natAbs_zero] using hB0,
      by simpa only [Rat.den_zero] using h1B⟩
  · rw [hmatch] at hcq
    dsimp only at hcq
    rw [← hcq]
    have hp_mem : p ∈ (bareissElimCols (clearDenoms augRat) sys.matrix.numCols).pivotRows := by
      have hm := List.mem_of_find?_eq_some hmatch
      exact (List.of_mem_zip hm).1
    have hp_lt := hinv.row_lt p hp_mem
    have hcol_lt : sys.matrix.numCols < augRat.numCols := by
      simp only [augRat, augmentRatTable, Nat.lt_succ_self]
    have hB_eq : stageEntryBound augRat.numRows augRat.numCols (2 ^ ((augRat.numCols + 1) * b)) =
        B := rfl
    rw [← hB_eq]
    exact divInt_bounds_of_le hinv.pivotDet_ne_zero (hbd.1 ⟨p, hp_lt⟩ ⟨_, hcol_lt⟩) hbd.2

end Cslib.LinearAlgebra
