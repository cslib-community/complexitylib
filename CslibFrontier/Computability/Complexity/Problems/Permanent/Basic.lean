/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.IntBinary
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
public import Mathlib.LinearAlgebra.Matrix.Permanent
import CslibFrontier.Foundations.Data.Matrix.Permanent.ZeroOne

/-!
# Permanents of tables as counting problems

A table `A : List (List R)` is read as the square matrix `tableMatrix A` with one row and one
column per row of `A`: entry `(i, j)` is entry `j` of row `i`, and missing entries are `0`. Every
table is therefore an instance, and the matrix size is the number of rows. The counting problems
of Valiant's theorem [Valiant][Valiant1979] are the permanents of such tables: `IntPermanent`
for integer tables and `ZeroOnePermanent` for Boolean tables, read as 0/1 matrices.
`zeroOnePermanent_eq_card` counts the permutations supported on the `true` entries, that is the
perfect matchings of the bipartite graph whose biadjacency matrix is the table.

Tables are encoded row by row (`encIntTable`, `encBoolTable`), so the encoded length of an
`n × n` table is at least `n²`: a dense matrix encoding, as in the books.

## Main definitions

* `Cslib.Complexity.tableMatrix`, `Cslib.Complexity.boolTableMatrix`: tables as square matrices.
* `Cslib.Complexity.IntPermanent`, `Cslib.Complexity.ZeroOnePermanent`: their permanents.
* `Cslib.Complexity.encIntTable`, `Cslib.Complexity.encBoolTable`: dense table encodings.

## Main results

* `Cslib.Complexity.zeroOnePermanent_eq_card`: the 0/1 permanent counts permutations supported
  on `true` entries.

## References

* [L. Valiant, *The complexity of computing the permanent*][Valiant1979]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-- Integer tables, densely: the framed list of rows, each row the framed list of its entries in
binary sign-magnitude (`encIntBin`). -/
abbrev encIntTable : List (List ℤ) ↪ List Bool :=
  encList (encList encIntBin)

/-- Boolean tables, densely: the framed list of rows, each row the framed list of its bits. -/
abbrev encBoolTable : List (List Bool) ↪ List Bool :=
  encList (encList encBool)

/-- The square matrix of a table: entry `(i, j)` is entry `j` of row `i`, missing entries are `0`,
and the size is the number of rows. -/
def tableMatrix {R : Type*} [Zero R] (A : List (List R)) :
    Matrix (Fin A.length) (Fin A.length) R :=
  Matrix.of fun i j => A[i].getD j 0

/-- The 0/1 matrix of a Boolean table: entry `(i, j)` is `1` exactly when entry `j` of row `i` is
`true`; missing entries are `0`, and the size is the number of rows. -/
def boolTableMatrix (A : List (List Bool)) : Matrix (Fin A.length) (Fin A.length) ℕ :=
  Matrix.of fun i j => (A[i].getD j false).toNat

/-- The permanent of an integer table. -/
def IntPermanent (A : List (List ℤ)) : ℤ :=
  (tableMatrix A).permanent

/-- The permanent of a Boolean table, read as a 0/1 matrix. -/
def ZeroOnePermanent (A : List (List Bool)) : ℕ :=
  (boolTableMatrix A).permanent

theorem tableMatrix_apply {R : Type*} [Zero R] (A : List (List R)) (i j : Fin A.length) :
    tableMatrix A i j = A[i].getD j 0 :=
  rfl

theorem boolTableMatrix_apply (A : List (List Bool)) (i j : Fin A.length) :
    boolTableMatrix A i j = (A[i].getD j false).toNat :=
  rfl

/-- **The 0/1 permanent counts perfect matchings**: the permutations `σ` whose entries
`(i, σ i)` are all `true`. -/
theorem zeroOnePermanent_eq_card (A : List (List Bool)) :
    ZeroOnePermanent A =
      (Finset.univ.filter fun σ : Equiv.Perm (Fin A.length) =>
        ∀ i : Fin A.length, A[i].getD (σ i) false = true).card := by
  rw [ZeroOnePermanent, Matrix.permanent_eq_card_filter_of_le_one (A := boolTableMatrix A)
    fun i j => Bool.toNat_le _]
  congr 1
  ext σ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, boolTableMatrix_apply,
    Bool.toNat_eq_one]

end Cslib.Complexity
