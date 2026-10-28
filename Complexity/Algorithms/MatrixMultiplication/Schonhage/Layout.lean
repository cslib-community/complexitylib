/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.MatrixMultiplication.Schonhage.Levels
public import Mathlib.Data.Nat.Sqrt

/-!
# Tiling layout data

## Main definitions

* `Layout`: index equivalences and an injective assignment of level sets to block pairs.
* `wantedStrings`, `tiles`: requested outputs grouped by tile.

## References

Adapted selectively from [AlmanWilliams2026, Section 2] and
[Anthropic's pinned formal source](https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Sec2).
Source pin: `16a5ce41304fcdaea4e0be7c132e1c361dc26da5`. These are finite mathematical
counts and identities; they give no native program or instruction-cost certificate.
-/

@[expose] public section

open Finset

namespace Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- The natural square root of the number `K L m` of size-`m` level sets. -/
def K0 (L m : ℕ) : ℕ := Nat.sqrt (K L m)

/-- `N₀ = 3^{L-m}` is positive. -/
theorem N0_pos (L m : ℕ) : 0 < N0 L m := Nat.pow_pos (by decide)

/-- `K₀ = ⌊√binom(L, m)⌋` is positive when `m ≤ L`. -/
theorem K0_pos {L m : ℕ} (h : m ≤ L) : 0 < K0 L m := Nat.sqrt_pos.mpr (Nat.choose_pos h)

/-- Indexing data for the block decomposition, under `m ≤ L`.

The three equivalences identify block rows, block columns and the thin dimension with
their string indices. The injective `table` assigns a size-`m` subset of `Fin L` to each
pair of block indices in a tile. All tiles use this same table. The structure contains no
matrix values or solver certificate; the correctness results hold for any such indexing
choices. -/
structure Layout (L m : ℕ) where
  hmL : m ≤ L
  /-- Index a block's rows by outer strings. -/
  rowIdx : Fin (N0 L m) ≃ OuterStr L m
  /-- Index a block's columns by outer strings. -/
  colIdx : Fin (N0 L m) ≃ OuterStr L m
  /-- Index the thin matrix dimension by strings of inner index pairs. -/
  innerIdx : Fin (D m) ≃ InnerStr m
  /-- Assign a distinct size-`m` level set to each block product in a tile. -/
  table : Fin (K0 L m) × Fin (K0 L m) → Finset (Fin L)
  table_card : ∀ gh, (table gh).card = m
  table_injective : Function.Injective table

/-- The common band dimension `K0 L m * N0 L m`: each band contains `K0 L m` consecutive
blocks of size `N0 L m`. -/
def bandSize (L m : ℕ) : ℕ := K0 L m * N0 L m

/-- The quotient `(N + bandSize L m - 1) / bandSize L m`. When `m ≤ L`, the band size is
positive and this is the number of bands needed to cover `N` positions, including `N = 0`. -/
def numBands (L m N : ℕ) : ℕ := (N + bandSize L m - 1) / bandSize L m

/-- The dimension covered by `numBands L m N` complete bands. -/
def padN (L m N : ℕ) : ℕ := numBands L m N * bandSize L m

/-- Extend `X` to natural-number row indices by returning zero at indices `I ≥ N`. -/
def padRows {N D' : ℕ} (X : Matrix (Fin N) (Fin D') ℤ) (I : ℕ) (k : Fin D') : ℤ :=
  if h : I < N then X ⟨I, h⟩ k else 0

/-- Extend `Y` to natural-number column indices by returning zero at indices `J ≥ N`. -/
def padCols {N D' : ℕ} (Y : Matrix (Fin D') (Fin N) ℤ) (k : Fin D') (J : ℕ) : ℤ :=
  if h : J < N then Y k ⟨J, h⟩ else 0

/-- Extract the `N0 L m` rows starting at `B * N0 L m` from `padRows X`, using `lay.rowIdx`
and `lay.innerIdx` to index the resulting integer matrix by strings. -/
def rowBlock {L m N : ℕ} (lay : Layout L m) (X : Matrix (Fin N) (Fin (D m)) ℤ) (B : ℕ) :
    LeftMat L m :=
  fun r π => padRows X (B * N0 L m + lay.rowIdx.symm r) (lay.innerIdx.symm π)

/-- Extract the `N0 L m` columns starting at `B * N0 L m` from `padCols Y`, using
`lay.innerIdx` and `lay.colIdx` to index the resulting integer matrix by strings. -/
def colBlock {L m N : ℕ} (lay : Layout L m) (Y : Matrix (Fin (D m)) (Fin N) ℤ) (B : ℕ) :
    RightMat L m :=
  fun π c => padCols Y (lay.innerIdx.symm π) (B * N0 L m + lay.colIdx.symm c)

/-- For a table entry `Q = lay.table (g, h)`, select row block `β * K0 L m + g` of `X`; return
the zero matrix for sets outside the table's image. Injectivity of the table ensures that
the defining sum selects at most one matrix. -/
def bandFamilyL {L m N : ℕ} (lay : Layout L m) (X : Matrix (Fin N) (Fin (D m)) ℤ) (β : ℕ) :
    Finset (Fin L) → LeftMat L m :=
  fun Q => ∑ gh, if lay.table gh = Q then rowBlock lay X (β * K0 L m + gh.1) else 0

/-- For a table entry `Q = lay.table (g, h)`, select column block `β * K0 L m + h` of `Y`;
return the zero matrix for sets outside the table's image. -/
def bandFamilyR {L m N : ℕ} (lay : Layout L m) (Y : Matrix (Fin (D m)) (Fin N) ℤ) (β : ℕ) :
    Finset (Fin L) → RightMat L m :=
  fun Q => ∑ gh, if lay.table gh = Q then colBlock lay Y (β * K0 L m + gh.2) else 0

/-- The left batch array formed from the block family for row band `β`. -/
def bandArrayL {L m N : ℕ} (lay : Layout L m) (X : Matrix (Fin N) (Fin (D m)) ℤ) (β : ℕ) :
    LeftStr L → ℤ :=
  arrayL m (bandFamilyL lay X β)

/-- The right batch array formed from the block family for column band `β`. -/
def bandArrayR {L m N : ℕ} (lay : Layout L m) (Y : Matrix (Fin (D m)) (Fin N) ℤ) (β : ℕ) :
    RightStr L → ℤ :=
  arrayR m (bandFamilyR lay Y β)

/-- The band that contains row (or column) `I`. -/
def bandOf (L m I : ℕ) : ℕ := I / bandSize L m

/-- The position, within its band, of the block that contains row (or column) `I`. -/
def blockOf {L m : ℕ} (lay : Layout L m) (I : ℕ) : Fin (K0 L m) :=
  ⟨I / N0 L m % K0 L m, Nat.mod_lt _ (K0_pos lay.hmL)⟩

/-- The position of row (or column) `I` within its block. -/
def offsetOf (L m I : ℕ) : Fin (N0 L m) := ⟨I % N0 L m, Nat.mod_lt _ (N0_pos L m)⟩

/-- Encode the within-tile position `(I, J)` as an output string. Its inner set comes from the
table at the two block indices, and its outer indices come from the two offsets within
those blocks. The tile itself is identified separately by `(bandOf L m I, bandOf L m J)`. -/
def outStrOfPos {L m : ℕ} (lay : Layout L m) (I J : ℕ) : OutStr L :=
  outStrOf (lay.table (blockOf lay I, blockOf lay J)) (lay.table_card _)
    (lay.rowIdx (offsetOf L m I)) (lay.colIdx (offsetOf L m J))

/-- Output strings for the positions of `W` whose row band is `β` and column band is `β'`.
This is the image of the filtered position set under `outStrOfPos lay`. -/
def wantedStrings {L m N : ℕ} (lay : Layout L m) (W : Finset (Fin N × Fin N)) (β β' : ℕ) :
    Finset (OutStr L) :=
  (W.filter fun IJ => bandOf L m IJ.1 = β ∧ bandOf L m IJ.2 = β').image
    fun IJ => outStrOfPos lay IJ.1 IJ.2

/-- All the tiles: pairs of a row band and a column band. -/
def tiles (L m N : ℕ) : Finset (ℕ × ℕ) := range (numBands L m N) ×ˢ range (numBands L m N)

end Cslib.Algorithms.MatrixMultiplication.Schonhage
