/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandFlat

/-!
# Shared catalogue inputs for an existing mathematical tile

## Main definitions

* `BandPreparation.tileInputBases`: the two shared band pointers of a tile in `tiles`.

## Main results

* `BandPreparation.tile_input_values`: both pointed arrays contain the corresponding
  unchanged public band encodings, in `Encoding.leafIndex` order.
* `BandPreparation.table_word_layout`: the computed forward table encodes the actual
  deterministic `Layout` table, rather than caller-supplied indexing data.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandPreparation

open Cslib.WordRAM Cslib.WordRAM.Signed
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- A tile `(rowBand,columnBand)` reads these two shared `10^L` arrays. The left pointer
depends only on its row band, and the right pointer only on its column band. -/
def tileInputBases (L m N : ℕ) (T : ℕ × ℕ) : ℕ × ℕ :=
  (catalogueAddress L m N false T.1 0, catalogueAddress L m N true T.2 0)

/-- The catalogue results returned by `runs` directly supply both inputs of every original
mathematical tile. Repeated row/column bands refer to the same stored arrays. -/
theorem tile_input_values {L m N : ℕ} (hm : m ≤ L)
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ) (y : Data 96)
    (hleft : ∀ β < numBands L m N, ∀ τ,
      y.mem (catalogueAddress L m N false β (Encoding.leafIndex τ).val) =
        encode (encodingL (bandArrayL (MaskTable.layout hm) X β) τ))
    (hright : ∀ β < numBands L m N, ∀ τ,
      y.mem (catalogueAddress L m N true β (Encoding.leafIndex τ).val) =
        encode (encodingR (bandArrayR (MaskTable.layout hm) Y β) τ))
    (T : ℕ × ℕ) (hT : T ∈ tiles L m N) (τ : Leaf L) :
    y.mem ((tileInputBases L m N T).1 + (Encoding.leafIndex τ).val) =
        encode (encodingL (bandArrayL (MaskTable.layout hm) X T.1) τ) ∧
      y.mem ((tileInputBases L m N T).2 + (Encoding.leafIndex τ).val) =
        encode (encodingR (bandArrayR (MaskTable.layout hm) Y T.2) τ) := by
  have ht : T.1 < numBands L m N ∧ T.2 < numBands L m N := by
    simpa only [tiles, Finset.mem_product, Finset.mem_range] using hT
  simpa only [tileInputBases, catalogueAddress, Nat.add_zero] using
    And.intro (hleft T.1 ht.1 τ) (hright T.2 ht.2 τ)

/-- The retained native forward words encode exactly the computed mathematical layout. -/
theorem table_word_layout {L m N : ℕ} (hm : m ≤ L) (y : Data 96)
    (hforward : ∀ gh : Fin (K0 L m) × Fin (K0 L m),
      y.mem (tableBase L m N + (MaskTable.pairRank gh).val) =
        (MaskTable.selectedMask gh).val)
    (gh : Fin (K0 L m) × Fin (K0 L m)) :
    y.mem (tableBase L m N + (MaskTable.pairRank gh).val) =
      (MaskTable.maskCode ((MaskTable.layout hm).table gh)).val := by
  rw [hforward]
  exact congrArg Fin.val (MaskTable.maskCode_maskSet (MaskTable.selectedMask gh)).symm

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandPreparation
