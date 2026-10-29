/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Product.Bands

/-!
# Preserving the actual shared catalogue between tile calls

## Main definitions

* `QueriedProduct.EncodedBands`: the unchanged producer's mathematical encodings in real memory.

## Main results

* `QueriedProduct.EncodedBands.reframe`: retain both catalogues through a readonly low-memory frame.

This predicate contains only ordinary word equalities. `exec_bands` establishes them by
running the native producer; no execution, fit or cost assertion is bundled in the predicate.
-/

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Actual shared arrays, using the original band arrays and authoritative leaf numbering. -/
public structure EncodedBands {L m N : ℕ} (hm : m ≤ L)
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ)
    (μ : ℕ → ℕ) : Prop where
  /-- The left encoding is computed once for each row band. -/
  left : ∀ β < numBands L m N, ∀ τ,
    μ (BandPreparation.catalogueAddress L m N false β (Encoding.leafIndex τ).val) =
      Signed.encode (encodingL (bandArrayL (MaskTable.layout hm) X β) τ)
  /-- The right encoding is computed once for each column band. -/
  right : ∀ β < numBands L m N, ∀ τ,
    μ (BandPreparation.catalogueAddress L m N true β (Encoding.leafIndex τ).val) =
      Signed.encode (encodingR (bandArrayR (MaskTable.layout hm) Y β) τ)

/-- The native tile kernel's low readonly frame preserves all shared encodings. -/
public theorem EncodedBands.reframe {L m N : ℕ} {hm : m ≤ L}
    {X : Matrix (Fin N) (Fin (D m)) ℤ} {Y : Matrix (Fin (D m)) (Fin N) ℤ}
    {μ ν : ℕ → ℕ} (h : EncodedBands hm X Y μ)
    (hf : ∀ a < BandPreparation.memoryEnd L m N, ν a = μ a) : EncodedBands hm X Y ν := by
  have hread (side : Bool) (β : ℕ) (hβ : β < numBands L m N) (τ : Leaf L) :
      ν (BandPreparation.catalogueAddress L m N side β (Encoding.leafIndex τ).val) =
        μ (BandPreparation.catalogueAddress L m N side β (Encoding.leafIndex τ).val) := by
    have hb := BandPreparation.catalogue_block_le side hβ
    have ht := (Encoding.leafIndex τ).isLt
    apply hf
    unfold BandPreparation.catalogueAddress at hb ⊢
    omega
  exact ⟨fun β hβ τ => (hread false β hβ τ).trans (h.left β hβ τ),
    fun β hβ τ => (hread true β hβ τ).trans (h.right β hβ τ)⟩

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct
