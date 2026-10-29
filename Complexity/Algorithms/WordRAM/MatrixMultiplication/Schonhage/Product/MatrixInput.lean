/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Product.MatrixTransfer
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Product.Admission

/-!
# Original matrices through the actual native input adapter

## Main results

* `QueriedProduct.exec_prepareInputMatrices`: real signed copies or raw-entry doubling
  establish the exact input words required by the existing band producer.

The source-word equalities come from the preceding native original-input snapshot. The
raw path represents nonnegative entries, including the ET frontend's raw zero/one matrices.
-/

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Every original matrix entry reaches the producer in its canonical signed convention.
The instruction envelope includes the actual conversion at every raw input entry. -/
public theorem exec_prepareInputMatrices {w L m N A : ℕ} (hw : 0 < w) (bits : Bool)
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ)
    (qs : List (Fin N × Fin N)) (x : Data 160) (hp : Parameters L m N qs.length x)
    (hsource : ∀ j < 2 * (N * D m), x.mem (snapshotBase L m N qs.length + 5 + j) =
      (State.init (input bits L X Y qs) : State 160).data.mem (5 + j))
    (hX : ∀ i k, |X i k| ≤ (A : ℤ)) (hY : ∀ k j, |Y k j| ≤ (A : ℤ))
    (hbits : bits = true → (∀ i k, 0 ≤ X i k) ∧ (∀ k j, 0 ≤ Y k j))
    (hmag : magnitudeBound L A < 2 ^ (w - 1))
    (hfit : Fits (w + 2) (wordBudget L m N qs.length)) :
    ∃ y, ExecWithin (w + 2) (prepareMatrices bits) x y (8 * (2 * (N * D m)) + 10) ∧
      Parameters L m N qs.length y ∧
      (∀ side r, r < N → ∀ k, k < D m →
        y.mem (BandPreparation.matrixOffset m N side r k + 4) =
          Signed.encode (BandPreparation.matrixValues X Y side r k)) ∧
      (∀ a, a < 4 ∨ 4 + 2 * (N * D m) ≤ a → y.mem a = x.mem a) := by
  obtain ⟨y, he, yp, hy, hf⟩ :
      ∃ y, ExecWithin (w + 2) (prepareMatrices bits) x y (8 * (2 * (N * D m)) + 10) ∧
        Parameters L m N qs.length y ∧
        (∀ j < 2 * (N * D m), y.mem (4 + j) =
          if bits then 2 * x.mem (snapshotBase L m N qs.length + 5 + j)
            else x.mem (snapshotBase L m N qs.length + 5 + j)) ∧
        (∀ a, a < 4 ∨ 4 + 2 * (N * D m) ≤ a → y.mem a = x.mem a) := by
    cases bits
    · obtain ⟨y, he, yp, hy, hf⟩ := exec_prepareSigned x hp hfit
      exact ⟨y, he.mono (by omega), yp, hy, hf⟩
    · obtain ⟨y, he, yp, hy, hf⟩ := exec_prepareBits x hp hfit
        (magnitude_admissions hw hmag).2.2 (by
          intro j hj
          rw [hsource j hj]
          exact input_raw_matrix_le X Y qs hX hY j hj)
      exact ⟨y, he.mono (by omega), yp, hy, hf⟩
  refine ⟨y, he, yp, ?_, hf⟩
  intro side r hr k hk
  have hindex := BandPreparation.matrixAddress_lt_inverse (L := L) side hr hk
  unfold BandPreparation.matrixAddress BandPreparation.inverseBase
    BandPreparation.inputEnd at hindex
  have hi : BandPreparation.matrixOffset m N side r k < 2 * (N * D m) := by omega
  have hv := input_matrix_word (L := L) bits X Y qs side r k hr hk
  rw [show BandPreparation.matrixOffset m N side r k + 4 =
      4 + BandPreparation.matrixOffset m N side r k by omega, hy _ hi, hsource _ hi,
    show 5 + BandPreparation.matrixOffset m N side r k =
      BandPreparation.matrixOffset m N side r k + 5 by omega, hv]
  exact convert_entryWord bits _ (by
    intro hb
    have hnonneg := hbits hb
    cases side <;>
      simp only [BandPreparation.matrixValues, dite_eq_left hr, dite_eq_left hk,
        Bool.false_eq_true, ↓reduceIte]
    · exact hnonneg.1 _ _
    · exact hnonneg.2 _ _)

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct
