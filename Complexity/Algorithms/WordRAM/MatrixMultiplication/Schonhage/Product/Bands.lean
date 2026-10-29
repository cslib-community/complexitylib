/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Product.Admission
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Product.Memory
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandFlat

/-!
# Running the actual shared catalogue producer in the product caller

## Main results

* `QueriedProduct.exec_bands`: invoke the complete actual band/encoding program in the low bank,
  yielding the unchanged mathematical `encodingL/R` arrays and preserving the caller's scalars.

The input memory equations are discharged by the preceding charged matrix adaptation.
No encoded catalogue, subset layout or producer execution is supplied to the program.
-/

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- The actual native producer computes every shared band encoding, once per band.
Its complete outside frame protects the caller's original input and saved routing arrays. -/
public theorem exec_bands {w L m N Q A : ℕ} (hw : 0 < w) (hm : m ≤ L)
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ)
    (x : Data 160) (hp : Parameters L m N Q x)
    (hL : x.mem 1 = L) (hmemory : x.mem 2 = m) (hN : x.mem 3 = N)
    (hmat : ∀ side r, r < N → ∀ k, k < D m →
      x.mem (BandPreparation.matrixOffset m N side r k + 4) =
        Signed.encode (BandPreparation.matrixValues X Y side r k))
    (hX : ∀ i k, |X i k| ≤ (A : ℤ)) (hY : ∀ k j, |Y k j| ≤ (A : ℤ))
    (hmag : magnitudeBound L A < 2 ^ (w - 1))
    (hfit : Fits (w + 2) (wordBudget L m N Q)) :
    ∃ y, ExecWithin (w + 2) (BandPreparation.program.rename bank) x y
        (BandPreparation.timeBound L m N) ∧ Parameters L m N Q y ∧
      (∀ β < numBands L m N, ∀ τ,
        y.mem (BandPreparation.catalogueAddress L m N false β (Encoding.leafIndex τ).val) =
          Signed.encode (encodingL (bandArrayL (MaskTable.layout hm) X β) τ)) ∧
      (∀ β < numBands L m N, ∀ τ,
        y.mem (BandPreparation.catalogueAddress L m N true β (Encoding.leafIndex τ).val) =
          Signed.encode (encodingR (bandArrayR (MaskTable.layout hm) Y β) τ)) ∧
      (∀ a, a < BandPreparation.inputEnd m N ∨ BandPreparation.memoryEnd L m N ≤ a →
        y.mem a = x.mem a) := by
  have hbound (side : Bool) (r : ℕ) (hr : r < N) (k : ℕ) (hk : k < D m) :
      |BandPreparation.matrixValues X Y side r k| ≤ (A : ℤ) := by
    cases side <;>
      simp only [BandPreparation.matrixValues, dite_eq_left hr, dite_eq_left hk,
        Bool.false_eq_true, ↓reduceIte]
    · exact hX _ _
    · exact hY _ _
  obtain ⟨z, he, _, hv, _, _, hf⟩ := BandPreparation.exec hw hm (x.comap bank) hL hmemory hN
    (BandPreparation.matrixValues X Y) hmat (A : ℤ) (by positivity) hbound
    (magnitude_admissions hw hmag).1 (producer_fits hfit).1
  let y := z.extend bank x
  have hframe (i : Fin 160) (hi : 96 ≤ i.val) : y.regs i = x.regs i := by
    have hnot : ¬∃ j, bank j = i := by
      rintro ⟨j, hj⟩
      have hv := congrArg (fun r : Fin 160 => r.val) hj
      change j.val = i.val at hv
      omega
    exact Function.extend_apply' _ _ _ hnot
  refine ⟨y, he.rename bank_injective, hp.reframe hframe, ?_, ?_, ?_⟩
  · intro β hβ τ
    change z.mem _ = _
    simpa only [BandPreparation.catalogueValue_left hm X (BandPreparation.matrixValues X Y false)
      (by intro i k; simp [BandPreparation.matrixValues])] using
        hv false β hβ (Encoding.leafIndex τ).val (Encoding.leafIndex τ).isLt
  · intro β hβ τ
    change z.mem _ = _
    simpa only [BandPreparation.catalogueValue_right hm Y (BandPreparation.matrixValues X Y true)
      (by intro k i; simp [BandPreparation.matrixValues])] using
        hv true β hβ (Encoding.leafIndex τ).val (Encoding.leafIndex τ).isLt
  · intro a ha
    exact hf a (by rcases ha with ha | ha <;> omega)

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct
