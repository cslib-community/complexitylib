/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct.Admission
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Product.Input
import Mathlib.Data.List.GetD

/-!
# Original matrix, coordinate and threshold input for a box product

The existing four headers, both original matrices and coordinate occurrences retain
their input addresses. One final word contains the ordinary box threshold. The actual
program reads that word before either producer reuses the original low-memory payload.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct

open Cslib.WordRAM Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Original matrix/coordinate words, followed by one ordinary threshold word. -/
@[expose] def input {m N : ℕ} (bits : Bool) (L t : ℕ)
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ)
    (qs : List (Fin N × Fin N)) : List ℕ := QueriedProduct.input bits L X Y qs ++ [t]

/-- Every original word, including the threshold and native length header, has this extent. -/
theorem input_length {m N : ℕ} (bits : Bool) (L t : ℕ)
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ)
    (qs : List (Fin N × Fin N)) :
    (input bits L t X Y qs).length = QueriedProduct.inputEnd m N qs.length := by
  simpa only [input, List.length_append, List.length_singleton] using
    QueriedProduct.input_length bits L X Y qs

/-- Appending the threshold preserves every original positive-address matrix/coordinate word.
Address zero instead records the new literal input length. -/
theorem input_prefix {L m t N : ℕ} (bits : Bool)
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ)
    (qs : List (Fin N × Fin N)) (p : ℕ) (hp : 0 < p)
    (hbound : p < QueriedProduct.inputEnd m N qs.length) :
    (State.init (input bits L t X Y qs) : State 160).data.mem p =
      (State.init (QueriedProduct.input bits L X Y qs) : State 160).data.mem p := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : p ≠ 0)
  change (Data.init (input bits L t X Y qs) : Data 160).mem (k + 1) = _
  rw [Data.init_mem_succ]
  change (QueriedProduct.input bits L X Y qs ++ [t]).getD k 0 =
    (Data.init (QueriedProduct.input bits L X Y qs) : Data 160).mem (k + 1)
  rw [Data.init_mem_succ]
  exact List.getD_append _ _ _ _ (by
    have := QueriedProduct.input_length bits L X Y qs
    omega)

/-- The final original word contains precisely the supplied threshold. -/
theorem input_threshold {L m t N : ℕ} (bits : Bool)
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ)
    (qs : List (Fin N × Fin N)) :
    (State.init (input bits L t X Y qs) : State 160).data.mem
      (QueriedProduct.inputEnd m N qs.length) = t := by
  rw [← QueriedProduct.input_length bits L X Y qs]
  change (Data.init (input bits L t X Y qs) : Data 160).mem
    ((QueriedProduct.input bits L X Y qs).length + 1) = t
  rw [Data.init_mem_succ]
  simp [input]

/-- All original words fit from original dimensions, threshold and entry magnitudes. -/
theorem input_fits {w L m t N A : ℕ} (hw : 0 < w) (hm : m ≤ L) (bits : Bool)
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ)
    (qs : List (Fin N × Fin N)) (hX : ∀ i k, |X i k| ≤ (A : ℤ))
    (hY : ∀ k j, |Y k j| ≤ (A : ℤ)) (hmag : magnitudeBound L A < 2 ^ (w - 1))
    (hfit : Fits (w + 2) (wordBudget L m t N qs.length)) :
    InputFits (w + 2) (input bits L t X Y qs) := by
  have hold := QueriedProduct.input_fits hw hm bits X Y qs hX hY
    (old_magnitude hmag) (old_fits hfit)
  constructor
  · rw [input_length]
    exact hfit.of_le (by unfold wordBudget QueriedProduct.wordBudget; omega)
  · intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact hold.2 v hv
    · have hv' : v = t := by simpa only [List.mem_singleton] using hv
      subst v
      exact hfit.of_le (by unfold wordBudget; omega)

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct
