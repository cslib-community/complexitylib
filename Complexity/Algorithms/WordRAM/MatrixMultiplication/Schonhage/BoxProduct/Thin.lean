/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct.Width
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct.Resources

/-!
# Actual native thin-product execution with the improved finite saving

The same initialized prefix, charged halt and exact original-order matrix products
satisfy the finite `D^(-8/125)` instruction bound. Original dimensions, occurrence
sparsity, entry magnitudes and sufficient width are explicit; no backend is supplied.
Polynomial depth factors remain visible, so this is not the final 3SUM exponent.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct

open Cslib.WordRAM Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- One actual initialized native product with finite `0.064` thin-dimension saving,
including the charged halt, raw conversion when selected, and complete input restoration. -/
theorem runs_thin {W k N A : ℕ} (bits : Bool)
    (X : Matrix (Fin N) (Fin (D (9 * k))) ℤ)
    (Y : Matrix (Fin (D (9 * k))) (Fin N) ℤ)
    (qs : List (Fin N × Fin N)) (hX : ∀ i j, |X i j| ≤ (A : ℤ))
    (hY : ∀ i j, |Y i j| ≤ (A : ℤ))
    (hbits : bits = true → (∀ i j, 0 ≤ X i j) ∧ (∀ i j, 0 ≤ Y i j))
    (hN : D (9 * k) ^ 18 ≤ N) (hQ : qs.length * 2 ^ (9 * k) ≤ N ^ 2)
    (hW : admissionWidth (189 * k) (9 * k) k N qs.length A ≤ W) :
    InputFits W (input bits (189 * k) k X Y qs) ∧
    ∃ y n, ((n + 1 : ℕ) : ℝ) ≤
        2621440 * ((189 * k + 1 : ℕ) : ℝ) ^ 2 * ((9 * k + 1 : ℕ) : ℝ) *
          (D (9 * k) : ℝ) ^ (-(8 / 125 : ℝ)) * (N : ℝ) ^ 2 ∧
      Runs W ((program bits).program QueriedProduct.Reg.output)
        (State.init (input bits (189 * k) k X Y qs)) ⟨(program bits).size, y⟩ n ∧
      Executes W ((program bits).program QueriedProduct.Reg.output)
        (State.init (input bits (189 * k) k X Y qs))
        (QueriedProduct.outputBase (189 * k) (9 * k) N qs.length) (n + 1) ∧
      y.Bounded W ∧
      (∀ i : Fin qs.length,
        y.mem (QueriedProduct.outputBase (189 * k) (9 * k) N qs.length + i.val) =
          Signed.encode ((X * Y) (qs.get i).1 (qs.get i).2)) ∧
      (∀ p, ¬(QueriedProduct.inputEnd (9 * k) N qs.length + 1 ≤ p ∧
        p < memoryEnd (189 * k) (9 * k) k N qs.length) →
        y.mem p = (State.init (input bits (189 * k) k X Y qs) : State 160).data.mem p) := by
  obtain ⟨hi, y, n, hn, hp, he, hy, hv, hf⟩ :=
    runs_wide (L := 189 * k) (m := 9 * k) (t := k)
      (by omega) (by omega) bits X Y qs hX hY hbits hW
  have hn' : ((n + 1 : ℕ) : ℝ) ≤ (timeBound (189 * k) (9 * k) k qs + 1 : ℕ) := by
    exact_mod_cast hn
  exact ⟨hi, y, n, hn'.trans (thin_timeBound_rpow k N qs hN hQ), hp, he, hy, hv, hf⟩

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct
