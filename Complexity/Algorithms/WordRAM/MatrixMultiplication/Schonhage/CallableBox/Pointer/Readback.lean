/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.CallableBox.Pointer.Gather

/-!
# Physical snapshot readback and exact gather frame

These facts describe the four executed copy destinations. Source/source aliases are allowed;
only separation from the private destination is used. No unused memory is constrained.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PointerBoxProduct

open Cslib.WordRAM

/-- The physical gather writes only the complete snapshot interval. -/
theorem gatherMemory_outside (mem : ℕ → ℕ) (b S A Q s t q a : ℕ)
    (ha : a < b + S ∨ b + S + 5 + 2 * A + 2 * Q ≤ a) :
    gatherMemory mem b S A Q s t q a = mem a := by
  unfold gatherMemory
  rw [ArrayCopy.copyPrefix_outside (by omega), ArrayCopy.copyPrefix_outside (by omega),
    ArrayCopy.copyPrefix_outside (by omega), ArrayCopy.copyPrefix_outside (by omega)]

/-- Actual source readback determines every gathered word, including repeated coordinates. -/
theorem gatherMemory_readback (mem original : ℕ → ℕ) (b S A Q s t q : ℕ)
    (hS : 5 ≤ S) (hs : s + A ≤ b) (ht : t + A ≤ b) (hq : q + 2 * Q ≤ b)
    (hheader : ∀ j < 5, mem (b + j) = original j)
    (hleft : ∀ j < A, mem (s + j) = original (5 + j))
    (hright : ∀ j < A, mem (t + j) = original (5 + A + j))
    (hqueries : ∀ j < 2 * Q, mem (q + j) = original (5 + 2 * A + j))
    (j : ℕ) (hj : j < 5 + 2 * A + 2 * Q) :
    gatherMemory mem b S A Q s t q (b + S + j) = original j := by
  unfold gatherMemory
  by_cases h0 : j < 5
  · rw [ArrayCopy.copyPrefix_outside (by omega), ArrayCopy.copyPrefix_outside (by omega),
      ArrayCopy.copyPrefix_outside (by omega), ArrayCopy.copyPrefix_read h0]
    exact hheader j h0
  · by_cases h1 : j < 5 + A
    · rw [ArrayCopy.copyPrefix_outside (by omega), ArrayCopy.copyPrefix_outside (by omega),
        show b + S + j = b + S + 5 + (j - 5) by omega,
        ArrayCopy.copyPrefix_read (show j - 5 < A by omega),
        ArrayCopy.copyPrefix_outside (by omega)]
      simpa only [show 5 + (j - 5) = j by omega] using hleft (j - 5) (by omega)
    · by_cases h2 : j < 5 + 2 * A
      · rw [ArrayCopy.copyPrefix_outside (by omega),
          show b + S + j = b + S + 5 + A + (j - (5 + A)) by omega,
          ArrayCopy.copyPrefix_read (show j - (5 + A) < A by omega),
          ArrayCopy.copyPrefix_outside (by omega), ArrayCopy.copyPrefix_outside (by omega)]
        simpa only [show 5 + A + (j - (5 + A)) = j by omega] using
          hright (j - (5 + A)) (by omega)
      · rw [show b + S + j = b + S + 5 + 2 * A + (j - (5 + 2 * A)) by omega,
          ArrayCopy.copyPrefix_read (show j - (5 + 2 * A) < 2 * Q by omega),
          ArrayCopy.copyPrefix_outside (by omega), ArrayCopy.copyPrefix_outside (by omega),
          ArrayCopy.copyPrefix_outside (by omega)]
        simpa only [show 5 + 2 * A + (j - (5 + 2 * A)) = j by omega] using
          hqueries (j - (5 + 2 * A)) (by omega)

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PointerBoxProduct
