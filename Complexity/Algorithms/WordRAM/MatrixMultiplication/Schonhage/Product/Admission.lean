/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Product.Input

/-!
# Deriving producer and tile-kernel admission from original inputs

## Main results

* `QueriedProduct.kernel_fits`: actual separated tile pointers and bounded fresh epochs fit
  from the single original numerical allocation envelope.
* `QueriedProduct.magnitude_admissions`: the original entry envelope covers shared encodings,
  every pruned partial sum and the actual raw-word doubling instruction.

No intermediate-state fit contract is part of the final caller's input.
-/

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct

open Cslib.WordRAM

/-- The shared original allocation bound admits every computed tile's actual pointer values.
Query counts retain occurrences; epoch bounds are established by the caller's loop invariant. -/
public theorem kernel_fits {w L m N Q a b q o n E : ℕ}
    (hfit : Fits w (wordBudget L m N Q))
    (ha : a ≤ BandPreparation.memoryEnd L m N) (hb : b ≤ BandPreparation.memoryEnd L m N)
    (hq : q ≤ codeBase L m N Q + Q) (ho : o ≤ outputBase L m N Q) (hn : n ≤ Q)
    (hE : E ≤ epochBound L m N) :
    Fits w (PrunedQuery.kernelBudget L (scratchBase L m N Q) a b q o n E) := by
  apply hfit.of_le
  unfold wordBudget PrunedQuery.kernelBudget PrunedQuery.evaluationBudget
    PrunedQuery.nodeBudget PrunedQuery.addressBound
  omega

/-- All signed and conversion admission follows from the original integer-entry magnitude.
The extra two physical bits are the existing native signed-kernel convention. -/
public theorem magnitude_admissions {w L A : ℕ} (hw : 0 < w)
    (hmag : magnitudeBound L A < 2 ^ (w - 1)) :
    (7 ^ L : ℕ) * (A : ℤ) < (2 : ℤ) ^ (w - 1) ∧
      PrunedQuery.magnitudeBound L (7 ^ L * A) (7 ^ L * A) < 2 ^ (w - 1) ∧
      Fits (w + 2) (2 * A) := by
  have hk : PrunedQuery.magnitudeBound L (7 ^ L * A) (7 ^ L * A) < 2 ^ (w - 1) := by
    unfold magnitudeBound at hmag
    omega
  have hp : 7 ^ L * A < 2 ^ (w - 1) := by
    unfold PrunedQuery.magnitudeBound at hk
    omega
  refine ⟨by exact_mod_cast hp, hk, ?_⟩
  simpa only [entryWord, Bool.false_eq_true, ↓reduceIte, Signed.encode,
    Int.natAbs_natCast, ite_eq_right (show ¬(A : ℤ) < 0 by omega), Nat.add_zero] using
    entryWord_fits hw false (A : ℤ) (by simp) hmag

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct
