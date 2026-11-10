/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxBatch.InputLayout
import Mathlib.Data.Nat.Log
import CslibFrontier.Computability.WordRAM.Admission
import CslibFrontier.Foundations.Data.Nat.PowClog

/-!
# Original-input logarithmic admission for native query batches

Both source magnitude bounds and the original wanted count determine the sufficient
physical width. Neither this width nor a resource certificate is read by the code.
The same original parameters bound all words independently of wider admitted machines.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxBatch

open Cslib.WordRAM

/-- Positive physical admission determined by original header and signed-array bounds. -/
@[expose] def admissionWidth (L m t N A B : ℕ) : ℕ :=
  Nat.clog 2 (BoxQuery.magnitudeBound L A B + originalAddressBound L m t N + 1) + 3

theorem admissionWidth_pos (L m t N A B : ℕ) : 0 < admissionWidth L m t N A B := by
  unfold admissionWidth
  omega

/-- Every sufficiently wide physical machine admits all original signed and scalar bounds. -/
theorem admission_bounds {W L m t N A B : ℕ} (hW : admissionWidth L m t N A B ≤ W) :
    0 < W - 2 ∧ Fits W (originalAddressBound L m t N) ∧
      GenericRAM.Signed.Fits (W - 2) (BoxQuery.magnitudeBound L A B : ℕ) := by
  have hs : Nat.clog 2 (BoxQuery.magnitudeBound L A B + originalAddressBound L m t N + 1) ≤
      (W - 2) - 1 := by unfold admissionWidth at hW; omega
  have hmag : BoxQuery.magnitudeBound L A B < 2 ^ ((W - 2) - 1) :=
    fits_of_lt_clog_le
      (by omega : BoxQuery.magnitudeBound L A B <
        BoxQuery.magnitudeBound L A B + originalAddressBound L m t N + 1) hs
  have hw : 0 < W - 2 := by unfold admissionWidth at hW; omega
  refine ⟨hw, ?_, hw, ?_, ?_⟩
  · exact fits_of_lt_clog_le
      (by omega : originalAddressBound L m t N <
        BoxQuery.magnitudeBound L A B + originalAddressBound L m t N + 1) (by omega)
  · have hn : 0 ≤ (BoxQuery.magnitudeBound L A B : ℤ) := Int.natCast_nonneg _
    have hp : 0 ≤ (2 : ℤ) ^ ((W - 2) - 1) := by positivity
    omega
  · exact_mod_cast hmag

/-- A fixed original-input word/support envelope, independent of larger physical widths. -/
@[expose] def wordBound (L m t N A B : ℕ) : ℕ :=
  16 * (BoxQuery.magnitudeBound L A B + originalAddressBound L m t N + 1)

/-- Minimum-width data are strictly below the same original polynomial envelope. -/
theorem pow_admissionWidth_lt_wordBound (L m t N A B : ℕ) :
    2 ^ admissionWidth L m t N A B < wordBound L m t N A B := by
  let budget : ℕ := BoxQuery.magnitudeBound L A B + originalAddressBound L m t N + 1
  have h : 2 ^ Nat.clog 2 budget < 2 * budget :=
    Nat.pow_clog_lt_mul Nat.one_lt_two (Nat.succ_ne_zero _)
  change 2 ^ (Nat.clog 2 budget + 3) < 16 * budget
  rw [pow_add]
  omega

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxBatch
