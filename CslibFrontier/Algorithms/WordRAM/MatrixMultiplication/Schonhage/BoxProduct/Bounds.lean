/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct.FrontProgram
public import Mathlib.Data.Nat.Log
import CslibFrontier.Computability.WordRAM.Admission

/-!
# Original-input width admission for routed native box products

A binary ceiling logarithm of original magnitude and allocation envelopes admits the
whole fixed program. The threshold is data read from the original input; physical
width is never read. Minimum-width words have an explicit original-input envelope.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct

open Cslib.WordRAM

/-- Sufficient physical width derived from original dimensions, threshold and entry magnitude. -/
@[expose] def admissionWidth (L m t N Q A : ℕ) : ℕ :=
  Nat.clog 2 (magnitudeBound L A + wordBudget L m t N Q + 1) + 3

/-- Width admission is positive even for zero-size matrices and zero-magnitude entries. -/
theorem admissionWidth_pos (L m t N Q A : ℕ) : 0 < admissionWidth L m t N Q A := by
  unfold admissionWidth
  omega

/-- Original-input logarithmic admission derives all separate scalar and signed budgets. -/
theorem admission_bounds {W L m t N Q A : ℕ}
    (hW : admissionWidth L m t N Q A ≤ W) :
    0 < W - 2 ∧ magnitudeBound L A < 2 ^ ((W - 2) - 1) ∧
      Fits W (wordBudget L m t N Q) := by
  have hs : Nat.clog 2 (magnitudeBound L A + wordBudget L m t N Q + 1) ≤ (W - 2) - 1 := by
    unfold admissionWidth at hW
    omega
  refine ⟨by unfold admissionWidth at hW; omega, ?_, ?_⟩
  · exact fits_of_lt_clog_le
      (by omega : magnitudeBound L A < magnitudeBound L A + wordBudget L m t N Q + 1) hs
  · exact fits_of_lt_clog_le
      (by omega : wordBudget L m t N Q < magnitudeBound L A + wordBudget L m t N Q + 1) (by omega)

/-- Original-input word/support envelope, independent of larger admitted physical widths. -/
@[expose] def wordBound (L m t N Q A : ℕ) : ℕ :=
  16 * (magnitudeBound L A + wordBudget L m t N Q + 1)

/-- Every minimum-admission word is strictly below the same original-input envelope. -/
theorem pow_admissionWidth_lt_wordBound (L m t N Q A : ℕ) :
    2 ^ admissionWidth L m t N Q A < wordBound L m t N Q A := by
  let budget := magnitudeBound L A + wordBudget L m t N Q + 1
  have hbudget : 1 < budget := by dsimp only [budget]; unfold wordBudget; omega
  have hl : 0 < Nat.clog 2 budget := Nat.clog_pos (by decide) hbudget
  have hp := Nat.pow_pred_clog_lt_self (by decide : 1 < (2 : ℕ)) hbudget
  have he : Nat.clog 2 budget = (Nat.clog 2 budget).pred + 1 :=
    (Nat.succ_pred_eq_of_pos hl).symm
  change 2 ^ (Nat.clog 2 budget + 3) < 16 * budget
  rw [he, show (Nat.clog 2 budget).pred + 1 + 3 = (Nat.clog 2 budget).pred + 4 by omega,
    pow_add]
  norm_num only [pow_succ, pow_zero, Nat.reduceMul] at *
  omega

set_option maxRecDepth 8192 in
-- This closed structural check traverses both fixed producer/router/box program trees.
/-- Complete native code, including halt, has constant size independently of all inputs. -/
theorem program_size_le (bits : Bool) : (program bits).size + 1 ≤ 32768 := by
  cases bits <;> decide +kernel

set_option maxRecDepth 8192 in
-- This is a finite syntactic check of the actual renamed kernels in the fixed program.
/-- Neither input mode reads physical width. -/
theorem not_readsWidth (bits : Bool) : ¬(program bits).ReadsWidth := by
  cases bits <;> decide +kernel

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct
