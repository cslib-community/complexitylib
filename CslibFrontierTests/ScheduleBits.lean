/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.ScheduleBits

/-! Raw schedules reject invalid aligned pairs and incomplete rows. -/

open Turing.MultiTapeTM Turing.MultiTapeTM.ScheduleBits

private def firstRow : Option (Fin 1) → SignType
  | none => -1
  | some _ => 1

-- Input head first: negative input movement, then positive work-head movement.
example : row firstRow = [true, false, false, true] := by
  simp [row, firstRow, head, RelativeScan.encode, RelativeScan.negative, RelativeScan.positive]

-- Validity applies to the actual raw cells, not to a decoded packed-natural surrogate.
example : Canonical 1 [true, false, false, true] := by
  simpa [rows, row, firstRow, head, RelativeScan.encode, RelativeScan.negative,
    RelativeScan.positive] using canonical_rows [firstRow]

-- Whole-row length does not rescue the forbidden11 pair.
example : ¬ Canonical 1 [true, true, false, false] := not_canonical_true_true 1 [false, false]

-- A valid movement pair alone is incomplete when the schedule has two head columns.
example : ¬ Canonical 1 [false, false] := by simp [Canonical]

private def crossingRow : Option (Fin 1) → SignType
  | none => 1
  | some _ => -1

-- Adjacent ones crossing a pair boundary are valid: the aligned pairs are01 and10.
example : Canonical 1 [false, true, true, false] := by
  simpa [rows, row, crossingRow, head, RelativeScan.encode, RelativeScan.negative,
    RelativeScan.positive] using canonical_rows [crossingRow]
