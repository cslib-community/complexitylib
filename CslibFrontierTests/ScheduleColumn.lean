/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.ScheduleColumn

/-! Physical column extraction exercises first/last columns and empty prefix/suffix fields. -/

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.ScheduleColumn

private def firstRow : Option (Fin 1) → SignType
  | none => -1
  | some _ => 1

private def secondRow : Option (Fin 1) → SignType
  | none => 0
  | some _ => -1

-- Extract the input-head column. The complete source, existing output, and all head positions
-- are present in the certificate; the adapter tape is blank at the end.
example : RunsBetween (machine (0 : Fin 2))
    (tapesCfg [false] ![[], [true, false, false, true, false, false, true, false], []] 0 0 [true])
    (tapesCfg [false] ![[true, false, false, false],
      [true, false, false, true, false, false, true, false], []] 0 0 [true]) 50 42 := by
  simpa [ScheduleBits.rows, ScheduleBits.row, ScheduleBits.column, ScheduleBits.head,
    firstRow, secondRow, RelativeScan.encode, RelativeScan.negative, RelativeScan.positive]
    using runsBetween (0 : Fin 2) [false] [true] [firstRow, secondRow]

-- The last work-head column has no row suffix; the finite controller must restart immediately.
example : RunsBetween (machine (1 : Fin 2))
    (tapesCfg [] ![[], [true, false, false, true, false, false, true, false], []] 0 0 [])
    (tapesCfg [] ![[false, true, true, false],
      [true, false, false, true, false, false, true, false], []] 0 0 []) 50 42 := by
  have hc : ScheduleBits.column (1 : Fin 2) [firstRow, secondRow] =
      [false, true, true, false] := by decide
  simpa [hc, ScheduleBits.rows, ScheduleBits.row, ScheduleBits.head,
    firstRow, secondRow, RelativeScan.encode, RelativeScan.negative, RelativeScan.positive]
    using runsBetween (1 : Fin 2) [] [] [firstRow, secondRow]

-- With no work heads, both skip fields have width zero and the sole input column is copied.
example : RunsBetween (machine (0 : Fin 1))
    (tapesCfg [] ![[], [false, false], []] 0 0 [])
    (tapesCfg [] ![[false, false], [false, false], []] 0 0 []) 24 26 := by
  simpa [ScheduleBits.rows, ScheduleBits.row, ScheduleBits.column, ScheduleBits.head,
    RelativeScan.encode, RelativeScan.negative, RelativeScan.positive]
    using runsBetween (0 : Fin 1) [] [] [fun _ => (0 : SignType)]

-- Empty schedules still pay initialization and restoration; no column cells are produced.
example : RunsBetween (machine (1 : Fin 2))
    (tapesCfg [] ![[], [], []] 0 0 [false]) (tapesCfg [] ![[], [], []] 0 0 [false]) 14 18 := by
  simpa [ScheduleBits.rows, ScheduleBits.column, RelativeScan.encode] using
    runsBetween (1 : Fin 2) [] [false] []

private def middleRow : Option (Fin 2) → SignType
  | none => 1
  | some i => if i = 0 then -1 else 0

-- A middle column has nonempty skip fields on both sides. Two rows exercise the restart from
-- the suffix phase to the next row's nonempty prefix phase.
example : RunsBetween (machine (1 : Fin 3))
    (tapesCfg [] ![[], [false, true, true, false, false, false,
      false, true, true, false, false, false], []] 0 0 [false])
    (tapesCfg [] ![[true, false, true, false], [false, true, true, false, false, false,
      false, true, true, false, false, false], []] 0 0 [false]) 66 50 := by
  have hc : ScheduleBits.column (1 : Fin 3) [middleRow, middleRow] =
      [true, false, true, false] := by decide
  simpa [hc, ScheduleBits.rows, ScheduleBits.row, ScheduleBits.head, middleRow,
    RelativeScan.encode, RelativeScan.negative, RelativeScan.positive]
    using runsBetween (1 : Fin 3) [] [false] [middleRow, middleRow]
