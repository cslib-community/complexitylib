/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.RawScheduleEndpoint

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.RawScheduleEndpoint

private def positive : MultiTapePTM.Schedule 1 3 := fun i head =>
  match head with
  | none => 0
  | some _ => ![1, -1, 0] i

private def positioned : MultiTapePTM.Schedule 1 4 := fun i head =>
  match head with
  | none => -1
  | some _ => ![0, 1, -1, 0] i

private def exhausted : MultiTapePTM.Schedule 2 2 := fun i head =>
  match head with
  | none => -1
  | some h => if h = 0 then ![1, -1] i else 0

/- The query starts with only the raw table and runtime index. A positive current movement
forces the scan past interval one; all five final tapes and heads are checked explicitly. -/
example : RunsBetween (machine (0 : Fin 1) 0)
    (initialConfig [true, false]
      [false, false, false, true, false, false, true, false, false, false, false, false]
      [] [true])
    (tapesCfg [true, false] ![[false, true, true, false, false, false],
      [true, true, true], [false, true],
      [false, false, false, true, false, false, true, false, false, false, false, false], []]
      0 ![0, 2, 0, 0, 0] [true, true]) 122 226 := by
  have hw : word positive =
      [false, false, false, true, false, false, true, false, false, false, false, false] :=
    by decide
  have hc : RelativeScanSchedule.column positive 0 = [1, -1, 0] := by decide
  have hr : RelativeScanSchedule.result positive 0 0 0 = ⟨2, 1, true⟩ := by decide
  have hb : Nat.bits 2 = [false, true] := by decide
  simpa [hw, hc, hr, finalConfig, RelativeScan.encode,
    RelativeScan.negative, RelativeScan.positive, hb] using
    runsBetween [true, false] [true] positive 0 0 0

/- The nonzero runtime index is consumed and cleared by positioning; source movement differs
from the input-head movement, so selecting the wrong column or fixed start changes the result. -/
example : RunsBetween (machine (0 : Fin 1) 0)
    (initialConfig []
      [true, false, false, false, true, false, false, true,
        true, false, true, false, true, false, false, false] [true] [])
    (tapesCfg [] ![[false, false, false, true, true, false, false, false],
      [true, true, true], [true, true],
      [true, false, false, false, true, false, false, true,
        true, false, true, false, true, false, false, false], []]
      0 ![0, 2, 0, 0, 0] [true]) 166 316 := by
  have hw : word positioned =
      [true, false, false, false, true, false, false, true,
        true, false, true, false, true, false, false, false] := by decide
  have hc : RelativeScanSchedule.column positioned 0 = [0, 1, -1, 0] := by decide
  have hr : RelativeScanSchedule.result positioned 1 0 0 = ⟨3, 1, true⟩ := by decide
  have hb₁ : Nat.bits 1 = [true] := by decide
  have hb₃ : Nat.bits 3 = [true, true] := by decide
  simpa [hw, hc, hr, finalConfig, RelativeScan.encode,
    RelativeScan.negative, RelativeScan.positive, hb₁, hb₃] using
    runsBetween [] [] positioned 1 0 0

/- A middle column of a wider table exhausts: reaching the window after its final movement
does not create a successor interval. The raw table and marker remain visible at return. -/
example : RunsBetween (machine (0 : Fin 2) 0)
    (initialConfig []
      [true, false, false, true, false, false, true, false, true, false, false, false] [] [])
    (tapesCfg [] ![[false, true, true, false], [true, true, true], [false, true],
      [true, false, false, true, false, false, true, false, true, false, false, false], []]
      0 ![0, 2, 0, 0, 0] [false]) 110 192 := by
  have hw : word exhausted =
      [true, false, false, true, false, false, true, false, true, false, false, false] :=
    by decide
  have hc : RelativeScanSchedule.column exhausted 0 = [1, -1] := by decide
  have hr : RelativeScanSchedule.result exhausted 0 0 0 = ⟨2, 1, false⟩ := by decide
  have hb : Nat.bits 2 = [false, true] := by decide
  simpa [hw, hc, hr, finalConfig, RelativeScan.encode,
    RelativeScan.negative, RelativeScan.positive, hb] using
    runsBetween [] [] exhausted 0 0 0

/- Querying the final interval positions from the two-bit runtime index and returns exhaustion,
despite its current zero movement placing the initial distance inside the window. -/
example : RunsBetween (machine (0 : Fin 1) 1)
    (initialConfig []
      [false, false, false, true, false, false, true, false, false, false, false, false]
      [false, true] [false])
    (tapesCfg [] ![[false, true, true, false, false, false],
      [true, true, true], [true, true],
      [false, false, false, true, false, false, true, false, false, false, false, false], []]
      0 ![0, 1, 0, 0, 0] [false, false]) 154 322 := by
  have hw : word positive =
      [false, false, false, true, false, false, true, false, false, false, false, false] :=
    by decide
  have hc : RelativeScanSchedule.column positive 0 = [1, -1, 0] := by decide
  have hr : RelativeScanSchedule.result positive 2 0 1 = ⟨3, 0, false⟩ := by decide
  have hb₂ : Nat.bits 2 = [false, true] := by decide
  have hb₃ : Nat.bits 3 = [true, true] := by decide
  simpa [hw, hc, hr, finalConfig, RelativeScan.encode,
    RelativeScan.negative, RelativeScan.positive, hb₂, hb₃] using
    runsBetween [] [false] positive 2 0 1
