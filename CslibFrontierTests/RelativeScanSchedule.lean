/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.RelativeScanSchedule

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.RelativeScanSchedule

private abbrev positive : MultiTapePTM.Schedule 1 4 := fun i _ => ![1, -1, 1, 0] i
private abbrev negative : MultiTapePTM.Schedule 1 4 := fun i _ => ![-1, 1, -1, 0] i
private abbrev exhausted : MultiTapePTM.Schedule 1 2 := fun i _ => ![1, -1] i
private abbrev immediate (move : SignType) : MultiTapePTM.Schedule 1 2 := fun i _ => ![move, 0] i
private abbrev singleSchedule : MultiTapePTM.Schedule 1 1 := fun _ _ => 0

/- The block is absent at interval one and reappears at interval two. The semantic endpoint
is certified from the same suffix evaluation that drives the physical scanner. -/
private theorem positive_next : MultiTapePTM.firstAfter
    (MultiTapePTM.InWindow positive 0 (MultiTapePTM.portBlock positive 0 0 0)) 0 = some 2 := by
  apply Option.map_injective Fin.val_injective
  rw [← result_index]
  decide

/- The endpoint theorem writes the absolute interval two, preserving the skipped interval,
the complete source, arbitrary host input, and the previous output prefix. -/
example : RunsBetween (RelativeScanIndex.machine 4)
    (RelativeScanIndex.positionedConfig [true, false]
      [false, true, true, false, false, true, false, false] 1 [false])
    (tapesCfg [true, false]
      ![[false, true, true, false, false, true, false, false],
        [true, true, true], [false, true]] 0 ![0, 2, 0] [false, true]) 49 106 := by
  have hcolumn : column positive 0 = [1, -1, 1, 0] := by decide
  have hresult : result positive 0 0 0 = ⟨2, 1, true⟩ := by decide
  have hbits : Nat.bits 2 = [false, true] := by decide
  simpa [hcolumn, hresult, start, positive, RelativeScan.encode,
    RelativeScan.negative, RelativeScan.positive, hbits] using
    runsBetween_of_firstAfter [true, false] [false] positive 0 2 0 0 positive_next

/- The opposite boundary uses the same scanner family and starts at its lowest marker state. -/
example : RunsBetween (RelativeScanIndex.machine 0)
    (RelativeScanIndex.positionedConfig []
      [true, false, false, true, true, false, false, false] 1 [])
    (tapesCfg [] ![[true, false, false, true, true, false, false, false],
      [true, true, true], [false, true]] 0 ![0, 0, 0] [true]) 49 106 := by
  have hcolumn : column negative 0 = [-1, 1, -1, 0] := by decide
  have hresult : result negative 0 0 2 = ⟨2, -1, true⟩ := by decide
  have hbits : Nat.bits 2 = [false, true] := by decide
  simpa [hcolumn, hresult, start, negative, RelativeScanIndex.finalConfig,
    RelativeScan.encode, RelativeScan.negative, RelativeScan.positive, hbits] using
    runsBetween [] [] negative 0 0 2

/- Entering the window only after the final movement has no later interval to report. -/
example : MultiTapePTM.firstAfter
    (MultiTapePTM.InWindow exhausted 0 (MultiTapePTM.portBlock exhausted 0 0 0)) 0 = none := by
  apply Option.map_injective Fin.val_injective
  rw [← result_index]
  decide

example : RunsBetween (RelativeScanIndex.machine 4)
    (RelativeScanIndex.positionedConfig [] [false, true, true, false] 1 [])
    (tapesCfg [] ![[false, true, true, false], [true, true, true], [false, true]]
      0 ![0, 2, 0] [false]) 29 66 := by
  have hcolumn : column exhausted 0 = [1, -1] := by decide
  have hresult : result exhausted 0 0 0 = ⟨2, 1, false⟩ := by decide
  have hbits : Nat.bits 2 = [false, true] := by decide
  simpa [hcolumn, hresult, start, exhausted, RelativeScanIndex.finalConfig,
    RelativeScan.encode, RelativeScan.negative, RelativeScan.positive, hbits] using
    runsBetween [] [] exhausted 0 0 0

/- A query at the final interval has an empty suffix. It still pays to count and rewind all
four preserved pairs, while rejecting even though the initial distance is zero. -/
example : RunsBetween (RelativeScanIndex.machine 2)
    (RelativeScanIndex.positionedConfig []
      [false, true, true, false, false, true, false, false] 4 [])
    (tapesCfg [] ![[false, true, true, false, false, true, false, false],
      [true, true, true], [false, false, true]] 0 ![0, 1, 0] [false]) 41 90 := by
  have hcolumn : column positive 0 = [1, -1, 1, 0] := by decide
  have hresult : result positive 3 0 1 = ⟨4, 0, false⟩ := by decide
  have hbits : Nat.bits 4 = [false, false, true] := by decide
  simpa [hcolumn, hresult, start, positive, RelativeScan.evaluate,
    RelativeScanIndex.finalConfig, RelativeScan.encode,
    RelativeScan.negative, RelativeScan.positive, hbits] using
    runsBetween_exact [] [] positive 3 0 1

/- Every sign of the initial displacement, including both window boundaries, accepts the
first candidate without consuming its movement. The already passed pair is still charged. -/
example (move : SignType) : RunsBetween (RelativeScanIndex.machine (start move 1))
    (RelativeScanIndex.positionedConfig []
      [RelativeScan.negative move, RelativeScan.positive move, false, false] 1 [])
    (tapesCfg [] ![[RelativeScan.negative move, RelativeScan.positive move, false, false],
      [true, true, true], [true]] 0 ![0, (move : ℤ) + 1, 0] [true]) 17 42 := by
  have hcolumn : column (immediate move) 0 = [move, 0] := by cases move <;> decide
  have hresult : result (immediate move) 0 0 1 = ⟨1, (move : ℤ), true⟩ := by
    cases move <;> decide
  have hbits : Nat.bits 1 = [true] := by decide
  have hr := runsBetween_exact [] [] (immediate move) 0 0 1
  rw [hcolumn, hresult] at hr
  cases move <;>
    simpa [start, immediate, RelativeScan.evaluate,
      RelativeScanIndex.finalConfig, RelativeScan.encode,
      RelativeScan.negative, RelativeScan.positive, hbits] using hr

/- A singleton horizon is nonempty but has no outgoing successor to its only interval. -/
example : RunsBetween (RelativeScanIndex.machine 2)
    (RelativeScanIndex.positionedConfig [] [false, false] 1 [])
    (tapesCfg [] ![[false, false], [true, true, true], [true]] 0 ![0, 1, 0] [false]) 17 42 := by
  have hcolumn : column singleSchedule 0 = [0] := by decide
  have hresult : result singleSchedule 0 0 1 = ⟨1, 0, false⟩ := by decide
  have hbits : Nat.bits 1 = [true] := by decide
  simpa [hcolumn, hresult, start, singleSchedule, RelativeScan.evaluate,
    RelativeScanIndex.finalConfig, RelativeScan.encode,
    RelativeScan.negative, RelativeScan.positive, hbits] using
    runsBetween_exact [] [] singleSchedule 0 0 1
