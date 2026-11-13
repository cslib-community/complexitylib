/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.RelativeScanDispatch

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.RelativeScanDispatch

/- A positive current movement puts port zero outside the window. The dispatcher must read
the source pair: selecting the stationary-movement branch would incorrectly return index one. -/
example : RunsBetween (machine 0)
    (RelativeScanIndex.positionedConfig [true] [false, true, true, false, false, false] 0 [false])
    (tapesCfg [true] ![[false, true, true, false, false, false],
      [true, true, true], [false, true]] 0 ![0, 2, 0] [false, true]) 29 90 := by
  have hbits : Nat.bits 2 = [false, true] := by decide
  simpa [RelativeScan.evaluate, RelativeScanIndex.finalConfig, RelativeScan.encode,
    RelativeScan.negative, RelativeScan.positive, hbits] using
    runsBetween_fromPrefix [true] [false] [] [-1, 0] 1 0

/- The negative boundary selects the opposite marker state, using the same three-tape machine. -/
example : RunsBetween (machine 2)
    (RelativeScanIndex.positionedConfig [] [true, false, false, true, false, false] 0 [])
    (tapesCfg [] ![[true, false, false, true, false, false],
      [true, true, true], [false, true]] 0 ![0, 0, 0] [true]) 29 90 := by
  have hbits : Nat.bits 2 = [false, true] := by decide
  simpa [RelativeScan.evaluate, RelativeScanIndex.finalConfig, RelativeScan.encode,
    RelativeScan.negative, RelativeScan.positive, hbits] using
    runsBetween_fromPrefix [] [] [] [1, 0] (-1) 2

/- Entering the window only on the final movement exhausts the candidate list. -/
example : RunsBetween (machine 0)
    (RelativeScanIndex.positionedConfig [] [false, true, true, false] 0 [])
    (tapesCfg [] ![[false, true, true, false], [true, true, true], [false, true]]
      0 ![0, 2, 0] [false]) 29 90 := by
  have hbits : Nat.bits 2 = [false, true] := by decide
  simpa [RelativeScan.evaluate, RelativeScanIndex.finalConfig, RelativeScan.encode,
    RelativeScan.negative, RelativeScan.positive, hbits] using
    runsBetween_fromPrefix [] [] [] [-1] 1 0

/- A final-interval query still reads its actual pair and counts every preceding pair. -/
example : RunsBetween (machine 1)
    (RelativeScanIndex.positionedConfig [] [false, true, true, false, false, false] 2 [])
    (tapesCfg [] ![[false, true, true, false, false, false],
      [true, true, true], [true, true]] 0 ![0, 1, 0] [false]) 35 108 := by
  have hbits : Nat.bits 3 = [true, true] := by decide
  simpa [RelativeScan.evaluate, RelativeScanIndex.finalConfig, RelativeScan.encode,
    RelativeScan.negative, RelativeScan.positive, hbits] using
    runsBetween_fromPrefix [] [] [1, -1] [] 0 1
