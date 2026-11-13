/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module

import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.RelativeScanIndex

/-! Complete physical scanner/counter runs, including source restoration and preserved output. -/

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.RelativeScanIndex

-- Start at distance 2; one negative movement exposes a matching candidate. Both source and
-- counter heads return to zero, while the marker head stays at signed distance 1.
example : RunsBetween (machine 4)
    (initialConfig [] [true, false, false, true] [false])
    (tapesCfg [] ![[true, false, false, true], [true, true, true], [true]] 0
      ![0, 2, 0] [false, true]) 19 46 := by
  have hbits : Nat.bits 1 = [true] := by decide
  simpa [RelativeScan.evaluate, RelativeScan.initialDistance, RelativeScan.encode,
    RelativeScan.negative, RelativeScan.positive, finalConfig, hbits] using
    runsBetween [] [false] [-1, 1] 4

-- An empty source yields false, even after marker initialization; no counter digit is invented.
example : RunsBetween (machine 4) (initialConfig [] [] [])
    (tapesCfg [] ![[], [true, true, true], []] 0 ![0, 3, 0] [false]) 9 26 := by
  simpa [RelativeScan.evaluate, RelativeScan.initialDistance, RelativeScan.encode, finalConfig]
    using runsBetween [] [] [] 4

-- Entering the marker window only after the last movement does not invent a further candidate.
example : RunsBetween (machine 4) (initialConfig [] [true, false] [])
    (tapesCfg [] ![[true, false], [true, true, true], [true]] 0 ![0, 2, 0] [false]) 19 46 := by
  have hbits : Nat.bits 1 = [true] := by decide
  simpa [RelativeScan.evaluate, RelativeScan.initialDistance, RelativeScan.encode,
    RelativeScan.negative, RelativeScan.positive, finalConfig, hbits] using
    runsBetween [] [] [-1] 4

-- Starting after two preserved pairs returns absolute index3, using a counted rewind of all
-- three pairs. The earlier source cells and the old output prefix survive unchanged.
example : RunsBetween (machine 4)
    (positionedConfig [] [false, true, false, false, true, false, false, true] 2 [true, false])
    (tapesCfg [] ![[false, true, false, false, true, false, false, true],
      [true, true, true], [true, true]] 0 ![0, 2, 0] [true, false, true]) 35 78 := by
  have hbits : Nat.bits 3 = [true, true] := by decide
  simpa [RelativeScan.evaluate, RelativeScan.initialDistance, RelativeScan.encode,
    RelativeScan.negative, RelativeScan.positive, finalConfig, hbits] using
    runsBetween_fromPrefix [] [true, false] [1, 0] [-1, 1] 4

-- Exhaustion reports false but still returns the absolute frontier2, even when the last move
-- has brought the signed distance inside the window.
example : RunsBetween (machine 4) (positionedConfig [] [true, false, true, false] 1 [])
    (tapesCfg [] ![[true, false, true, false], [true, true, true], [false, true]] 0
      ![0, 2, 0] [false]) 27 62 := by
  have hbits : Nat.bits 2 = [false, true] := by decide
  simpa [RelativeScan.evaluate, RelativeScan.initialDistance, RelativeScan.encode,
    RelativeScan.negative, RelativeScan.positive, finalConfig, hbits] using
    runsBetween_fromPrefix [] [] [-1] [-1] 4

-- An immediate match at a nonzero cursor still pays to recover that cursor in binary.
example : RunsBetween (machine 3)
    (positionedConfig [] [false, true, false, false, false, true] 2 [])
    (tapesCfg [] ![[false, true, false, false, false, true], [true, true, true], [false, true]] 0
      ![0, 2, 0] [true]) 25 58 := by
  have hbits : Nat.bits 2 = [false, true] := by decide
  simpa [RelativeScan.evaluate, RelativeScan.initialDistance, RelativeScan.encode,
    RelativeScan.negative, RelativeScan.positive, finalConfig, hbits] using
    runsBetween_fromPrefix [] [] [1, 0] [1] 3
