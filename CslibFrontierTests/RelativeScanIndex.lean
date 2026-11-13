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
