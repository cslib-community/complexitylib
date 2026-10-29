/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

-- upstream: local-only (tests)

import Complexity.Algorithms.WordRAM.ExactTriangle.RecordWitness.Consume

/-!
# Actual candidate-consumer executions at valid thin geometry

These sparse-memory fixtures execute the full descriptor/root/query/verifier consumer at
`D=16`, `n=16^18`. They supply a post-product memory fixture, not a full producer/product run.
The initialized composition client is separate. No enormous encoder run is evaluated here.
-/

set_option linter.hashCommand false

namespace ComplexityTests.WordRAMExactTriangleRecordWitness

open Cslib.WordRAM Cslib.Algorithms.WordRAM.ExactTriangle

private def side : ℕ := 16 ^ 18
private def queryBase : ℕ := 8 + 6 * (side * side)
private def records : ℕ := 23 + 12 * (side * side)
private def heap : ℕ := records + 6 + 2 * (side * 16)
private def answers : ℕ := heap + 100

private def fixture (success zeroAnswers : Bool) : Data 400 :=
  { regs := fun i => if i.val = 39 then records else if i.val = 42 then heap
      else if i.val = 64 then 0 else if i.val = 65 then answers else 77
    mem := fun a =>
      if a = 1 then 16 else if a = 2 then 1 else if a = 3 then side else if a = 4 then 3
      else if 5 ≤ a && a < 5 + side * side then
        if a = 5 + (side - 1) * side + (side - 2) ||
            a = 5 + (side - 1) * side + (side - 1) then 0 else Signed.encode 1
      else if 5 + side * side ≤ a && a < 5 + 2 * (side * side) then
        if success then 0 else Signed.encode 3
      else if records ≤ a && a < records + 6 then
        [0, 0, queryBase, 2, records + 6, records + 6 + side * 16].getD (a - records) 0
      else if a = queryBase then side - 1 else if a = queryBase + 1 then side - 2
      else if a = queryBase + 2 then side - 1 else if a = queryBase + 3 then side - 1
      else if a = answers || a = answers + 1 then if zeroAnswers then 0 else Signed.encode 4
      else if a = answers + 2 then 99 else 0 }

private def observe (success zeroAnswers : Bool) : Option (List ℕ × Bool × Bool) :=
  (RecordWitness.consume.eval 512 64 (fixture success zeroAnswers)).map fun (y, t) =>
    ([y.regs RecordWitness.Reg.found, y.regs RecordWitness.Reg.witnessA,
      y.regs RecordWitness.Reg.witnessB, y.regs RecordWitness.Reg.witnessC,
      y.regs RecordWitness.Reg.scans, y.regs RecordWitness.Reg.index, y.mem (answers + 2)],
      decide (t ≤ 20 + 16 + 196 * y.regs RecordWitness.Reg.scans + 52),
      decide (∀ j : Fin 320, y.regs (RecordWitness.productBank j) =
        (fixture success zeroAnswers).regs (RecordWitness.productBank j)))

-- The first pair succeeds; the second candidate incurs no further original-weight scan.
#guard observe true false == some ([1, side - 1, side - 2, 3, 1, 2, 99], true, true)

-- Both accepted modular candidates have original sum three, and both scans fail.
#guard observe false false == some ([0, 0, 0, 0, 2, 2, 99], true, true)

-- Zero answer words produce no verifier call, even though original weights have zero sums.
#guard observe true true == some ([0, 0, 0, 0, 0, 2, 99], true, true)

#guard side ≥ 16 ^ 18
#guard ¬(16 ≥ 16 ^ 18)

end ComplexityTests.WordRAMExactTriangleRecordWitness
