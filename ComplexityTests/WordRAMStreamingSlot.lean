/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

-- upstream: local-only (tests)

import Complexity.Algorithms.WordRAM.ExactTriangle.StreamingFixedPrime.Program
-- Compiled `Code.eval` runs below use the fast interpreter.
import Complexity.Computability.WordRAM.Structured.FastEval

/-!
# Concrete slot reuse with dirty memory

These small native-program fixtures exercise control flow and physical memory reuse. Their
`D=1` geometry is deliberately outside the admitted endpoint theorem. Separate initialized
symbolic clients discharge the actual `D^18 ≤ n` geometry at positive threshold.
-/

set_option linter.hashCommand false

namespace ComplexityTests.WordRAMStreamingSlot

open Cslib.WordRAM Cslib.Algorithms.WordRAM.ExactTriangle

private def values (success : Bool) : List ℤ :=
  [1, 0, 0, 0, 0, 0, 0, 0, 0] ++ List.replicate 9 (if success then 2 else -2) ++
    (List.range 9).map (fun i => if success then if i = 1 then -3 else 2 else -2)

private def fixture (success : Bool) : Data 416 :=
  let input := PreparationInput.input 3 1 1 2 (values success)
  let canonical : Data 416 := .init input
  { regs := fun _ => 2 ^ 4096 + 7
    mem := fun a => if a < input.length + 1 then canonical.mem a else 2 ^ 4096 + 7 }

private def observe (success : Bool) : Option (List ℕ × List ℕ × Bool × ℕ) :=
  (StreamingFixedPrime.program.eval 8192 1024 (fixture success)).map fun (y, t) =>
    ([y.regs FixedPrime.Reg.index, y.regs FixedPrime.Reg.limit,
      y.regs FixedPrime.Reg.found, y.regs FixedPrime.Reg.scans,
      y.regs (StreamingFixedPrime.producerBank Instances.produced),
      y.regs (StreamingFixedPrime.producerBank Instances.total),
      y.regs (StreamingFixedPrime.producerBank Instances.heap),
      y.regs (FixedPrime.recordBank (RecordWitness.productBank RecordProduct.Reg.ordinal)),
      y.regs (FixedPrime.recordBank RecordWitness.Reg.witnessA),
      y.regs (FixedPrime.recordBank RecordWitness.Reg.witnessB),
      y.regs (FixedPrime.recordBank RecordWitness.Reg.witnessC),
      y.mem (y.regs (FixedPrime.recordBank (RecordWitness.productBank RecordProduct.Reg.result)))],
      (List.range 6).map (fun j => y.mem (103 + j)),
      decide (∀ q : Fin 32, y.mem q.val = (fixture success).mem q.val), t)

-- Logical records 0–4 use the same physical ordinal zero. The final query count is one,
-- whereas the first chunk has eight occurrences. Success in the later piece prevents record5.
#guard observe true == some
  ([5, 5, 1, 23, 5, 6, 103, 0, 0, 0, 1, 2], [1, 1, 79, 1, 109, 112], true, 37520)

-- Every logical record is consumed on failure, including the short final query chunk.
-- All original BC/AC weights in this fixture are negative.
#guard observe false == some
  ([6, 6, 0, 24, 6, 6, 103, 0, 0, 0, 0, 0], [1, 2, 79, 1, 109, 112], true, 43098)

private def firstSlot : Option (List ℕ × ℕ) := do
  let (a, _) ← StreamingFixedPrime.prepare.eval 8192 1024 (fixture true)
  let (b, _) ← StreamingFixedPrime.setup.eval 8192 1024 a
  let (c, t) ← StreamingFixedPrime.step.eval 8192 1024 b
  pure ((List.range 6).map (fun j => c.mem (103 + j)) ++
    [c.regs FixedPrime.Reg.index, c.regs (StreamingFixedPrime.producerBank Instances.heap),
      c.regs (FixedPrime.recordBank (RecordWitness.productBank RecordProduct.Reg.ordinal))], t)

#guard firstSlot == some ([0, 0, 61, 8, 109, 112, 1, 103, 0], 8550)

private def empty : Option (List ℕ × Bool) :=
  let input := PreparationInput.input 0 1 1 2 []
  let canonical : Data 416 := .init input
  let x : Data 416 :=
    { regs := fun _ => 717
      mem := fun a => if a < 5 then canonical.mem a else 999 }
  (StreamingFixedPrime.program.eval 32 32 x).map fun (y, _) =>
    ([y.regs FixedPrime.Reg.index, y.regs FixedPrime.Reg.limit,
      y.regs FixedPrime.Reg.found, y.regs FixedPrime.Reg.scans,
      y.regs (StreamingFixedPrime.producerBank Instances.produced),
      y.regs (StreamingFixedPrime.producerBank Instances.total),
      y.regs (StreamingFixedPrime.producerBank Instances.heap)], y.mem 7 == 999)

-- The zero-record guard leaves even the would-be slot untouched.
#guard empty == some ([0, 0, 0, 0, 0, 0, 7], true)

end ComplexityTests.WordRAMStreamingSlot
