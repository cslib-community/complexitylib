/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests of numeric packed replay answers)

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.QueryReplaySupplierChunkTable
public import ComplexityTests.Machines.Turing.MultiTape.QueryReplayGate

/-!
# Packed local-answer regressions

The last chunk is partial and contains a nonzero retained bit. Missing high bits are zero.
Rejection and motion failure return zero chunks, while huge binary offsets do not allocate
huge padded words. A concrete replay queries the original input before extracting its answer.
-/

public section

namespace ComplexityTests.QueryReplaySupplierChunk

open Turing MultiTapeTM MultiTapePTM.BlockComputation
open MultiTapePTM.BlockComputation.QueryReplay
open NativeBlockCodec

private theorem run_one (context : SupplierChunk.Context)
    (expected : Option (Fin 1) → SignType) :
    (SupplierChunk.machine QueryReplayGate.reader code).runFrom [true]
      (context, .inr (QueryReplayGate.start expected)) 1 =
        (context, .inr (QueryReplayGate.done expected)) := by
  rw [SupplierChunk.runFrom_eq, CheckedGate.runFrom_inr]
  apply congrArg (fun q => (context, Sum.inr q))
  unfold QueryReplayGate.start QueryReplayGate.done
  rw [Gate.runFrom_eq]
  simp only [QueryMachine.runFrom_succ, QueryMachine.runFrom_zero, QueryMachine.step,
    QueryReplay.machine, QueryMachine.read, tick, QueryReplayGate.reader, MultiTapeTM.tr_ofTr]
  rfl

def allFive : Fin 5 → Bool := fun _ => true

example : Encoding.NativeDecode.readNat [true, true, true, true, true] 3 3 = 3 := by decide
example : (Cslib.TreeEval.Ary.Packed.packBits (by decide : 5 ≤ 2 * 3)
    allFive (1 : Fin 2)).val = 3 := by decide

-- The completed 13-bit label has bit 12 set; its last 2-bit chunk therefore encodes one.
example : SupplierChunk.answer QueryReplayGate.reader code
    ((SupplierChunk.machine QueryReplayGate.reader code).runFrom [true]
      ((2, 6), .inr (QueryReplayGate.start (QueryReplayGate.row .pos .neg))) 1) = 1 := by
  rw [run_one]
  decide
example : SupplierChunk.answer QueryReplayGate.reader code
    ((SupplierChunk.machine QueryReplayGate.reader code).runFrom [true]
      ((2, 0), .inr (QueryReplayGate.start (QueryReplayGate.row .zero .neg))) 1) = 0 := by
  rw [run_one]
  decide
example : SupplierChunk.answer QueryReplayGate.reader code
    ((2, 6), .inl [true, true, true]) = 0 := by decide
example : SupplierChunk.answer QueryReplayGate.reader code
    ((0, 1000000000), .inr (QueryReplayGate.done (QueryReplayGate.row .pos .neg))) = 0 := by decide
example : SupplierChunk.answer QueryReplayGate.reader code
    ((1000000000, 1), .inr (QueryReplayGate.done (QueryReplayGate.row .pos .neg))) = 0 := by decide

end ComplexityTests.QueryReplaySupplierChunk
