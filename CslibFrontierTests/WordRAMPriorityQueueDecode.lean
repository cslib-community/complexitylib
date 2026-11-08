/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.DataStructure.PriorityQueue.WordRAM.Decode
import CslibFrontier.DataStructure.PriorityQueue.BinaryHeap.Native.Program

/-! Concrete observations through the actual uniform heap ABI. Constant register vectors make
the decoding tests independent of private register geometry. These are decoder tests, not
assertions that a native operation produced the register values. -/

namespace ComplexityTests.WordRAMPriorityQueueDecode

open Cslib.WordRAM Cslib.DataStructure.PriorityQueue
open Cslib.DataStructure.PriorityQueue.WordRAM
open Cslib.DataStructure.PriorityQueue.BinaryHeap.Native

-- The actual code's zero flag ignores payload registers even with an empty handle universe.
example : Program.code.decode (n := 0) (K_max := 0) .extractMin (fun _ => 0) = some none :=
  PQCode.decode_extractMin_none _ _ rfl

example : Program.code.decode (n := 1) (K_max := 7) (.getKey 0) (fun _ => 0) = some none :=
  PQCode.decode_getKey_none _ _ _ rfl

-- Starting with garbage in every register, replacing only the flag by zero reports absence.
example : Program.code.decode (n := 0) (K_max := 7) .extractMin
    (Function.update (fun _ => 7) Program.code.outFlag 0) = some none :=
  PQCode.decode_extractMin_none _ _ (Function.update_self _ _ _)

-- Any nonzero flag is accepted; the maximal three-bit payload stays 7, with no successor shift.
example : Fits 3 7 ∧
    Program.code.decode (n := 1) (K_max := 7) (.getKey 0) (fun _ => 7) = some (some 7) :=
  ⟨by decide, PQCode.decode_getKey_some _ _ _ (by decide) rfl⟩

example : Program.code.decode (n := 2) (K_max := 1) .extractMin (fun _ => 1) =
    some (some ((1 : Fin 2), 1)) :=
  PQCode.decode_extractMin_some _ _ _ (by decide) rfl rfl

-- A present flag does not bypass the typed handle-range check.
example : Program.code.decode (n := 1) (K_max := 7) .extractMin (fun _ => 7) = none := by
  simp [PQCode.decode]

example : Program.code.decode (n := 0) (K_max := 1) .extractMin (fun _ => 1) = none := by
  simp [PQCode.decode]

example : Program.code.decode (n := 0) (K_max := 0) .isEmpty (fun _ => 0) = some false :=
  PQCode.decode_isEmpty _ _ rfl

example : Program.code.decode (n := 0) (K_max := 0) .isEmpty (fun _ => 1) = some true :=
  PQCode.decode_isEmpty _ _ rfl

end ComplexityTests.WordRAMPriorityQueueDecode
