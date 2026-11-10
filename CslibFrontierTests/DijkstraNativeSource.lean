/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (Dijkstra bounded-source regressions)

public import CslibFrontier.Algorithms.Lean.Dijkstra.Native.Source
public import CslibFrontier.Algorithms.Lean.Dijkstra.Native.Word

/-! Source transport keeps a genuine empty-queue exit and repeated graph-offset reads.
These tests concern the memory program; no native instruction bound is asserted. -/

public section

namespace Cslib.Algorithms.Lean.Dijkstra.Tests.NativeSource

open Cslib.DataStructure Cslib.DataStructure.PriorityQueue

/-- Concrete source methods with an empty one-vertex heap. -/
@[expose] def methods : Methods (spec 1 0 0) (Memory.spec 4) :=
  Memory.memMethods 1 0 0 4 ⟨⟨5, 1⟩, 6⟩ ⟨4, 1⟩ (Memory.inputGraph 1 0)

-- Thirty-seven available rounds still perform only the first empty extraction.
/-- An empty extraction exits without executing the remaining thirty-six rounds. -/
theorem empty_exit : (Memory.spec 4).runClient ⟨fun _ => 0, 10⟩ (Native.loopView methods 37) =
    ((), ⟨fun _ => 0, 10⟩, [DataStructure.Memory.Op.read 5]) := by
  rw [Native.loopView_eq]
  rfl

-- Even a zero-degree scan retains its two offset reads and leaves all memory unchanged.
/-- The zero-degree case retains both offset queries. -/
theorem empty_scan : (Memory.spec 4).runClient ⟨fun _ => 0, 10⟩ (Native.scanView methods 0 0) =
    ((), ⟨fun _ => 0, 10⟩,
      [DataStructure.Memory.Op.read 3, DataStructure.Memory.Op.read 4]) := by
  rw [Native.scanView_eq]
  rfl

/-- An invalid edge target with a nonzero weight, as a source-behavior test. -/
@[expose] def malformedMemory (a : ℕ) : ℕ := if a = 5 then 9 else if a = 6 then 15 else 0

/-- The original invalid-target fallback uses the current vertex and zero weight.
All queried cells, both writes and the complete unchanged frontier are retained. -/
theorem invalid_edge_fallback :
    (Memory.spec 5).runClient ⟨malformedMemory, 30⟩
      (Native.relaxWord (fun v k => DataStructure.Memory.write (20 + v) k)
        (fun v k => DataStructure.Memory.write (21 + v) k) ⟨10, 1⟩
        ⟨⟨3, 2⟩, ⟨5, 2⟩⟩ 1 0 7 0) =
      ((), ⟨Function.update (Function.update malformedMemory 10 8) 20 7, 30⟩,
        [DataStructure.Memory.Op.read 3, .read 5, .read 6, .read 10, .write 10 8,
          .write 20 7]) := by
  rfl

end Cslib.Algorithms.Lean.Dijkstra.Tests.NativeSource
