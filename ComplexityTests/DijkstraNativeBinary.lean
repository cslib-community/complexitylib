/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (native Dijkstra endpoint regressions)

public import Complexity.Algorithms.Lean.Dijkstra.Native.Binary

/-! One fixed native program handles different graph inputs. The fixtures include a real
relaxation and an unreachable vertex; the complete frontier is retained as well as result cells. -/

public section

namespace Cslib.Algorithms.Lean.Dijkstra.Tests.NativeBinary

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure
open Cslib.Algorithms.WordRAM.Dijkstra (ListInstance)

/-- One vertex without an outgoing edge. -/
@[expose] def singleton : ListInstance := ⟨1, fun _ => [], 0⟩

/-- One weighted edge and one unreachable vertex. -/
@[expose] def oneEdge : ListInstance := ⟨3, fun u => if u = 0 then [(1, 7)] else [], 0⟩

/-- The exact source memory and frontier for the singleton instance. -/
theorem singleton_result :
    ((Memory.spec 6).clientState (Memory.State.init singleton.encode) Memory.run).mem
        (singleton.outAddr singleton.source) = 1 ∧
      ((Memory.spec 6).clientState (Memory.State.init singleton.encode) Memory.run).frontier = 11 :=
  by decide +kernel

/-- The source performs the relaxation but leaves the unreachable distance absent. -/
theorem oneEdge_result :
    ((Memory.spec 9).clientState (Memory.State.init oneEdge.encode) Memory.run).mem
        (oneEdge.outAddr oneEdge.source) = 1 ∧
      ((Memory.spec 9).clientState (Memory.State.init oneEdge.encode) Memory.run).mem
        (oneEdge.outAddr ⟨1, by decide⟩) = 8 ∧
      ((Memory.spec 9).clientState (Memory.State.init oneEdge.encode) Memory.run).mem
        (oneEdge.outAddr ⟨2, by decide⟩) = 0 ∧
      ((Memory.spec 9).clientState (Memory.State.init oneEdge.encode) Memory.run).frontier = 23 :=
  by decide +kernel

/-- The same code and frontier register handle both runtime raw memories, with actual charged
flat runs and exact source-state preservation. No code is selected after either graph. -/
theorem same_program :
    ∃ r pc : ℕ, ∃ prog : Program .exact r, ∃ frontier : Fin r,
      (∃ (y : Data r) (steps : ℕ), Runs 6 prog (State.init singleton.encode) ⟨pc, y⟩ steps ∧
        step 6 prog ⟨pc, y⟩ = .halt 0 ∧ y.mem (singleton.outAddr singleton.source) = 1 ∧
        y.regs frontier = 11) ∧
      (∃ (y : Data r) (steps : ℕ), Runs 9 prog (State.init oneEdge.encode) ⟨pc, y⟩ steps ∧
        step 9 prog ⟨pc, y⟩ = .halt 0 ∧ y.mem (oneEdge.outAddr oneEdge.source) = 1 ∧
        y.mem (oneEdge.outAddr ⟨1, by decide⟩) = 8 ∧ y.mem (oneEdge.outAddr ⟨2, by decide⟩) = 0 ∧
        y.regs frontier = 23) := by
  obtain ⟨r, _, pc, prog, frontier, he⟩ := Native.Binary.exists_program_state
  refine ⟨r, pc, prog, frontier, ?_, ?_⟩
  · obtain ⟨y, steps, hrun, hhalt, hm, _, _⟩ := he singleton 6 (by decide)
    refine ⟨y, steps, hrun, hhalt, ?_, ?_⟩
    · exact (congrArg (fun s : Memory.State => s.mem (singleton.outAddr singleton.source)) hm).trans
        singleton_result.1
    · exact (congrArg Memory.State.frontier hm).trans singleton_result.2
  · obtain ⟨y, steps, hrun, hhalt, hm, _, _⟩ := he oneEdge 9 (by decide)
    refine ⟨y, steps, hrun, hhalt, ?_, ?_, ?_, ?_⟩
    · exact (congrArg (fun s : Memory.State => s.mem (oneEdge.outAddr oneEdge.source)) hm).trans
        oneEdge_result.1
    · exact (congrArg (fun s : Memory.State => s.mem (oneEdge.outAddr ⟨1, by decide⟩)) hm).trans
        oneEdge_result.2.1
    · exact (congrArg (fun s : Memory.State => s.mem (oneEdge.outAddr ⟨2, by decide⟩)) hm).trans
        oneEdge_result.2.2.1
    · exact (congrArg Memory.State.frontier hm).trans oneEdge_result.2.2.2

end Cslib.Algorithms.Lean.Dijkstra.Tests.NativeBinary
