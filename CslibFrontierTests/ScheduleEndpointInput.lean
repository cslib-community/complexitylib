/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: local-only (native schedule-query input regression tests)

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.ScheduleEndpointInput

/-! Native preparation preserves malformed raw words and reports their invalidity. -/

public section

namespace CslibFrontierTests.ScheduleEndpointInput

open Turing Turing.MultiTapeTM ScheduleEndpointQuery ScheduleEndpointInput

-- Both number fields use canonical binary, with zero represented by the empty word.
example : encInput ⟨[], 0, 0⟩ = [false, false] := by decide

-- Framing is charged even when the raw schedule has no rows.
example : (encInput ⟨[], 0, 1024⟩).length = 13 := by decide

-- The same finite initializer handles a valid table and an invalid aligned11 pair.
-- The index fields and old output are retained, and invalid raw input is not silently repaired.
example : ∃ (scratch : ℕ) (Q : Type) (_ : Finite Q)
    (tm : MultiTapeTM (scratch + 4) Bool Q) (c : ℕ),
    (∀ out, RunsBetween tm
      (tapesCfg (encInput ⟨[false, false, false, false], 0, 0⟩) (fun _ => []) 0 0 out)
      (tapesCfg (encInput ⟨[false, false, false, false], 0, 0⟩)
        (Fin.append (fun _ : Fin scratch => [])
          ![[false, false, false, false], [], [], [true]]) 0 0 out)
      (c * 11) ((scratch + 4) * (c * 11 + 1))) ∧
    (∀ out, RunsBetween tm
      (tapesCfg (encInput ⟨[true, true, false, false], 0, 1024⟩) (fun _ => []) 0 0 out)
      (tapesCfg (encInput ⟨[true, true, false, false], 0, 1024⟩)
        (Fin.append (fun _ : Fin scratch => [])
          ![[true, true, false, false], [], (1024 : ℕ).bits, [false]]) 0 0 out)
      (c * 22) ((scratch + 4) * (c * 22 + 1))) := by
  obtain ⟨scratch, Q, hQ, tm, c, h⟩ := exists_prepare 1
  refine ⟨scratch, Q, hQ, tm, c, ?_, ?_⟩
  · intro out
    exact h ⟨[false, false, false, false], 0, 0⟩ out
  · intro out
    exact h ⟨[true, true, false, false], 0, 1024⟩ out

end CslibFrontierTests.ScheduleEndpointInput
