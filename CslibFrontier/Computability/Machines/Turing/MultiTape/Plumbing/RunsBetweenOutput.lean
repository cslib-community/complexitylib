/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.RunsBetween
import CslibFrontier.Computability.Machines.Turing.MultiTape.Run

/-!
# Plain computation from a native configuration contract

A bounded native run starting with blank work tapes and empty output is a plain computation.
The final work tapes and heads are unrestricted: the bridge retains both resource bounds and
takes the computed word from the final configuration's output.
-/

public section

namespace Turing.MultiTapeTM.RunsBetween

variable {K : ℕ} {Symbol State : Type*} {input : List Symbol}
  {tm : MultiTapeTM K Symbol State} {final : Cfg K Symbol Unit input} {t s : ℕ}

/-- A native run from the ordinary blank initial layout computes its final output within the
same time and workspace bounds, with no requirement to clear the final work tapes. -/
theorem computesInTimeAndSpace
    (h : RunsBetween tm (tapesCfg input (fun _ => []) 0 0 []) final t s) :
    tm.ComputesInTimeAndSpace input final.output t s := by
  rcases h with ⟨hrun, hspace⟩
  rw [tapesCfg_zero_withState, ← initCfg_eq_wordsCfg] at hrun hspace
  have hhalt : (tm.runFrom (tm.initCfg input) t).Halted := by rw [hrun]; rfl
  exact ⟨⟨t, hhalt, congrArg Cfg.output hrun⟩,
    runsInTime_of_halted hhalt, runsInSpace_of_halted hhalt hspace⟩

end Turing.MultiTapeTM.RunsBetween
