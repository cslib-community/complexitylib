/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.CSP.Edge.Solver.Semantics
public import CslibFrontier.Algorithms.Lean.EdgeCSP.Solver.Rows
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Mathlib.Data.List.GetD

/-!
# Native initialization from actual stored rows

The initial buffer is the flattening of one actual first stored row per constraint. Its native
certificate applies to all raw inputs; its agreement with occurrence labelings uses the full
model guard. In particular, false nullaries and malformed arities cannot enter the optimizer
through a fabricated initial row. This representation bookkeeping is original.
-/

public section

namespace Cslib.Complexity.CSP.EdgeSolver

open Cslib.Logic.PL Cslib.Logic.PL.CSP Turing.MultiTapeTM

/-- Materialize the actual first-row initializer in ordinary incidence order. -/
theorem initial_buffer (F : CSP Table ℕ) (h : checkModel F = true) :
    (incidenceList F).map (initial F) = (initialRows F).flatten :=
  Solver.materialize_labels F (initialRows F) (by simp [initialRows])
    (fun i => (initialRows_spec F h i).2)

/-- Actual stored-row initialization is native polynomial-time on every raw framed CSP.
No satisfying assignment, valid row or width certificate is supplied as input. -/
theorem computableInPolyTime_initialBuffer : ComputableInPolyTime
    (fun F : CSP Table ℕ => (initialRows F).flatten) (encCSP encTable encNat)
    (encList encBool) := by
  have hr := encTable_rows_deg.computableInPolyTime
  have hm : ComputableInPolyTime initialRows (encCSP encTable encNat)
      (encList (encList encBool)) := by
    unfold initialRows
    fun_prop
  simpa only [List.flatten_eq_flatMap] using
    ComputableInPolyTime.flatMapWithInput hm (ComputableInPolyTime.snd _ _)

end Cslib.Complexity.CSP.EdgeSolver
