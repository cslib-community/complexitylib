/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module

import Complexity.Foundations.Probability.HierarchyAccess

/-! Actual global requests distinguish negative endpoints, reset sources and fixed suffixes. -/

set_option linter.privateModule false

namespace ComplexityTests.HierarchyAccess

open Matrix Matrix.HierarchyParams Matrix.HierarchyParams.HierarchyTask

private def source : CorrectionRowTask.Channel ℕ (List ℕ) := ⟨0, 1, [7]⟩
private noncomputable def midpoint : CorrectionRowTask.Channel ℕ (List ℕ) := ⟨1, 1 / 2, [8]⟩
private noncomputable def endpoint : CorrectionRowTask.Channel ℕ (List ℕ) := ⟨2, 1 / 4, [9]⟩

-- Negative correction retains the endpoint role/suffix, while the left factor uses midpoint.
example : rawRequests (k := 1) 2 3 .residual source midpoint endpoint (1 / 8) =
    ⟨⟨.baseNormalized 2 3, source, ⟨2, 1 / 8, [9]⟩, ⟨2, 1 / 8, [9]⟩⟩,
     ⟨.row 2 (.normalized 0), source, midpoint, midpoint⟩,
     ⟨.baseNormalized 2 3, midpoint, ⟨2, 1 / 8, [9]⟩, ⟨2, 1 / 8, [9]⟩⟩,
     some ⟨.row 2 (.normalized 0), source, ⟨2, 1 / 2, [9]⟩, endpoint⟩⟩ := by
  norm_num [rawRequests, correctionAtomTask, Fin.cases, source, midpoint, endpoint]
  rfl

-- The first input reads literal zero; its successor reads an earlier normalized task.
example : (rawRequests (k := 2) 2 3 (.input 0) source midpoint endpoint 1).left.task =
    .row 2 (.correction 0) ∧
    (rawRequests (k := 2) 2 3 (.input 1) source midpoint endpoint 1).left.task =
      .row 2 (.normalized 0) := by
  constructor <;> rfl

-- Fixed symbols are prepended to inherited suffixes, on both source and endpoint.
example : routedCopyRequests (k := 0) 2 3 source endpoint (1 / 2) (1 / 8) 4 5 =
    [⟨.row 2 .weights, ⟨0, 1 / 2, [4, 7]⟩, ⟨2, 1 / 4, [5, 9]⟩,
        ⟨2, 1 / 4, [5, 9]⟩⟩,
     ⟨.residualNormalized 2 3, ⟨0, 1, [4, 7]⟩, ⟨2, 1 / 8, [5, 9]⟩,
        ⟨2, 1 / 8, [5, 9]⟩⟩] := by
  norm_num [routedCopyRequests, CorrectionRowTask.Channel.throughCopy,
    source, endpoint]

-- A zero-iteration residual is still an actual decreasing call family.
example (r : Request 0 ℕ ℕ)
    (hr : r ∈ (rawRequests 2 3 .residual source midpoint endpoint (1 / 8)).calls) :
    r.task.rank < (HierarchyTask.residual (k := 0) 2).rank :=
  rawRequests_rank_lt _ _ _ _ _ _ _ _ hr

private abbrev full (_ : ℕ) (_ : ℝ) (_ : List ℕ) (_ : Unit) (_ : Fin 2) : Prop := True

-- Arbitrary completed children are evaluated before multiplication and subtraction.
-- Distinct role requests return different entries on this same draw.
private noncomputable def child (r : Request 1 ℕ ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun x y => if r.source.role = 1 then (if x = y then 2 else 0)
    else if r.terminal.role = 1 then (if x = 0 ∧ y = 1 then 3 else 0)
    else if r.terminal.rate = 1 / 2 then 5 else 7

example : rawSample full 2 3 .residual source midpoint endpoint (1 / 8) child 0 1 =
    -5 / 4 := by
  norm_num [rawSample, rawPositiveSample, rawNegativeSample, rawRequests, usageRatio,
    CorrectionRowTask.Channel.retains,
    full, child, source, midpoint, endpoint, Fin.sum_univ_two]

end ComplexityTests.HierarchyAccess
