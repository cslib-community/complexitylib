/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.PCP.Approximation.LabelCover.Incidence
import Complexity.Computability.PCP.Encoded.Count

/-! Concrete incidence reductions, including tight factor-two loss and empty relations. -/

namespace ComplexityTests.LabelCoverIncidence

open Cslib.PCP Cslib.PCP.Encoded Cslib.Complexity LabelCoverIncidence Turing.MultiTapeTM

private def pairs : List (Bool × Bool) :=
  [(false, false), (false, true), (true, false), (true, true)]

private theorem pairs_cover (p : Bool × Bool) : p ∈ pairs := by
  rcases p with ⟨a, b⟩
  cases a <;> cases b <;> decide

/-- A single equality constraint on two distinct vertices. -/
def equality : Graph (Bool → Bool → Bool) :=
  ⟨2, [⟨0, 1, fun a b => a == b⟩]⟩

example : (reduce pairs false true equality).edges.length = 2 := by decide

example : ((reduce pairs false true equality).toGraph projectionEval).Satisfiable := by
  apply satisfiable_reduce pairs pairs_cover false true
  refine ⟨fun _ => false, fun i => ?_⟩
  fin_cases i
  rfl

/-- A loop requiring its own label to differ from itself. Its relation has satisfying pairs, so
this exercises the incidence branch rather than the empty-relation branch. -/
def loop : Graph (Bool → Bool → Bool) :=
  ⟨1, [⟨0, 0, fun a b => a != b⟩]⟩

example : (reduce pairs false true loop).edges.map (fun d => (d.src, d.dst)) =
    [(0, 0), (0, 0)] := by decide

private theorem unsatVal_loop : (loop.toGraph id).unsatVal = 1 := by
  refine le_antisymm (ConstraintGraph.unsatVal_le_one _) ((ConstraintGraph.le_unsatVal_iff _).2
    fun σ => ?_)
  rw [Graph.unsatFrac_toGraph]
  cases h : σ 0 <;> norm_num [loop, h]

/-- The incidence loss of two is tight already on a single loop. -/
example : ((reduce pairs false true loop).toGraph projectionEval).unsatVal = 1 / 2 := by
  refine le_antisymm ?_ ?_
  · calc
      _ ≤ ((reduce pairs false true loop).toGraph projectionEval).unsatFrac
          (fun _ : ℕ => ((false, false), false)) := ConstraintGraph.unsatVal_le _ _
      _ = 1 / 2 := by
        rw [Graph.unsatFrac_toGraph]
        norm_num [reduce, incidence, block, repair, pairs, loop, projectionEval]
  · simpa only [unsatVal_loop] using half_unsatVal_le_reduce pairs false true (by decide) loop

/-- Contradictory parallel constraints retain two distinct left occurrence indices. -/
def parallel : Graph (Bool → Bool → Bool) :=
  ⟨2, [⟨0, 1, fun a b => a == b⟩, ⟨0, 1, fun a b => a != b⟩]⟩

example : (reduce pairs false true parallel).edges.map (fun d => (d.src, d.dst)) =
    [(0, 0), (0, 1), (1, 0), (1, 1)] := by decide

private theorem unsatVal_parallel : (parallel.toGraph id).unsatVal = 1 / 2 := by
  have hfrac (σ : ℕ → Bool) : (parallel.toGraph id).unsatFrac σ = 1 / 2 := by
    rw [Graph.unsatFrac_toGraph]
    cases h₀ : σ 0 <;> cases h₁ : σ 1 <;> norm_num [parallel, h₀, h₁]
  refine le_antisymm ?_ ((ConstraintGraph.le_unsatVal_iff _).2 fun σ => (hfrac σ).ge)
  simpa only [hfrac] using (parallel.toGraph id).unsatVal_le (fun _ => false)

example : ((reduce pairs false true parallel).toGraph projectionEval).unsatVal = 1 / 4 := by
  refine le_antisymm ?_ ?_
  · calc
      _ ≤ ((reduce pairs false true parallel).toGraph projectionEval).unsatFrac
          (fun _ : ℕ => ((false, false), false)) := ConstraintGraph.unsatVal_le _ _
      _ = 1 / 4 := by
        rw [Graph.unsatFrac_toGraph]
        norm_num [reduce, incidence, block, repair, pairs, parallel, projectionEval]
  · have h := half_unsatVal_le_reduce pairs false true (by decide) parallel
    rw [unsatVal_parallel] at h
    norm_num at h ⊢
    exact h

/-- The empty relation is handled explicitly, with target value exactly one half. -/
example : ((reduce pairs false true (⟨2, [⟨0, 1, fun _ _ => false⟩]⟩ :
    Graph (Bool → Bool → Bool))).toGraph projectionEval).unsatVal = 1 / 2 := by
  exact unsatVal_contradiction false true (by decide)

/-- An edge-free input remains edge-free, including when it declares no vertices. -/
example : (reduce pairs false true (⟨0, []⟩ : Graph (Bool → Bool → Bool))).edges = [] := rfl

example : ((reduce pairs false true (⟨0, []⟩ : Graph (Bool → Bool → Bool))).toGraph
    projectionEval).unsatVal = 0 := by
  change ((⟨0, []⟩ : Graph (Bool × Bool → Bool)).toGraph projectionEval).unsatVal = 0
  apply (ConstraintGraph.unsatVal_eq_zero_iff _).2
  exact ⟨fun _ => ((false, false), false), fun i => Fin.elim0 i⟩

/-- The native certificate composes with a client counting the output edges. -/
example : ComputableInPolyTime
    (fun g : Graph (Bool → Bool → Bool) => (reduce pairs false true g).edges.length)
    (Graph.encoding (encPi (encPi encBool))) encUnary := by
  have h := isPolyTime_reduce pairs false true encBool
  fun_prop

end ComplexityTests.LabelCoverIncidence
