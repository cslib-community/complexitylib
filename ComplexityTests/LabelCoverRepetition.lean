/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.PCP.Approximation.LabelCover.Repetition
import Complexity.Computability.PCP.Approximation.LabelCover.Incidence
import Complexity.Computability.PCP.Encoded.Count

/-! # Parallel repetition of Label Cover instances

Concrete simple and non-simple instances, the edge count and numbering of a repetition, perfect
completeness, and Holenstein's bound for the repetitions of an instance of value `1/2`.
-/

namespace ComplexityTests.LabelCoverRepetition

open Cslib.PCP Cslib.PCP.Encoded Cslib.Complexity LabelCoverRepetition

/-- Two left vertices whose constant projections give the one right vertex different labels.
Every labelling satisfies exactly one of the two edges. -/
def conflict : Graph (Bool → Bool) :=
  ⟨2, [⟨0, 0, fun _ => false⟩, ⟨1, 0, fun _ => true⟩]⟩

example : conflict.IsSimple := by decide
example : conflict.WellFormed := (Graph.isWellFormed_eq_true _).mp (by decide)

-- The fixed contradictory instance of the incidence reduction joins the same two vertices twice,
-- so it is not simple.
example : ¬(LabelCoverIncidence.contradiction false true).IsSimple := by decide

-- Opposite directions between two vertices, and an edge from left `0` to right `0`, are allowed.
example : (⟨1, [⟨0, 0, id⟩, ⟨0, 1, id⟩, ⟨1, 0, id⟩]⟩ : Graph (Bool → Bool)).IsSimple := by decide

-- A pair of parallel edges, even with equal projections, is not.
example : ¬(⟨1, [⟨0, 1, id⟩, ⟨0, 1, id⟩]⟩ : Graph (Bool → Bool)).IsSimple := by decide

-- The two-fold repetition has the four pairs of edges, in lexicographic order. A pair `(a, b)` is
-- numbered `Nat.pair a (Nat.pair b 0)`, so the left ends `(0, 0)`, `(0, 1)`, `(1, 0)`, `(1, 1)` are
-- numbered `0`, `4`, `2`, `5`, and the right ends are all `(0, 0)`, numbered `0`.
example : (pow 2 conflict).edges.length = 4 := by simp [conflict]
example : tupleCode 2 ![1, 0] = Nat.pair 1 (Nat.pair 0 0) := rfl
example : (pow 2 conflict).edges.map (fun d => (d.src, d.dst)) =
    [(0, 0), (4, 0), (2, 0), (5, 0)] := by
  decide
example : (pow 2 conflict).WellFormed :=
  wellFormed_pow 2 ((Graph.isWellFormed_eq_true _).mp (by decide))

-- Every labelling of `conflict` violates exactly half of the edges.
theorem unsatVal_conflict : (conflict.toGraph projectionEval).unsatVal = 1 / 2 := by
  refine le_antisymm ?_ ((ConstraintGraph.le_unsatVal_iff _).2 fun τ => ?_)
  · refine ((conflict.toGraph projectionEval).unsatVal_le fun _ => (false, false)).trans ?_
    rw [Graph.unsatFrac_toGraph]
    norm_num [conflict, projectionEval]
  · rw [Graph.unsatFrac_toGraph]
    cases h : (τ 0).2 <;> norm_num [conflict, projectionEval, h]

-- Holenstein's bound for the repetitions of `conflict`: `|β| |γ| = 4`, so the exponent is `k / 2`,
-- and every labelling of the `k`-fold repetition satisfies at most the proportion
-- `(1 - (1/2)³ / 6000)^{k / 2}` of its edges.
example (k : ℕ) :
    1 - ((pow k conflict).toGraph projectionEval).unsatVal ≤
      (1 - (1 / 2) ^ 3 / 6000) ^ ((k : ℝ) / 2) := by
  have hlog : Real.logb 2 (Fintype.card Bool * Fintype.card Bool) = 2 := by
    rw [Fintype.card_bool, show ((2 : ℕ) : ℝ) * (2 : ℕ) = 2 ^ (2 : ℝ) by norm_num,
      Real.logb_rpow two_pos (by norm_num)]
  have h := one_sub_unsatVal_pow_le (g := conflict) (by decide) (by simp)
    unsatVal_conflict.ge k
  rwa [hlog] at h

/-- A single negation constraint, satisfied by labelling left `0` with `false` and right `1` with
`true`. -/
def negation : Graph (Bool → Bool) :=
  ⟨2, [⟨0, 1, not⟩]⟩

-- Repetition keeps satisfiability.
example (k : ℕ) : ((pow k negation).toGraph projectionEval).Satisfiable := by
  refine satisfiable_pow k ((satisfiable_toGraph_projectionEval_iff _).mpr
    ⟨fun _ => false, fun _ => true, ?_⟩)
  decide

end ComplexityTests.LabelCoverRepetition
