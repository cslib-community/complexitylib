/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.PCP.Approximation.LabelCover.MinRep
import CslibFrontier.Computability.PCP.Encoded.Count

/-! Concrete weighted Min-Rep instances: the exact output on a star with a repeated left end, a
yes-instance, a no-instance from a contradictory pair of edges, and the edge-free case. -/

namespace CslibFrontierTests.LabelCoverMinRep

open Cslib.PCP Cslib.PCP.Encoded Cslib.Complexity Cslib.PCP.Encoded.LabelCoverMinRep
  Turing.MultiTapeTM

/-- Two edges from the left vertex `0`, to the right vertices `5` and `7`, with the identity and
the constant `0` as projections. -/
def star : Graph (Fin 2 → Fin 2) :=
  ⟨8, [⟨0, 5, id⟩, ⟨0, 7, fun _ => 0⟩]⟩

/-- The left vertex `0` has degree `2`, at both of its positions in `srcs`; the right vertices
have degree `1`. The variables `2` and `3` belong to the second position of `0` and occur in no
formula. The threshold is `2m = 4`. -/
example : minRep (.refl _) (.refl _) star =
    ⟨[2, 2, 2, 2, 1, 1, 1, 1], 4,
      [[[(0, true), (4, true)], [(1, true), (5, true)]],
        [[(0, true), (6, true)], [(1, true), (6, true)]]]⟩ := by
  decide

/-- Label `0` with `1`, `5` with `1` and `7` with `0`: the selected variables `1`, `5`, `6` weigh
`2 + 1 + 1 = 4`. -/
example : minRep (.refl _) (.refl _) star ∈ (GapCMMSA 4 1 1).yes := by
  refine minRep_mem_yes _ _ ?_ le_rfl
  refine (satisfiable_toGraph_projectionEval_iff star).2 ⟨fun _ => 1,
    fun v => if v = 5 then 1 else 0, ?_⟩
  decide

/-- Two edges between the same vertices asking for the identity and for the swap. -/
def contradiction : Graph (Fin 2 → Fin 2) :=
  ⟨2, [⟨0, 1, id⟩, ⟨0, 1, fun a => a + 1⟩]⟩

/-- Every labelling violates one of the two edges. -/
private theorem half_le_unsatVal :
    1 / 2 ≤ (contradiction.toGraph projectionEval).unsatVal := by
  refine (ConstraintGraph.le_unsatVal_iff _).2 fun σ => ?_
  rw [Graph.unsatFrac_toGraph]
  have hcount : 1 ≤ contradiction.edges.countP fun d =>
      !projectionEval d.constraint (σ d.src) (σ d.dst) := by
    simp only [contradiction, List.countP_cons, List.countP_nil, projectionEval]
    generalize (σ 0).1 = a
    generalize (σ 1).2 = b
    revert a b
    decide
  have hlen : contradiction.edges.length = 2 := rfl
  rw [hlen]
  have : (1 : ℝ) ≤ (contradiction.edges.countP fun d =>
      !projectionEval d.constraint (σ d.src) (σ d.dst) : ℕ) := by exact_mod_cast hcount
  push_cast
  linarith

/-- With value `1 / 2 < 1 / g²` for the gap `g = 5 / 4`, the output is a no-instance: every
assignment of weight at most `(5 / 4) · 4` falsifies a formula. -/
example : minRep (.refl _) (.refl _) contradiction ∈ (GapCMMSA 4 (5 / 4) 1).no :=
  minRep_mem_no _ _ le_rfl (by norm_num) (by norm_num : (1 / 2 : ℝ) < 1 / (5 / 4) ^ 2)
    (by linarith [half_le_unsatVal])

/-- An instance without edges gives the fixed yes-instance with threshold `1`. -/
example : minRep (.refl _) (.refl _) (⟨3, []⟩ : Graph (Fin 2 → Fin 2)) = ⟨[], 1, []⟩ := by
  decide

/-- The native certificate composes with a client reading the threshold. -/
example : ComputableInPolyTime
    (fun G : Graph (Fin 2 → Fin 2) => (minRep (.refl _) (.refl _) G).threshold)
    (Graph.encoding (encPi (encFinEnum (Fin 2)))) encUnary :=
  CMMSAInstance.isPolyTime_threshold (isPolyTime_minRep _ _)

end CslibFrontierTests.LabelCoverMinRep
