/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Statistics.LeastSquares.FixedEffects.Matrix
public import Complexity.Statistics.LeastSquares.FixedEffects.Resources
import Mathlib.Tactic

/-!
# Matrix semantics of the computed fixed-effects audit

Connects actual rational retained observations in [XuGaoHu2027], Theorem 4.1
(PDF p. 9), to the real inverse-matrix estimator. A retained group with no
observations has no dummy column. Repeated observations retain distinct row
indices. Positive denominator is proved equivalent to positive definiteness.
-/

public section

namespace Cslib.LeastSquares.FixedEffects

open Matrix

/-- Nonempty retained groups, indexed by their original positions in the plan. -/
abbrev Active (p : List Choice) :=
  {g : Fin p.length // 0 < (p.get g).kept.length}

/-- Row indices within a nonempty retained group. -/
abbrev Rows (p : List Choice) (g : Active p) := Fin (p.get g.val).kept.length

instance (p : List Choice) (g : Active p) : Nonempty (Rows p g) :=
  Fin.pos_iff_nonempty.mp g.property

/-- Real regressor data for the retained design. -/
@[expose] def realX (p : List Choice) (g : Active p) (i : Rows p g) : ℝ :=
  ((p.get g.val).kept.get i).1

/-- Real response data for the retained design. -/
@[expose] def realY (p : List Choice) (g : Active p) (i : Rows p g) : ℝ :=
  ((p.get g.val).kept.get i).2

private theorem active_sum (p : List Choice) (f : Choice → ℚ) (hz : ∀ a, a.kept = [] → f a = 0) :
    (∑ g : Active p, (f (p.get g.val) : ℝ)) = ((p.map f).sum : ℝ) := by
  rw [← Fin.sum_univ_fun_getElem]
  push_cast
  simp only [← List.get_eq_getElem]
  change (∑ g : {g : Fin p.length // 0 < (p.get g).kept.length},
    (f (p.get g.val) : ℝ)) = _
  rw [← Finset.sum_subtype (Finset.univ.filter fun g : Fin p.length =>
    0 < (p.get g).kept.length) (by simp) (fun g => (f (p.get g) : ℝ))]
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro g _ hg
  have hn : (p.get g).kept = [] := by
    apply List.length_eq_zero_iff.mp
    have : ¬ 0 < (p.get g).kept.length := by simpa using hg
    omega
  rw [hz _ hn]
  norm_num

/-- The real matrix's within numerator is exactly the computed rational numerator. -/
theorem real_cross (p : List Choice) :
    MatrixModel.cross (realX p) (realY p) = (numerator p : ℝ) := by
  change (∑ g : Active p, _) = _
  rw [show (numerator p : ℝ) = ∑ g : Active p, (cross (p.get g.val).kept : ℝ) from
    (active_sum p (cross ∘ Choice.kept) (by intro a h; simp [h, empty_scatter])).symm]
  apply Finset.sum_congr rfl
  intro g _
  rw [cross_running_sums]
  simp only [← Fin.sum_univ_fun_getElem]
  push_cast
  simp [realX, realY, Rows]

/-- The real matrix's within denominator is exactly the computed rational denominator. -/
theorem real_scatter (p : List Choice) :
    MatrixModel.scatter (realX p) = (denominator p : ℝ) := by
  change (∑ g : Active p, _) = _
  rw [show (denominator p : ℝ) = ∑ g : Active p, (variance (p.get g.val).kept : ℝ) from
    (active_sum p (variance ∘ Choice.kept) (by intro a h; simp [h, empty_scatter])).symm]
  apply Finset.sum_congr rfl
  intro g _
  rw [variance_running_sums]
  simp only [← Fin.sum_univ_fun_getElem]
  push_cast
  simp [realX, Rows, pow_two]

/-- Positive definiteness is derived from the actual retained data, with all empty
group dummies removed. This includes panels containing vanished groups. -/
theorem real_gram_posDef_iff (p : List Choice) :
    (MatrixModel.gram (realX p)).PosDef ↔ 0 < denominator p := by
  rw [MatrixModel.gram_posDef_iff, real_scatter]
  exact_mod_cast Iff.rfl

/-- The real inverse-matrix slope equals the rational scalar estimator used by
the algorithm, rather than merely satisfying one normal equation. -/
theorem real_inverse_slope (p : List Choice) (hv : 0 < denominator p) :
    ((MatrixModel.gram (realX p))⁻¹ *ᵥ MatrixModel.response (realX p) (realY p)) none =
      (slope p : ℝ) := by
  rw [MatrixModel.inverse_estimate _ _ (by rw [real_scatter]; exact_mod_cast hv)]
  change MatrixModel.cross (realX p) (realY p) / MatrixModel.scatter (realX p) = _
  rw [real_cross, real_scatter]
  exact (Rat.cast_div _ _).symm

/-- Actual inverse-matrix feasibility agrees with the optimizer's feasibility,
including the nondegeneracy test and refitting after groups disappear. -/
theorem matrix_feasible_iff (groups : List (List Point)) (p : List Choice) :
    (Valid groups p ∧ (MatrixModel.gram (realX p)).PosDef ∧
      ((MatrixModel.gram (realX p))⁻¹ *ᵥ MatrixModel.response (realX p) (realY p)) none ≤ 0) ↔
      Feasible groups p := by
  rw [real_gram_posDef_iff]
  constructor
  · rintro ⟨hp, hv, hs⟩
    rw [real_inverse_slope p hv] at hs
    exact ⟨hp, hv, by exact_mod_cast hs⟩
  · rintro ⟨hp, hv, hs⟩
    refine ⟨hp, hv, ?_⟩
    rw [real_inverse_slope p hv]
    exact_mod_cast hs

/-- Matrix feasibility after deleting the dummy of every vanished group. -/
@[expose] def MatrixFeasible (groups : List (List Point)) (p : List Choice) : Prop :=
  Valid groups p ∧ (MatrixModel.gram (realX p)).PosDef ∧
    ((MatrixModel.gram (realX p))⁻¹ *ᵥ MatrixModel.response (realX p) (realY p)) none ≤ 0

/-- Integral stability with the paper's refitting convention. Unlike the fixed-column
`LeastSquares.integralStability`, this allows a group and its dummy to disappear.
The natural infimum is zero when no feasible plan exists; the optimality theorem
below supplies a feasible plan explicitly. -/
@[expose] noncomputable def refittedIntegralStability (groups : List (List Point)) : ℕ :=
  sInf {k : ℕ | ∃ p, MatrixFeasible groups p ∧ k = deletions p}

/-- Any proved optimal feasible scalar plan computes the real matrix stability. -/
theorem refittedIntegralStability_eq (groups : List (List Point)) (p : List Choice)
    (hp : Feasible groups p) (hm : ∀ q, Feasible groups q → deletions p ≤ deletions q) :
    refittedIntegralStability groups = deletions p := by
  have hmat : MatrixFeasible groups p := (matrix_feasible_iff groups p).mpr hp
  apply le_antisymm
  · exact Nat.sInf_le ⟨p, hmat, rfl⟩
  · apply le_csInf (show {k : ℕ | ∃ q, MatrixFeasible groups q ∧ k = deletions q}.Nonempty
      from ⟨deletions p, p, hmat, rfl⟩)
    rintro k ⟨q, hq, rfl⟩
    exact hm q ((matrix_feasible_iff groups q).mp hq)

/-- End-to-end Theorem 4.1 matrix interpretation: the actual executed audit
returns a refitted inverse-matrix sign reversal with the optimal deletion count
and the already derived arithmetic-RAM resource bound. Nondegeneracy is exactly
the source's positive-scatter numerator minimizer condition. -/
theorem Resources.run_matrix_optimal (groups : List (List Point)) (T : ℕ) (r : Resources.Result)
    (hr : (Resources.run groups).ret = some r)
    (hne : ∀ g ∈ groups, g ≠ []) (hT : ∀ g ∈ groups, g.length ≤ T)
    (hfull : 0 < numerator (Resources.fullPlan groups))
    (hnd : ∃ q, Valid groups q ∧ deletions q = r.hit.index ∧
      numerator q = numerator r.hit.entry.plan ∧ 0 < denominator q) :
    MatrixFeasible groups r.hit.entry.plan ∧
      refittedIntegralStability groups = r.hit.index ∧
      (Resources.run groups).time ≤
        300 * (sampleSize groups * 2 ^ T +
          sampleSize groups * refittedIntegralStability groups) := by
  obtain ⟨hf, hm, ht⟩ := Resources.run_time_of_nondegenerate groups T r hr hne hT hfull hnd
  have hc := (Resources.run_spec groups r hr).2.1
  have he := refittedIntegralStability_eq groups r.hit.entry.plan hf (by simpa only [hc] using hm)
  rw [hc] at he
  exact ⟨(matrix_feasible_iff groups _).mpr hf, he, he ▸ ht⟩

end Cslib.LeastSquares.FixedEffects
