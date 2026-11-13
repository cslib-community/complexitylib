/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.MachineLearning.PACLearning.MulticlassPredictors
public import CslibFrontier.MachineLearning.PACLearning.Halfspaces

/-!
# Checks for the Natarajan dimension of multiclass predictors

Exercises `CslibFrontier.MachineLearning.PACLearning.MulticlassPredictors`:

* **Tie-breaking:** `argmaxFirst` returns the first maximal index, so one-versus-all predicts the
  first label whose classifier says `true`, and the first label when none does.
* **One-versus-all:** with homogeneous halfspaces in the plane and four labels, the Natarajan
  dimension is at most `24 log 12`.
* **The displayed bound of Lemmas 29.5 and 29.6:** with one classifier from a class that shatters
  one point, the reduction N-shatters that point, although `3 l d log (l d)` vanishes at
  `l = d = 1`.
* **Linear multiclass predictors:** the multivector construction with three labels on the plane
  has Natarajan dimension at most `6`, and with two labels on the line it N-shatters a point.
-/

public section

namespace CslibFrontierTests.MulticlassPredictors

open Cslib.MachineLearning.PACLearning

/-! ### Tie-breaking -/

/-- Two labels say `true`; one-versus-all picks the first of them. -/
example : argmaxFirst ![false, true, true] = 1 :=
  argmaxFirst_eq_iff.2 ⟨by decide, by decide⟩

/-- No label says `true`; one-versus-all falls back to the first label. -/
example : argmaxFirst (fun _ : Fin 3 => false) = 0 :=
  argmaxFirst_eq_iff.2 ⟨by decide, by decide⟩

/-! ### One-versus-all over halfspaces -/

/-- One-versus-all over homogeneous halfspaces in the plane with four labels. -/
example : HasFiniteNatarajanDim (oneVsAllClass (homogeneousHalfspaces 2) (Fin 4)) ∧
    (natarajanDim (oneVsAllClass (homogeneousHalfspaces 2) (Fin 4)) : ℝ) ≤ 24 * Real.log 12 := by
  have hH : HasFiniteVCDim (homogeneousHalfspaces 2) := by
    rw [homogeneousHalfspaces_eq_positivityClass]
    exact hasFiniteVCDim_positivityClass _
  have h := natarajanDim_oneVsAllClass_le (ι := Fin 4) hH
  rw [vcDim_homogeneousHalfspaces, Fintype.card_fin] at h
  refine ⟨h.1, h.2.trans_eq ?_⟩
  norm_num

/-! ### The displayed bound at `l = d = 1` -/

/-- The class of all labelings of one point shatters at most one point. -/
example (W : Finset Unit) (_ : SetShatters (Set.univ : ConceptClass Unit Bool) ↑W) :
    W.card ≤ 1 :=
  W.card_le_univ

/-- Reading off one classifier from that class, the reduction N-shatters the point, so its
Natarajan dimension is at least `1`, while `3 l d log (l d) = 0` for `l = d = 1`. -/
example : NatarajanShatters
    (reductionClass (Set.univ : ConceptClass Unit Bool) fun b : Unit → Bool => b ())
    (Set.univ : Set Unit) := by
  classical
  refine ⟨fun _ => true, fun _ => false, fun _ _ => Bool.noConfusion, fun B _ => ?_⟩
  refine ⟨fun x => decide (x ∈ B), mem_reductionClass.2 ⟨fun _ x => decide (x ∈ B),
    fun _ => Set.mem_univ _, rfl⟩, fun x hx => decide_eq_true hx, fun x hx => decide_eq_false hx.2⟩

example : 3 * (1 : ℝ) * 1 * Real.log (1 * 1) = 0 := by
  simp

/-! ### Linear multiclass predictors -/

/-- The multivector construction with three labels on the plane. -/
example : natarajanDim (linearArgmaxClass (multivectorScores (Fin 3) 2)) ≤ 6 := by
  simpa using (natarajanDim_linearArgmaxClass_multivectorScores_le (ι := Fin 3) 2).2

/-- With two labels on the line, the multivector predictors N-shatter the point `1`. -/
example : NatarajanShatters (linearArgmaxClass (multivectorScores (Fin 2) 1))
    {fun _ => 1} := by
  classical
  refine ⟨fun _ => 0, fun _ => 1, fun _ _ => Fin.zero_ne_one, fun B hB => ?_⟩
  by_cases hp : (fun _ : Fin 1 => (1 : ℝ)) ∈ B
  · refine ⟨_, mem_linearArgmaxClass.2 ⟨![fun _ => 1, fun _ => 0], rfl⟩, fun x hx => ?_,
      fun x hx => absurd (Set.mem_singleton_iff.1 hx.1 ▸ hp) hx.2⟩
    rw [Set.mem_singleton_iff.1 (hB hx)]
    refine argmaxFirst_eq_iff.2 ⟨fun j => ?_, fun j hj => absurd hj (Fin.not_lt_zero j)⟩
    fin_cases j <;> simp [dotProduct]
  · refine ⟨_, mem_linearArgmaxClass.2 ⟨![fun _ => 0, fun _ => 1], rfl⟩,
      fun x hx => absurd (Set.mem_singleton_iff.1 (hB hx) ▸ hx) hp, fun x hx => ?_⟩
    rw [Set.mem_singleton_iff.1 hx.1]
    refine argmaxFirst_eq_iff.2 ⟨fun j => ?_, fun j hj => ?_⟩
    · fin_cases j <;> simp [dotProduct]
    · fin_cases j
      · simp [dotProduct]
      · exact absurd hj (lt_irrefl _)

end CslibFrontierTests.MulticlassPredictors
