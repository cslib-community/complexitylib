/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyParams

/-!
# Bounded atom cutoff for pilot and actual hierarchy rows

The exact hierarchy uses `Q`, whereas computed rows use the bounded scalar extension
`Qat(d) = Q(clip_[0,B_Q](d))` of [OpenAI2026LogSpace, Section 5.3, preceding (5.14)],
revision `7ef5c0cc`. The fixed cap exceeds `k+1` and `θ₂`. Both pilot and actual input bounds
therefore imply agreement on true entries. Only the scalar argument is clipped: ranks and
incoming scores continue to use the raw matrix. These algebraic bounds alone do not supply
root regularity, a recursive error bound or the global estimator.

## Main definitions

* `Matrix.HierarchyParams.atomCap`: fixed input cap.
* `Matrix.HierarchyParams.atomCutoff`: bounded scalar cutoff for estimated rows.

## Main results

* `Matrix.HierarchyParams.atomCutoff_eq`: agreement on the true nonnegative input range.
* `Matrix.HierarchyParams.atomCutoff_le`: uniform bound for arbitrary real inputs.
-/

public section

namespace Matrix.HierarchyParams

/-- Fixed source atom cap, strictly above the hierarchy input bound `k + 1` and `θ₂`.
This is `B_Q` of [OpenAI2026LogSpace, Section 5.3], not a cap on raw matrices. -/
@[expose] noncomputable def atomCap {q cπ Cπ Cpair Cvar : ℝ}
    (P : HierarchyParams q cπ Cπ Cpair Cvar) : ℝ :=
  max ((P.k : ℝ) + 1) P.θ₂ + 1

/-- The source's bounded scalar cutoff `Qat`. Ranks and incoming scores must continue to use
unclipped child entries [OpenAI2026LogSpace, Section 5.3, before (5.14)]. -/
@[expose] noncomputable def atomCutoff {q cπ Cπ Cpair Cvar : ℝ}
    (P : HierarchyParams q cπ Cπ Cpair Cvar) (d : ℝ) : ℝ :=
  P.Q (min P.atomCap (max 0 d))

variable {q cπ Cπ Cpair Cvar : ℝ} (P : HierarchyParams q cπ Cπ Cpair Cvar)

/-- The chosen atom cap exceeds both source lower bounds. -/
theorem atomCap_gt : max ((P.k : ℝ) + 1) P.θ₂ < P.atomCap := by
  unfold atomCap
  linarith

/-- The bounded extension is nonnegative for every real estimate. -/
theorem atomCutoff_nonneg (d : ℝ) : 0 ≤ P.atomCutoff d := P.Q_nonneg _

/-- Uniform bound on the scalar cutoff, independent of the child estimate. -/
theorem atomCutoff_le (d : ℝ) : P.atomCutoff d ≤ P.Q P.atomCap :=
  P.Q_mono (min_le_left _ _)

/-- The bounded extension agrees with the hierarchy cutoff on its nonnegative true range. -/
theorem atomCutoff_eq {d : ℝ} (hd : 0 ≤ d) (hdk : d ≤ (P.k : ℝ) + 1) :
    P.atomCutoff d = P.Q d := by
  have hcap : d ≤ P.atomCap := hdk.trans ((le_max_left _ _).trans P.atomCap_gt.le)
  simp only [atomCutoff, max_eq_right hd, min_eq_right hcap]

/-- Nonpositive estimates give zero, as required by the source extension. -/
theorem atomCutoff_eq_zero {d : ℝ} (hd : d ≤ 0) : P.atomCutoff d = 0 := by
  have hcap : 0 ≤ P.atomCap := by
    have hk : (0 : ℝ) ≤ P.k := Nat.cast_nonneg _
    have hm := le_max_left ((P.k : ℝ) + 1) P.θ₂
    have hg := P.atomCap_gt
    linarith
  have hQ : P.Q 0 = 0 := le_antisymm (by
    simpa only [zero_sub, max_eq_right (neg_nonpos.mpr P.θ_pos.le)] using P.Q_le 0)
    (P.Q_nonneg 0)
  simp only [atomCutoff, max_eq_left hd, min_eq_right hcap, hQ]

/-- The bounded extension does not introduce support absent from the original cutoff. -/
theorem atomCutoff_eq_zero_of_Q_eq_zero {d : ℝ} (hd : P.Q d = 0) :
    P.atomCutoff d = 0 := by
  by_cases hd0 : d ≤ 0
  · exact P.atomCutoff_eq_zero hd0
  · apply le_antisymm _ (P.atomCutoff_nonneg d)
    calc
      P.atomCutoff d ≤ P.Q d := P.Q_mono (by
        exact (min_le_right _ _).trans (by rw [max_eq_right (not_le.mp hd0).le]))
      _ = 0 := hd

end Matrix.HierarchyParams
