/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.PMF

/-!
# Some outcome is at least the mean

For a real-valued function on a finite type, some outcome that the distribution can produce is
at least the mean (`exists_mem_support_sum_mul_le`). This is the averaging step that fixes a good
choice after showing that a random choice is good on average. The opposite inequality for
`[0, ∞]`-valued functions on arbitrary types is
`Cslib.Probability.PMF.exists_mem_support_le_tsum_mul` in `CslibFrontier.Probability.Minimax`.

## Main results

* `Cslib.Probability.PMF.exists_mem_support_sum_mul_le`: some possible outcome is at least the mean.
-/

public section

namespace Cslib.Probability.PMF

variable {α : Type*} [Fintype α]

/-- **Some possible outcome is at least the mean** of a real-valued function on a finite type. -/
theorem exists_mem_support_sum_mul_le (μ : PMF α) (g : α → ℝ) :
    ∃ a ∈ μ.support, ∑ x, (μ x).toReal * g x ≤ g a := by
  by_contra! h
  obtain ⟨a, ha⟩ := μ.support_nonempty
  have hpos : 0 < ∑ x, (μ x).toReal * (∑ y, (μ y).toReal * g y - g x) := by
    refine Finset.sum_pos' (fun x _ => ?_)
      ⟨a, Finset.mem_univ _, mul_pos (ENNReal.toReal_pos ((μ.mem_support_iff a).mp ha)
        (μ.apply_ne_top a)) (sub_pos.mpr (h a ha))⟩
    by_cases hx : x ∈ μ.support
    · exact mul_nonneg ENNReal.toReal_nonneg (sub_nonneg.mpr (h x hx).le)
    · simp [(μ.apply_eq_zero_iff x).mpr hx]
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, sum_toReal, one_mul,
    sub_self] at hpos
  exact lt_irrefl _ hpos

end Cslib.Probability.PMF
