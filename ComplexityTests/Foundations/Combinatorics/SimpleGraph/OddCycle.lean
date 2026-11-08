/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexity.Foundations.Combinatorics.SimpleGraph.OddCycle
public import Complexity.Foundations.Combinatorics.SimpleGraph.Pentagon

public section

open SimpleGraph Real
open scoped RealInnerProductSpace

namespace Cslib.Tests.OddCycle

/-! ### Both representations are instances for every odd `n ≥ 3` -/

example : (cycleGraph 7).IsOrthonormalRepresentation (oddCycleFourier 7) :=
  isOrthonormalRepresentation_oddCycleFourier (by decide) (by norm_num)

example : (cycleGraph 7)ᶜ.IsOrthonormalRepresentation (oddCycleComplUmbrella 7) :=
  isOrthonormalRepresentation_oddCycleComplUmbrella (by decide) (by norm_num)

/-- The Fourier representation of `C₅` is not a representation of `C₅ᶜ`: the vertices `0` and `1`
are nonadjacent in `C₅ᶜ` but their vectors have inner product `1 / (2 cos (π/5)) ≠ 0`. -/
example : ¬(cycleGraph 5)ᶜ.IsOrthonormalRepresentation (oddCycleFourier 5) := by
  intro h
  have h0 := h.inner_eq_zero (v := 0) (w := 1) (by decide) (by decide)
  have hc : 0 < cos (π / 5) := by rw [cos_pi_div_five]; positivity
  rw [inner_oddCycleFourier (by decide) (by norm_num), sum_oddCycleWeight_mul_cos (by norm_num),
    ite_eq_right (by decide), ite_eq_left (by decide), ite_eq_right (by decide)] at h0
  have : (0 : ℝ) < ((0 + ((0 : ℝ) + 5)) / (2 * cos (π / ((5 : ℕ) : ℝ)))) / ((5 : ℕ) : ℝ) := by
    push_cast
    positivity
  push_cast at h0 this
  linarith

/-! ### Edge cases of the formula -/

/-- For `n = 3` the formula gives `ϑ(K₃) = 1`. -/
example : (cycleGraph 3).lovaszTheta = 1 := by
  rw [lovaszTheta_cycleGraph_of_odd (by decide) le_rfl]
  push_cast
  rw [cos_pi_div_three]
  norm_num

/-- For `n = 5` the formula agrees with `ϑ(C₅) = √5` from the pentagon umbrella. -/
example : (5 : ℕ) * cos (π / (5 : ℕ)) / (1 + cos (π / (5 : ℕ))) = (cycleGraph 5).lovaszTheta := by
  rw [lovaszTheta_cycleGraph_five]
  push_cast
  rw [cos_pi_div_five]
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h5pos : 0 < √5 := by positivity
  field_simp
  linear_combination -h5

/-- `ϑ(C₅) ϑ(C₅ᶜ) = 5`. -/
example : (cycleGraph 5).lovaszTheta * (cycleGraph 5)ᶜ.lovaszTheta = 5 := by
  exact_mod_cast lovaszTheta_cycleGraph_mul_compl_of_odd (n := 5) (by decide) (by norm_num)

/-! ### The heptagon: `3 ≤ ϑ(C₇) < 7/2` -/

example : (cycleGraph 7).shannonCapacity < 7 / 2 := by
  have hc : 0 < cos (π / (7 : ℕ)) := by
    apply cos_pos_of_mem_Ioo
    constructor <;> push_cast <;> linarith [pi_pos]
  have hc1 : cos (π / (7 : ℕ)) < 1 := by
    rw [← cos_zero]
    apply cos_lt_cos_of_nonneg_of_le_pi le_rfl
    · push_cast; linarith [pi_pos]
    · push_cast; positivity
  refine (shannonCapacity_cycleGraph_le_of_odd (by decide) (by norm_num)).trans_lt ?_
  rw [div_lt_div_iff₀ (by positivity) two_pos]
  push_cast at hc hc1 ⊢
  nlinarith

end Cslib.Tests.OddCycle
