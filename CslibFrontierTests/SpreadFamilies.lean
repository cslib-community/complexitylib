/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Probability.Spread.Exceptional
import CslibFrontier.Probability.Spread.Selector

/-! Concrete integral/fractional covers, spread-law obstructions, selector values and the
finite minimax majorant. The conjectures themselves are not assumed or asserted here. -/

namespace CslibFrontierTests.SpreadFamilies
open Finset Cslib.Probability.Spread
open scoped BigOperators ENNReal

/-- A one-coordinate upper family has a one-generator cover of cost one quarter. -/
theorem coordinate_small : IsSmall (1 / 4) {J : Finset (Fin 2) | 0 ∈ J} := by
  refine ⟨{{0}}, ?_, ?_⟩
  · intro J hJ
    exact ⟨{0}, by simp, singleton_subset_iff.mpr hJ⟩
  · norm_num

/-- The integral cover constructs the probability witness, rather than supplying it as advice. -/
theorem coordinate_weakly_small : IsWeaklySmall (1 / 4) {J : Finset (Fin 2) | 0 ∈ J} :=
  coordinate_small.isWeaklySmall (by norm_num)

/-- Empty-set mass is a valid spread law even at rate zero. -/
theorem empty_spread : IsSpreadLaw 0 (PMF.pure (∅ : Finset (Fin 2))) :=
  isSpreadLaw_pure_empty le_rfl

/-- The whole cube is not weakly small: it supports the empty-set spread law. -/
theorem univ_not_weakly_small : ¬ IsWeaklySmall (1 / 4) (Set.univ : Set (Finset (Fin 2))) :=
  not_isWeaklySmall_of_spread (by norm_num)
    (isSpreadLaw_pure_empty (by norm_num)) (by simp)

/-- Hence it cannot have an integral cover of the advertised small cost either. -/
theorem univ_not_small : ¬ IsSmall (1 / 4) (Set.univ : Set (Finset (Fin 2))) :=
  fun h => univ_not_weakly_small (h.isWeaklySmall (by norm_num))

/-- Minimax produces a law supported by this concrete non-small family. -/
theorem univ_fractional_duality : ∃ ν : PMF (Finset (Fin 2)),
    IsSpreadLaw (1 / 2) ν ∧ ∀ J ∈ ν.support, J ∈ (Set.univ : Set (Finset (Fin 2))) := by
  convert exists_spread_of_not_isWeaklySmall (by norm_num : (0 : ℝ) < 1 / 4)
    univ_not_weakly_small using 1; norm_num

/-- A nonempty deterministic parent is not spread below rate one. -/
theorem singleton_not_spread : ¬ IsSpreadLaw (1 / 2) (PMF.pure ({0} : Finset (Fin 1))) := by
  intro h
  have hm := kernel_average_le_one (by norm_num : (0 : ℝ) < 1 / 2) h {0}
  simp only [PMF.pure_apply, apply_ite, ENNReal.toReal_one, ENNReal.toReal_zero,
    ite_mul, one_mul, zero_mul, sum_ite_eq', mem_univ, ite_true] at hm
  norm_num [upperKernel] at hm

/-- Selecting two unit coordinates from a singleton vector family gives exactly two. -/
theorem selector_two_units :
    selectorProcess ({fun _ : Fin 2 => (1 : ℝ≥0∞)} : Set (Fin 2 → ℝ≥0∞)) {0, 1} = 2 := by
  simp

/-- An actual kernel moment bound instantiates the majorant theorem without any conjecture. -/
theorem kernel_majorant : ∃ η : PMF (Finset (Fin 2)), ∀ J,
    upperKernel (1 / 4) {0} J ≤ coverScore (1 / 4) η J := by
  obtain ⟨η, hη⟩ := exists_coverScore_majorant (by norm_num : (0 : ℝ) < 1 / 4)
    (upperKernel (ι := Fin 2) (1 / 4) {0}) (upperKernel_nonneg (by norm_num) {0})
    (fun _ hν => kernel_average_le_one (by norm_num) hν {0})
  exact ⟨η, by simpa only [one_mul] using hη⟩

end CslibFrontierTests.SpreadFamilies
