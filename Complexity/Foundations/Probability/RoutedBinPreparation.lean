/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.DenseRowRecipes
public import Complexity.Foundations.Probability.FourthRootHierarchyParams
public import Complexity.Foundations.Probability.PolynomialAtomCutoffs

/-!
# Polynomial preparation for routed bins

The existing polynomial preparation cutoff supplies a concrete light-input support
and covering plateau for every bounded routed numerator. Its fourth-root regularity
is inherited from the polynomial switch. These primitive laws do not prove canonical
compressed-output accuracy or a lower-budget correctness invariant.

## Main results

* `Matrix.FourthRootHierarchyParams.routedBin_prep_eq_one`: preparation covers every
  nonzero routed numerator.
* `Matrix.FourthRootHierarchyParams.routedBin_prep_laws`: range, vanishing, covering
  plateau and fourth-root regularity for the actual preparation choice.
-/
public section

namespace Matrix.FourthRootHierarchyParams
open Cslib

/-- The existing polynomial preparation covers every bounded routed-bin numerator.
The numerator starts above `1/2`, well beyond the hierarchy preparation's plateau. -/
theorem routedBin_prep_eq_one
    (HP : FourthRootHierarchyParams 16 1 16 32 8)
    {χ : ℝ → ℝ} {b : ℕ → ℝ} {cap d : ℝ}
    (hcap : 0 ≤ cap) (hχ : ∀ v, v ≤ 1 / 2 → χ v = 0)
    (hb : ∀ i, 0 < b i) (hanti : Antitone b) (i : ℕ) (route : ℝ → ℝ)
    (hd : boundedRoutedBinCutoff χ b cap i route d ≠ 0) :
    polynomialPrepCutoff4 HP.θ d = 1 := by
  have hhalf : 1 / 2 < d := lt_of_not_ge fun h =>
    hd (boundedRoutedBinCutoff_eq_zero hcap hχ hb hanti h i route)
  have hθ := HP.θ_lt_θ₂.trans HP.θ₂_lt
  norm_num at hθ
  exact polynomialPrepCutoff4_eq_one HP.θ_pos (by linarith)

/-- A single concrete preparation has the range, light-input support, bin-covering
plateau and fourth-root regularity needed by the routed-bin accuracy route.
Its constants are selected before the bin scales, routing function or input. -/
theorem routedBin_prep_laws
    (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    (∀ v, polynomialPrepCutoff4 HP.θ v ∈ Set.Icc 0 1) ∧
    (∀ v, v ≤ HP.θ / 2 → polynomialPrepCutoff4 HP.θ v = 0) ∧
    (∀ (χ : ℝ → ℝ) (b : ℕ → ℝ) (cap : ℝ), 0 ≤ cap →
      (∀ v, v ≤ 1 / 2 → χ v = 0) → (∀ i, 0 < b i) → Antitone b →
      ∀ i (route : ℝ → ℝ) d, boundedRoutedBinCutoff χ b cap i route d ≠ 0 →
        polynomialPrepCutoff4 HP.θ d = 1) ∧
    ∃ L : ℝ, 0 ≤ L ∧ ∀ v w,
      |polynomialPrepCutoff4 HP.θ v ^ (4⁻¹ : ℝ) -
        polynomialPrepCutoff4 HP.θ w ^ (4⁻¹ : ℝ)| ≤ L * |v - w| := by
  refine ⟨fun v => ⟨polynomialPrepCutoff4_nonneg _ _, polynomialPrepCutoff4_le_one _ _⟩,
    fun v hv => polynomialPrepCutoff4_eq_zero HP.θ_pos hv, ?_, ?_⟩
  · intro χ b cap hcap hχ hb hanti i route d hd
    exact routedBin_prep_eq_one HP hcap hχ hb hanti i route hd
  · obtain ⟨L, hL⟩ := exists_lipschitzWith_polynomialSwitch4_root
      (HP.θ / 2) (3 * HP.θ / 4)
    refine ⟨L, L.coe_nonneg, ?_⟩
    intro v w
    simpa only [polynomialPrepCutoff4, Real.dist_eq] using hL.dist_le_mul v w

end Matrix.FourthRootHierarchyParams
