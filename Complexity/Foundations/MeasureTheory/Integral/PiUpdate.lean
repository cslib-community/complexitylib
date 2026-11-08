/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/MeasureTheory/Constructions/Pi.lean`)

public import Complexity.Init
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Resampling one coordinate of a product measure

Under a product `Measure.pi μ` of probability measures, replacing coordinate `i` of a sample by an
independent draw from `μ i` does not change the distribution. Formally, the map
`(v, z) ↦ Function.update v i z` sends `(Measure.pi μ).prod (μ i)` to `Measure.pi μ`.

The integral form says that one can integrate over coordinate `i` first, while keeping the other
coordinates of the original sample. This avoids reindexing `ι` as `{i} ⊕ {j // j ≠ i}`.

## Main results

* `MeasureTheory.measurePreserving_update`: resampling coordinate `i` preserves `Measure.pi μ`.
* `MeasureTheory.integral_integral_update`: for integrable `F`,
  `∫ v, ∫ z, F (update v i z) ∂μ i ∂Measure.pi μ = ∫ v, F v ∂Measure.pi μ`.
* `MeasureTheory.integral_integral_update_swap`: the same with the coordinate `i` integrated last,
  `∫ z, ∫ v, F (update v i z) ∂Measure.pi μ ∂μ i = ∫ v, F v ∂Measure.pi μ`.
-/

public section

namespace MeasureTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
  (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]

/-- Resampling coordinate `i` of a product of probability measures preserves the product:
`(v, z) ↦ Function.update v i z` maps `(Measure.pi μ).prod (μ i)` to `Measure.pi μ`. -/
theorem measurePreserving_update (i : ι) :
    MeasurePreserving (fun p : (∀ j, X j) × X i => Function.update p.1 i p.2)
      ((Measure.pi μ).prod (μ i)) (Measure.pi μ) where
  measurable := measurable_update'
  map_eq := by
    symm
    refine Measure.pi_eq fun s hs => ?_
    rw [Measure.map_apply measurable_update' (MeasurableSet.univ_pi hs)]
    have hpre : (fun p : (∀ j, X j) × X i => Function.update p.1 i p.2) ⁻¹' Set.univ.pi s =
        (Set.univ.pi (Function.update s i Set.univ)) ×ˢ s i := by
      ext ⟨v, z⟩
      simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_prod]
      constructor
      · intro h
        refine ⟨fun j => ?_, by simpa using h i⟩
        by_cases hj : j = i
        · subst hj; simp
        · simpa [Function.update_of_ne hj] using h j
      · rintro ⟨h1, h2⟩ j
        by_cases hj : j = i
        · subst hj; simpa using h2
        · simpa [Function.update_of_ne hj] using h1 j
    rw [hpre, Measure.prod_prod, Measure.pi_pi,
      ← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
      ← Finset.mul_prod_erase (s := Finset.univ) (fun j => μ j (s j)) (Finset.mem_univ i),
      Function.update_self, measure_univ, one_mul, mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

/-- **Fubini over one coordinate.** Integrating `F` against a product of probability measures is
the same as first integrating over a fresh draw of coordinate `i`, keeping the other coordinates
of the outer sample. -/
theorem integral_integral_update {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : (∀ j, X j) → E} (hF : Integrable F (Measure.pi μ)) (i : ι) :
    ∫ v, ∫ z, F (Function.update v i z) ∂μ i ∂Measure.pi μ = ∫ v, F v ∂Measure.pi μ := by
  have hΦ := measurePreserving_update μ i
  have hint : Integrable (fun p : (∀ j, X j) × X i => F (Function.update p.1 i p.2))
      ((Measure.pi μ).prod (μ i)) := hΦ.integrable_comp_of_integrable hF
  rw [← integral_prod _ hint]
  conv_rhs => rw [← hΦ.map_eq]
  rw [integral_map hΦ.measurable.aemeasurable (by rw [hΦ.map_eq]; exact hF.aestronglyMeasurable)]

/-- **Fubini over one coordinate, outer form.** Integrating `F` against a product of probability
measures is the same as first fixing coordinate `i` to `z`, averaging over the other coordinates,
and then integrating over `z ∼ μ i`. -/
theorem integral_integral_update_swap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : (∀ j, X j) → E} (hF : Integrable F (Measure.pi μ)) (i : ι) :
    ∫ z, ∫ v, F (Function.update v i z) ∂Measure.pi μ ∂μ i = ∫ v, F v ∂Measure.pi μ := by
  have hint : Integrable (Function.uncurry fun (v : ∀ j, X j) (z : X i) =>
      F (Function.update v i z)) ((Measure.pi μ).prod (μ i)) :=
    (measurePreserving_update μ i).integrable_comp_of_integrable hF
  rw [← integral_integral_swap hint, integral_integral_update μ hF i]

end MeasureTheory
