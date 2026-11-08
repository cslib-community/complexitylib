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
independent draw from a probability measure `ν` gives a sample from the product in which the `i`th
factor is `ν`. Formally, the map `(v, z) ↦ Function.update v i z` sends `(Measure.pi μ).prod ν` to
`Measure.pi (Function.update μ i ν)`; for `ν = μ i` it preserves `Measure.pi μ`.

The integral form says that one can integrate over coordinate `i` first, while keeping the other
coordinates of the original sample. This avoids reindexing `ι` as `{i} ⊕ {j // j ≠ i}`.

Replacing the coordinates one at a time interpolates between two products `Measure.pi μ` and
`Measure.pi ν` through the *hybrids* `Measure.pi (s.piecewise ν μ)`, which draw the coordinates in
`s` from `ν` and the others from `μ`. Adding one coordinate `t` to `s` changes the integral of `F`
by the integral, over the hybrid for `s`, of the change caused by redrawing coordinate `t` from
`ν t` instead of `μ t` (`integral_pi_piecewise_insert_sub`). Summing these steps bounds the
difference between the two products (`abs_integral_pi_sub_le_sum`); this is the bookkeeping of
Lindeberg's replacement method.

## Main results

* `MeasureTheory.measurePreserving_update_measure`: replacing coordinate `i` by an independent draw
  from `ν` sends `(Measure.pi μ).prod ν` to `Measure.pi (Function.update μ i ν)`.
* `MeasureTheory.measurePreserving_update`: resampling coordinate `i` preserves `Measure.pi μ`.
* `MeasureTheory.integral_integral_update_measure`, `MeasureTheory.integral_integral_update`: the
  integral forms, for integrable `F`; for instance
  `∫ v, ∫ z, F (update v i z) ∂μ i ∂Measure.pi μ = ∫ v, F v ∂Measure.pi μ`.
* `MeasureTheory.integral_integral_update_swap`: the same with the coordinate `i` integrated last,
  `∫ z, ∫ v, F (update v i z) ∂Measure.pi μ ∂μ i = ∫ v, F v ∂Measure.pi μ`.
* `MeasureTheory.integral_pi_piecewise_insert_sub`: one step of the hybrid argument.
* `MeasureTheory.abs_integral_pi_sub_le_sum`: the hybrid argument, bounding
  `|∫ F ∂Measure.pi ν - ∫ F ∂Measure.pi μ|` by a sum of one-coordinate bounds.
-/

public section

namespace MeasureTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
  (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]

/-- Replacing coordinate `i` of a sample from a product of probability measures by an independent
draw from `ν`: `(v, z) ↦ Function.update v i z` maps `(Measure.pi μ).prod ν` to
`Measure.pi (Function.update μ i ν)`. -/
theorem measurePreserving_update_measure (i : ι) (ν : Measure (X i)) [IsProbabilityMeasure ν] :
    MeasurePreserving (fun p : (∀ j, X j) × X i => Function.update p.1 i p.2)
      ((Measure.pi μ).prod ν) (Measure.pi (Function.update μ i ν)) where
  measurable := measurable_update'
  map_eq := by
    have : ∀ j, IsProbabilityMeasure (Function.update μ i ν j) := fun j => by
      by_cases hj : j = i
      · subst hj; rw [Function.update_self]; infer_instance
      · rw [Function.update_of_ne hj]; infer_instance
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
      ← Finset.mul_prod_erase (s := Finset.univ) (fun j => Function.update μ i ν j (s j))
        (Finset.mem_univ i),
      Function.update_self, Function.update_self, measure_univ, one_mul, mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj),
      Function.update_of_ne (Finset.ne_of_mem_erase hj)]

/-- Resampling coordinate `i` of a product of probability measures preserves the product:
`(v, z) ↦ Function.update v i z` maps `(Measure.pi μ).prod (μ i)` to `Measure.pi μ`. -/
theorem measurePreserving_update (i : ι) :
    MeasurePreserving (fun p : (∀ j, X j) × X i => Function.update p.1 i p.2)
      ((Measure.pi μ).prod (μ i)) (Measure.pi μ) := by
  simpa using measurePreserving_update_measure μ i (μ i)

/-- **Fubini over one coordinate, with a new law for it.** Integrating `F` against the product in
which the `i`th factor is replaced by `ν` is the same as first integrating over an independent
draw of coordinate `i` from `ν`, keeping the other coordinates of a sample from `Measure.pi μ`. -/
theorem integral_integral_update_measure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : ι) (ν : Measure (X i)) [IsProbabilityMeasure ν] {F : (∀ j, X j) → E}
    (hF : Integrable F (Measure.pi (Function.update μ i ν))) :
    ∫ v, ∫ z, F (Function.update v i z) ∂ν ∂Measure.pi μ =
      ∫ v, F v ∂Measure.pi (Function.update μ i ν) := by
  have hΦ := measurePreserving_update_measure μ i ν
  have hint : Integrable (fun p : (∀ j, X j) × X i => F (Function.update p.1 i p.2))
      ((Measure.pi μ).prod ν) := hΦ.integrable_comp_of_integrable hF
  rw [← integral_prod _ hint]
  conv_rhs => rw [← hΦ.map_eq]
  rw [integral_map hΦ.measurable.aemeasurable (by rw [hΦ.map_eq]; exact hF.aestronglyMeasurable)]

/-- The inner integral of `integral_integral_update_measure` is integrable in the outer sample. -/
theorem integrable_integral_update_measure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : ι) (ν : Measure (X i)) [IsProbabilityMeasure ν] {F : (∀ j, X j) → E}
    (hF : Integrable F (Measure.pi (Function.update μ i ν))) :
    Integrable (fun v => ∫ z, F (Function.update v i z) ∂ν) (Measure.pi μ) :=
  ((measurePreserving_update_measure μ i ν).integrable_comp_of_integrable hF).integral_prod_left

/-- **Fubini over one coordinate.** Integrating `F` against a product of probability measures is
the same as first integrating over a fresh draw of coordinate `i`, keeping the other coordinates
of the outer sample. -/
theorem integral_integral_update {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : (∀ j, X j) → E} (hF : Integrable F (Measure.pi μ)) (i : ι) :
    ∫ v, ∫ z, F (Function.update v i z) ∂μ i ∂Measure.pi μ = ∫ v, F v ∂Measure.pi μ := by
  simpa using integral_integral_update_measure μ i (μ i) (F := F) (by simpa using hF)

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

/-! ### Hybrids of two product measures -/

variable (ν : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (ν i)]

omit [Fintype ι] [DecidableEq ι] in
/-- The factors of a hybrid of two families of probability measures are probability measures. -/
theorem isProbabilityMeasure_piecewise (s : Finset ι) [∀ i, Decidable (i ∈ s)] (i : ι) :
    IsProbabilityMeasure (s.piecewise ν μ i) := by
  by_cases h : i ∈ s
  · rw [Finset.piecewise_eq_of_mem _ _ _ h]; infer_instance
  · rw [Finset.piecewise_eq_of_notMem _ _ _ h]; infer_instance

/-- **One step of the hybrid argument.** Moving coordinate `t ∉ s` from `μ t` to `ν t` changes the
integral of `F` over the hybrid `Measure.pi (s.piecewise ν μ)` by the integral, over that hybrid,
of the change caused by redrawing coordinate `t` from `ν t` instead of `μ t`. -/
theorem integral_pi_piecewise_insert_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : (∀ j, X j) → E} {s : Finset ι} {t : ι} (ht : t ∉ s)
    (hF : ∀ s : Finset ι, Integrable F (Measure.pi (s.piecewise ν μ))) :
    ∫ v, F v ∂Measure.pi ((insert t s).piecewise ν μ) - ∫ v, F v ∂Measure.pi (s.piecewise ν μ) =
      ∫ v, (∫ z, F (Function.update v t z) ∂ν t - ∫ z, F (Function.update v t z) ∂μ t)
        ∂Measure.pi (s.piecewise ν μ) := by
  have := isProbabilityMeasure_piecewise μ ν s
  have e1 : Function.update (s.piecewise ν μ) t (ν t) = (insert t s).piecewise ν μ := by
    rw [Finset.piecewise_insert]
  have e2 : Function.update (s.piecewise ν μ) t (μ t) = s.piecewise ν μ := by
    rw [Function.update_eq_self_iff, Finset.piecewise_eq_of_notMem _ _ _ ht]
  have hF1 : Integrable F (Measure.pi (Function.update (s.piecewise ν μ) t (ν t))) := by
    rw [e1]; exact hF _
  have hF2 : Integrable F (Measure.pi (Function.update (s.piecewise ν μ) t (μ t))) := by
    rw [e2]; exact hF _
  have hI1 := integral_integral_update_measure (s.piecewise ν μ) t (ν t) hF1
  have hI2 := integral_integral_update_measure (s.piecewise ν μ) t (μ t) hF2
  rw [e1] at hI1
  rw [e2] at hI2
  rw [← hI1, ← hI2, integral_sub (integrable_integral_update_measure _ t _ hF1)
    (integrable_integral_update_measure _ t _ hF2)]

omit [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)] in
/-- **The hybrid argument.** If, for every `s` and `t ∉ s`, moving coordinate `t` of the hybrid
`Measure.pi (s.piecewise ν μ)` from `μ t` to `ν t` changes the integral of `F` by at most `δ t`,
then the integrals of `F` over `Measure.pi μ` and `Measure.pi ν` differ by at most `∑ t, δ t`. -/
theorem abs_integral_pi_sub_le_sum {F : (∀ j, X j) → ℝ} (δ : ι → ℝ)
    (hδ : ∀ (s : Finset ι) (t : ι), t ∉ s →
      |∫ v, F v ∂Measure.pi ((insert t s).piecewise ν μ) -
        ∫ v, F v ∂Measure.pi (s.piecewise ν μ)| ≤ δ t) :
    |∫ v, F v ∂Measure.pi μ - ∫ v, F v ∂Measure.pi ν| ≤ ∑ t, δ t := by
  have key (s : Finset ι) :
      |∫ v, F v ∂Measure.pi (s.piecewise ν μ) - ∫ v, F v ∂Measure.pi μ| ≤ ∑ t ∈ s, δ t := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert t s ht ih =>
      rw [Finset.sum_insert ht]
      exact (abs_sub_le _ (∫ v, F v ∂Measure.pi (s.piecewise ν μ)) _).trans
        (add_le_add (hδ s t ht) ih)
  have h := key Finset.univ
  rwa [Finset.piecewise_univ, abs_sub_comm] at h

end MeasureTheory
