/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Probability/Independence/InfinitePi.lean`)

public import Complexity.Foundations.Probability.SecondMoment
public import Mathlib.Probability.Independence.InfinitePi

/-!
# Local events of an infinite product are independent

Under the product `Measure.infinitePi P` of arbitrarily many probability measures, functions of
disjoint finite sets of coordinates (in the sense of `DependsOn`) are independent. This is the
infinite-product counterpart of `ProbabilityTheory.indepFun_pi_of_dependsOn`; it is what makes the
checks of distinct vertices of a witness structure independent in the Moser–Tardos analysis of the
algorithmic local lemma.

## Main results

* `ProbabilityTheory.indepFun_infinitePi_of_dependsOn`,
  `ProbabilityTheory.indepSet_infinitePi_of_dependsOn`: functions and events of disjoint finite
  sets of coordinates are independent under `Measure.infinitePi`.
-/

@[expose] public section

open MeasureTheory Finset

namespace ProbabilityTheory

variable {ι : Type*} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
  {P : ∀ i, Measure (Ω i)} [∀ i, IsProbabilityMeasure (P i)]

/-- **Functions of disjoint finite sets of coordinates are independent** under an infinite product
of probability measures. -/
theorem indepFun_infinitePi_of_dependsOn {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    {f : (Π i, Ω i) → β} {g : (Π i, Ω i) → γ} (hf : Measurable f) (hg : Measurable g)
    {S T : Finset ι} (hfS : DependsOn f (S : Set ι)) (hgT : DependsOn g (T : Set ι))
    (hST : Disjoint S T) : IndepFun f g (Measure.infinitePi P) := by
  obtain ⟨ω₀⟩ := nonempty_of_isProbabilityMeasure (Measure.infinitePi P)
  obtain ⟨f', hf', rfl⟩ := exists_measurable_comp_restrict hf hfS ω₀
  obtain ⟨g', hg', rfl⟩ := exists_measurable_comp_restrict hg hgT ω₀
  have hind : iIndepFun (fun i (ω : Π i, Ω i) => ω i) (Measure.infinitePi P) :=
    iIndepFun_infinitePi (X := fun _ x => x) fun _ => measurable_id
  exact (hind.indepFun_finset _ _ hST fun i => measurable_pi_apply i).comp hf' hg'

/-- **Events of disjoint finite sets of coordinates are independent** under an infinite product of
probability measures. -/
theorem indepSet_infinitePi_of_dependsOn {A B : Set (Π i, Ω i)} (hA : MeasurableSet A)
    (hB : MeasurableSet B) {S T : Finset ι} (hAS : DependsOn (· ∈ A) (S : Set ι))
    (hBT : DependsOn (· ∈ B) (T : Set ι)) (hST : Disjoint S T) :
    IndepSet A B (Measure.infinitePi P) := by
  have h := (indepFun_infinitePi_of_dependsOn (P := P) (measurable_mem.2 hA)
    (measurable_mem.2 hB) hAS hBT hST).measure_inter_preimage_eq_mul {True} {True}
      (measurableSet_singleton _) (measurableSet_singleton _)
  have hpre : ∀ C : Set (Π i, Ω i), (· ∈ C) ⁻¹' {True} = C := fun C => by
    ext
    simp
  rw [hpre, hpre] at h
  exact (indepSet_iff_measure_inter_eq_mul hA hB _).2 h

end ProbabilityTheory
