/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.MachineLearning.PACLearning.NatarajanLowerBound
public import CslibFrontier.MachineLearning.PACLearning.NatarajanUpperBound
public import CslibFrontierTests.NatarajanDimension

/-!
# Checks for the multiclass lower bound

Exercises `CslibFrontier.MachineLearning.PACLearning.NatarajanLowerBound`:

* **Characterization:** the constant functions from `ℕ` to `Fin 3` are PAC learnable in the
  realizable setting through the characterization. The class of all functions from `ℕ` to
  `Fin 3` has infinite Natarajan dimension, so it is learnable neither in the realizable setting
  nor agnostically.
* **Explicit sample sizes:** ten examples do not suffice to learn all functions from `ℕ` to
  `Fin 3` to accuracy `1/8` with confidence `14/15`, because the class N-shatters `{0, …, 41}`.
  As a nonvacuity check, zero examples do not learn all functions from `Fin 3` to `Fin 3`, even
  agnostically. On `Fin 5` the realizable sample complexity is at least `1`.
-/

public section

namespace CslibFrontierTests.NatarajanLowerBound

open Cslib.MachineLearning.PACLearning CslibFrontierTests.NatarajanDimension
open scoped NNReal

/-- The accuracy `1/8`. -/
noncomputable def eighth : Set.Ioo (0 : ℝ≥0) 1 := ⟨1 / 8, by norm_num, by norm_num⟩

/-- The confidence parameter `1/15`. -/
noncomputable def fifteenth : Set.Ioo (0 : ℝ≥0) 1 := ⟨1 / 15, by norm_num, by norm_num⟩

theorem eighth_le : ((eighth : ℝ≥0) : ℝ) ≤ 1 / 8 := by
  norm_num [eighth]

theorem fifteenth_lt : ((fifteenth : ℝ≥0) : ℝ) < 1 / 14 := by
  norm_num [fifteenth]

/-- On an infinite domain the class of all functions to `Fin 3` has infinite Natarajan
dimension. -/
theorem not_hasFiniteNatarajanDim_univ {α : Type*} [Infinite α] :
    ¬ HasFiniteNatarajanDim (Set.univ : ConceptClass α (Fin 3)) := by
  intro h
  obtain ⟨N, hN⟩ := hasFiniteNatarajanDim_iff.1 h
  obtain ⟨W, hW⟩ := Infinite.exists_subset_card_eq α (N + 1)
  have := hN W (natarajanShatters_univ (b₀ := 0) (b₁ := 1) (by decide) _)
  omega

/-- The constant functions from `ℕ` to `Fin 3` are PAC learnable in the realizable setting,
through the characterization. -/
example : IsPACLearnable (constants (α := ℕ) (Fin 3))
    (realizableDistributions (constants (α := ℕ) (Fin 3))) :=
  isPACLearnable_realizableDistributions_iff_hasFiniteNatarajanDim.2
    (hasFiniteNatarajanDim_iff.2 ⟨1, fun _ hW => card_le_one_of_natarajanShatters_constants hW⟩)

/-- All functions from `ℕ` to `Fin 3` are not PAC learnable in the realizable setting. -/
example : ¬ IsPACLearnable (Set.univ : ConceptClass ℕ (Fin 3)) (realizableDistributions Set.univ) :=
  fun h => not_hasFiniteNatarajanDim_univ
    (isPACLearnable_realizableDistributions_iff_hasFiniteNatarajanDim.1 h)

/-- All functions from `ℕ` to `Fin 3` are not agnostically PAC learnable. -/
example : ¬ IsPACLearnable (Set.univ : ConceptClass ℕ (Fin 3)) Set.univ :=
  fun h => not_hasFiniteNatarajanDim_univ (h.hasFiniteNatarajanDim (Set.subset_univ _))

/-- Ten examples do not suffice to learn all functions from `ℕ` to `Fin 3` to accuracy `1/8` with
confidence `14/15`: the class N-shatters `{0, …, 41}`, and `42 > 32 · (1/8) · 10 + 1`. -/
example : ¬ IsPACLearnerFor 10 eighth fifteenth (Set.univ : ConceptClass ℕ (Fin 3))
    (realizableDistributions Set.univ) := by
  intro h
  have := card_le_of_natarajanShatters_of_isPACLearnerFor (W := Finset.range 42)
    (natarajanShatters_univ (b₀ := 0) (b₁ := 1) (by decide) _) eighth_le fifteenth_lt subset_rfl h
  norm_num [eighth] at this

/-- Nonvacuity: zero examples do not learn all functions from `Fin 3` to `Fin 3` to accuracy `1/8`
with confidence `14/15`, even agnostically. -/
example : ¬ IsPACLearnerFor 0 eighth fifteenth (Set.univ : ConceptClass (Fin 3) (Fin 3))
    Set.univ := by
  intro h
  have := card_le_of_natarajanShatters_of_isPACLearnerFor (W := Finset.univ)
    (natarajanShatters_univ (b₀ := 0) (b₁ := 1) (by decide) _) eighth_le fifteenth_lt
    (Set.subset_univ _) h
  norm_num at this

/-- All functions from `Fin 5` to `Fin 3` have Natarajan dimension `5`, so their realizable sample
complexity at accuracy `1/8` and confidence `14/15` is at least `(5 - 1) / (32 / 8) = 1`. -/
example : 1 ≤ sampleComplexity IsPACLearnerFor (Set.univ : ConceptClass (Fin 5) (Fin 3)) eighth
    fifteenth (realizableDistributions Set.univ) := by
  have hlearn := isPACLearnable_realizableDistributions_of_hasFiniteNatarajanDim
    (hasFiniteNatarajanDim_of_finite (Set.univ : ConceptClass (Fin 5) (Fin 3)))
  have h := sampleComplexity_lower_bound_natarajanDim eighth_le fifteenth_lt subset_rfl
    (hlearn eighth fifteenth)
  rw [natarajanDim_univ (b₀ := (0 : Fin 3)) (b₁ := 1) (by decide)] at h
  norm_num [eighth] at h
  exact_mod_cast h

end CslibFrontierTests.NatarajanLowerBound
