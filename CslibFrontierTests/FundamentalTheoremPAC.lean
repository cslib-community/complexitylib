/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.MachineLearning.PACLearning.FundamentalTheorem
import CslibFrontier.MachineLearning.PACLearning.VCLowerBound
import CslibFrontierTests.RealizablePAC

/-! Checks for the EHKV lower bound on general domains and the realizable characterization of PAC
learnability by finite VC dimension: thresholds on `ℕ` are learnable through the characterization;
the class of all Boolean functions is neither realizably nor agnostically learnable on `ℕ`, nor on
the uncountable, non-discrete domain `ℝ`; ten examples do not suffice to learn all Boolean
functions on `ℕ` to accuracy `1/8` and confidence `14/15`, matching the explicit constant of the
lower bound; and, as a nonvacuity check, zero examples do not learn all Boolean functions on
`Fin 3`. -/

namespace CslibFrontierTests.FundamentalTheoremPAC

open Cslib.MachineLearning.PACLearning MeasureTheory
open CslibFrontierTests.RealizablePAC
open scoped NNReal ENNReal

noncomputable def eighth : Set.Ioo (0 : ℝ≥0) 1 := ⟨1 / 8, by norm_num, by norm_num⟩

noncomputable def fifteenth : Set.Ioo (0 : ℝ≥0) 1 := ⟨1 / 15, by norm_num, by norm_num⟩

theorem eighth_le : ((eighth : ℝ≥0) : ℝ) ≤ 1 / 8 := by
  norm_num [eighth]

theorem fifteenth_lt : ((fifteenth : ℝ≥0) : ℝ) < 1 / 14 := by
  norm_num [fifteenth]

/-! ### Thresholds are learnable -/

/-- Thresholds on `ℕ` are PAC learnable in the realizable setting, through the characterization. -/
example : IsPACLearnable thresholds (realizableDistributions thresholds) :=
  isPACLearnable_realizableDistributions_iff_hasFiniteVCDim.2 hasFiniteVCDim_thresholds

/-- The same for randomized learners. -/
example : IsRPACLearnable thresholds (realizableDistributions thresholds) :=
  isRPACLearnable_realizableDistributions_iff_hasFiniteVCDim.2 hasFiniteVCDim_thresholds

/-! ### All Boolean functions are not learnable -/

/-- On an infinite domain the class of all Boolean functions has infinite VC dimension. -/
theorem not_hasFiniteVCDim_univ {α : Type*} [Infinite α] :
    ¬ HasFiniteVCDim (Set.univ : ConceptClass α Bool) := by
  rintro h
  obtain ⟨N, hN⟩ := hasFiniteVCDim_iff.1 h
  obtain ⟨W, hW⟩ := Infinite.exists_subset_card_eq α (N + 1)
  have := hN W (setShatters_univ _)
  omega

/-- All Boolean functions on `ℕ` are not PAC learnable in the realizable setting. -/
example : ¬ IsPACLearnable (Set.univ : ConceptClass ℕ Bool) (realizableDistributions Set.univ) :=
  fun h => not_hasFiniteVCDim_univ (isPACLearnable_realizableDistributions_iff_hasFiniteVCDim.1 h)

/-- All Boolean functions on `ℕ` are not agnostically PAC learnable. -/
example : ¬ IsPACLearnable (Set.univ : ConceptClass ℕ Bool) Set.univ :=
  fun h => not_hasFiniteVCDim_univ h.hasFiniteVCDim_of_univ

/-- All Boolean functions on `ℕ` are not randomized PAC learnable in the realizable setting. -/
example : ¬ IsRPACLearnable (Set.univ : ConceptClass ℕ Bool) (realizableDistributions Set.univ) :=
  fun h => not_hasFiniteVCDim_univ (h.hasFiniteVCDim subset_rfl)

/-- The lower bound needs neither a countable domain nor measurable concepts: all Boolean functions
on `ℝ`, most of which are not Borel measurable, are not PAC learnable in the realizable setting. -/
example : ¬ IsPACLearnable (Set.univ : ConceptClass ℝ Bool) (realizableDistributions Set.univ) :=
  fun h => not_hasFiniteVCDim_univ (h.hasFiniteVCDim subset_rfl)

/-! ### Explicit sample sizes -/

/-- Ten examples do not suffice to learn all Boolean functions on `ℕ` to accuracy `1/8` with
confidence `14/15`: the class shatters `{0, …, 41}`, and `42 > 32 · (1/8) · 10 + 1`. -/
example : ¬ IsPACLearnerFor 10 eighth fifteenth (Set.univ : ConceptClass ℕ Bool)
    (realizableDistributions Set.univ) := by
  intro h
  have := card_le_of_isPACLearnerFor (W := Finset.range 42) (setShatters_univ _) eighth_le
    fifteenth_lt subset_rfl h
  norm_num [eighth] at this

/-- Nonvacuity: zero examples do not learn all Boolean functions on `Fin 3` to accuracy `1/8` with
confidence `14/15`, even agnostically. -/
example : ¬ IsPACLearnerFor 0 eighth fifteenth (Set.univ : ConceptClass (Fin 3) Bool) Set.univ := by
  intro h
  have := card_le_of_isPACLearnerFor (W := Finset.univ) (setShatters_univ _) eighth_le
    fifteenth_lt (Set.subset_univ _) h
  norm_num at this

/-- Restricting the class of all Boolean functions to a subdomain shatters the whole subdomain. -/
example (s : Set ℕ) : SetShatters (restrictDomain (Set.univ : ConceptClass ℕ Bool) s) Set.univ :=
  (setShatters_univ s).restrictDomain

end CslibFrontierTests.FundamentalTheoremPAC
