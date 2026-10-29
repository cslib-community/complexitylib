/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Probability.ProductConditioning

/-! # Conditioning a product distribution

Conditioning on a certain event leaves every marginal unchanged, and conditioning two fair bits on
the first being `true` satisfies the bound of Raz's conditioning lemma.
-/

namespace ComplexityTests.ProductConditioning

open Cslib.Probability.PMF
open scoped Cslib.Probability.PMF

-- Conditioning on a certain event leaves every marginal where it was.
example {ι : Type} [Fintype ι] {β : ι → Type} [∀ i, Fintype (β i)] (p : ∀ i, PMF (β i))
    (h : ∃ u ∈ (Set.univ : Set (∀ i, β i)), u ∈ (pi p).support) :
    ∑ j, dist (((pi p).filter Set.univ h).map fun u => u j) (p j) = 0 := by
  refine le_antisymm ?_ (Finset.sum_nonneg fun _ _ => dist_nonneg)
  have h1 : ((pi p).toOuterMeasure Set.univ).toReal = 1 := by
    rw [(PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr (Set.subset_univ _), ENNReal.toReal_one]
  simpa [h1] using sum_dist_map_filter_pi_le p Set.univ h

/-- Two fair bits. -/
noncomputable def bits : Fin 2 → PMF Bool := fun _ => uniformOfFintype Bool

theorem first_true_mem : ∃ u ∈ {u : Fin 2 → Bool | u 0 = true}, u ∈ (pi bits).support :=
  ⟨fun _ => true, rfl, by
    rw [mem_support_pi_iff]
    intro i
    simp [bits]⟩

-- Conditioning two fair bits on the first being `true`, in both Raz's and Holenstein's forms.
example :
    (∑ j, dist (((pi bits).filter {u | u 0 = true} first_true_mem).map fun u => u j)
        (bits j)) ^ 2 ≤
      2 * Real.log (1 / ((pi bits).toOuterMeasure {u | u 0 = true}).toReal) / 2 ∧
    ((pi bits).toOuterMeasure {u | u 0 = true}).toReal ≤ (2 : ℝ) ^
      (-∑ j, dist (((pi bits).filter {u | u 0 = true} first_true_mem).map fun u => u j)
        (bits j) ^ 2) :=
  ⟨by simpa using sq_sum_dist_map_filter_pi_le bits {u | u 0 = true} first_true_mem,
    toOuterMeasure_toReal_le_two_rpow bits _ first_true_mem⟩

end ComplexityTests.ProductConditioning
