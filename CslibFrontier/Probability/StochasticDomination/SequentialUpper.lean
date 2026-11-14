/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticDomination.SequentialSupport
import CslibFrontier.Probability.PoissonBinomial.Reflection
import CslibFrontier.Probability.PMF.Event
import Mathlib.Tactic

/-!
# Upper bounds for sequential event counts

A conditional upper bound on event probability at supported histories gives
binomial upper stochastic domination of the actual count. Complementing events
reduces this to the existing lower comparison; binomial reflection converts the
complemented count back. Response types may have arbitrary discrete support.

## Main results

* `seqCount_add_compl`: an event and its complement partition the trial budget.
* `poissonBinomial_replicate_stochasticallyDominates_seqCount_of_support`:
  binomial domination from supported-prefix conditional upper bounds.
* `seqCount_toReal_Ici_le_of_support`: real-valued binomial upper tails.
-/

public section
noncomputable section
namespace Cslib.Probability.PMF
open scoped ENNReal unitInterval
variable {α : Type*}

/-- Every trial belongs either to the history-dependent event or its complement. -/
theorem seqCount_add_compl (E : ∀ t : ℕ, (Fin t → α) → Set α)
    (n : ℕ) (h : Fin n → α) :
    seqCount E n h + seqCount (fun t h => (E t h)ᶜ) n h = n := by
  classical
  rw [seqCount, seqCount, ← Finset.sum_add_distrib]
  calc
    _ = ∑ _ : Fin n, 1 := by
      apply Finset.sum_congr rfl
      intro t _
      simp only [Set.mem_compl_iff]
      split_ifs <;> omega
    _ = n := by simp

/-- A sequential event count cannot exceed its trial budget. -/
theorem seqCount_le (E : ∀ t : ℕ, (Fin t → α) → Set α)
    (n : ℕ) (h : Fin n → α) : seqCount E n h ≤ n := by
  have := seqCount_add_compl E n h
  omega

/-- A homogeneous conditional upper envelope is required only at histories
in the actual support. The resulting binomial law dominates the event count. -/
theorem poissonBinomial_replicate_stochasticallyDominates_seqCount_of_support
    (step : ∀ t : ℕ, (Fin t → α) → PMF α)
    (E : ∀ t : ℕ, (Fin t → α) → Set α) (n : ℕ) (p : I)
    (hp : ∀ t, t < n → ∀ h : Fin t → α,
      h ∈ (seqProcess step t).support →
        ((step t h).toOuterMeasure (E t h)).toReal ≤ (p : ℝ)) :
    StochasticallyDominates (poissonBinomial (List.replicate n p))
      ((seqProcess step n).map (seqCount E n)) := by
  have hc := seqCount_stochasticallyDominates_poissonBinomial_of_support step
    (fun t h => (E t h)ᶜ) (List.replicate n (σ p)) (by
      intro t ht h hh
      simp only [List.length_replicate] at ht
      simp only [List.getElem_replicate, unitInterval.coe_symm_eq]
      have := toOuterMeasure_toReal_add_compl (step t h) (E t h)
      have := hp t ht h hh
      linarith)
  rw [List.length_replicate] at hc
  rw [stochasticallyDominates_nat_iff_Ici]
  intro r
  by_cases hr : r ≤ n
  · have hb := hc.le_Iic (n - r)
    rw [← poissonBinomial_replicate_map_sub n p] at hb
    simp only [PMF.toOuterMeasure_map_apply] at hb ⊢
    have he : (seqCount (fun t h => (E t h)ᶜ) n) ⁻¹' Set.Iic (n - r) =
        (seqCount E n) ⁻¹' Set.Ici r := by
      ext h
      simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_Ici]
      have := seqCount_add_compl E n h
      omega
    have hk : (fun k => n - k) ⁻¹' Set.Iic (n - r) = Set.Ici r := by
      ext k
      simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_Ici]
      omega
    rwa [he, hk] at hb
  · have he : (seqCount E n) ⁻¹' Set.Ici r = ∅ := by
      ext h
      simp only [Set.mem_preimage, Set.mem_Ici, Set.mem_empty_iff_false, iff_false]
      have := seqCount_le E n h
      omega
    rw [PMF.toOuterMeasure_map_apply, he, MeasureTheory.measure_empty]
    exact zero_le

/-- Upper binomial tail for the actual sequential count, with a conditional
upper probability envelope only at supported prefixes. -/
theorem seqCount_toReal_Ici_le_of_support
    (step : ∀ t : ℕ, (Fin t → α) → PMF α)
    (E : ∀ t : ℕ, (Fin t → α) → Set α) (n r : ℕ) (p : I)
    (hp : ∀ t, t < n → ∀ h : Fin t → α,
      h ∈ (seqProcess step t).support →
        ((step t h).toOuterMeasure (E t h)).toReal ≤ (p : ℝ)) :
    (((seqProcess step n).map (seqCount E n)).toOuterMeasure (Set.Ici r)).toReal ≤
      (ProbabilityTheory.binomial n p).real (Set.Ici r) := by
  have hb := (poissonBinomial_replicate_stochasticallyDominates_seqCount_of_support
    step E n p hp).Ici_le r
  have hr := ENNReal.toReal_mono (toOuterMeasure_ne_top _ _) hb
  rw [← toMeasure_poissonBinomial_replicate n p, MeasureTheory.measureReal_def,
    PMF.toMeasure_apply_eq_toOuterMeasure_apply _ measurableSet_Ici]
  exact hr

end Cslib.Probability.PMF
