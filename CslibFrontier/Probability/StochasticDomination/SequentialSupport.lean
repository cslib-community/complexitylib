/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticDomination.Adapted
import CslibFrontier.Probability.PMF.Map
import Mathlib.Tactic

/-!
# Sequential count bounds on supported prefixes

The event probabilities in a history-dependent process need only be controlled
at histories the process can actually reach. These original support-restricted
corollaries reuse the sequential Poisson-binomial comparison from `Adapted`.
They allow arbitrary response types, without a finite alphabet or a hypothesis
on zero-probability histories. This is useful for stochastic-oracle policies
whose raw responses and invoice metadata have unbounded discrete support.

The proof completes the comparison event to the whole response space at null
prefixes. Its count agrees with the original count on every supported execution;
the actual transition distributions are unchanged.

## Main results

* `seqCount_congr_on_support`: supported-prefix event equality preserves actual counts.
* `seqCount_stochasticallyDominates_poissonBinomial_of_support`: reached-prefix domination.
* `seqCount_active_toReal_Iio_le_of_support`: active-before-target binomial bound.
-/

public section
noncomputable section
namespace Cslib.Probability.PMF
open scoped ENNReal unitInterval
variable {α : Type*}

/-- Events agreeing at each supported prefix have the same count along every
supported execution. No restriction is imposed at null histories. -/
theorem seqCount_congr_on_support
    (step : ∀ t : ℕ, (Fin t → α) → PMF α)
    (E F : ∀ t : ℕ, (Fin t → α) → Set α)
    (H : ∀ t h, h ∈ (seqProcess step t).support → E t h = F t h)
    (n : ℕ) (h : Fin n → α) (hh : h ∈ (seqProcess step n).support) :
    seqCount E n h = seqCount F n h := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [seqProcess, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hh
    obtain ⟨g, hg, a, _, rfl⟩ := hh
    rw [seqCount_snoc, seqCount_snoc, ih g hg, H n g hg]

private def completedEvent (step : ∀ t : ℕ, (Fin t → α) → PMF α)
    (E : ∀ t : ℕ, (Fin t → α) → Set α) (t : ℕ) (h : Fin t → α) : Set α :=
  by
    classical
    exact if h ∈ (seqProcess step t).support then E t h else Set.univ

private theorem completedEvent_count (step : ∀ t : ℕ, (Fin t → α) → PMF α)
    (E : ∀ t : ℕ, (Fin t → α) → Set α) (n : ℕ)
    (h : Fin n → α) (hh : h ∈ (seqProcess step n).support) :
    seqCount E n h = seqCount (completedEvent step E) n h :=
  seqCount_congr_on_support step E (completedEvent step E)
    (fun _ _ hs => by simp [completedEvent, hs]) n h hh

private theorem completedEvent_map (step : ∀ t : ℕ, (Fin t → α) → PMF α)
    (E : ∀ t : ℕ, (Fin t → α) → Set α) (n : ℕ) :
    (seqProcess step n).map (seqCount E n) =
      (seqProcess step n).map (seqCount (completedEvent step E) n) :=
  map_congr_on_support _ _ _ (fun h hh => completedEvent_count step E n h hh)

/-- Sequential Poisson-binomial domination only needs the conditional lower
probability envelope at prefixes in the actual process support. -/
theorem seqCount_stochasticallyDominates_poissonBinomial_of_support
    (step : ∀ t : ℕ, (Fin t → α) → PMF α)
    (E : ∀ t : ℕ, (Fin t → α) → Set α) (ps : List I)
    (hp : ∀ t (ht : t < ps.length) (h : Fin t → α),
      h ∈ (seqProcess step t).support →
      (ps[t] : ℝ) ≤ ((step t h).toOuterMeasure (E t h)).toReal) :
    StochasticallyDominates ((seqProcess step ps.length).map (seqCount E ps.length))
      (poissonBinomial ps) := by
  rw [completedEvent_map step E ps.length]
  apply seqCount_stochasticallyDominates_poissonBinomial
  intro t ht h
  by_cases hh : h ∈ (seqProcess step t).support
  · simpa only [completedEvent, ite_eq_left hh] using hp t ht h hh
  · have huniv : (step t h).toOuterMeasure Set.univ = 1 :=
      (PMF.toOuterMeasure_apply_eq_one_iff _ _).2 (Set.subset_univ _)
    simpa only [completedEvent, ite_eq_right hh, huniv, ENNReal.toReal_one] using (ps[t]).2.2

/-- Before-target binomial tail bound from a lower event-probability envelope
only at supported prefixes whose original success count is below the target. -/
theorem seqCount_active_toReal_Iio_le_of_support
    (step : ∀ t : ℕ, (Fin t → α) → PMF α)
    (E : ∀ t : ℕ, (Fin t → α) → Set α) (n r : ℕ) (p : I)
    (hp : ∀ t, t < n → ∀ h : Fin t → α,
      h ∈ (seqProcess step t).support → seqCount E t h < r →
        (p : ℝ) ≤ ((step t h).toOuterMeasure (E t h)).toReal) :
    (((seqProcess step n).map (seqCount E n)).toOuterMeasure (Set.Iio r)).toReal ≤
      (ProbabilityTheory.binomial n p).real (Set.Iio r) := by
  rw [completedEvent_map step E n]
  apply seqCount_active_toReal_Iio_le
  intro t ht h hc
  by_cases hh : h ∈ (seqProcess step t).support
  · have hc' : seqCount E t h < r := by
      rw [completedEvent_count step E t h hh]
      exact hc
    simpa only [completedEvent, ite_eq_left hh] using hp t ht h hh hc'
  · have huniv : (step t h).toOuterMeasure Set.univ = 1 :=
      (PMF.toOuterMeasure_apply_eq_one_iff _ _).2 (Set.subset_univ _)
    simpa only [completedEvent, ite_eq_right hh, huniv, ENNReal.toReal_one] using p.2.2

end Cslib.Probability.PMF
