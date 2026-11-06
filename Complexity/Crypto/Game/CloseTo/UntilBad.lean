/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Game.CloseTo
import Complexity.Probability.PMF.Bind

/-!
# Mixtures that agree outside a bad event

Two randomized continuations that agree on supported inputs outside a bad event induce close
mixtures, with error equal to the actual probability of that event. Neither type must be finite.
The proof uses the existing Boolean-game mixture inequality and all-event variational bridge.

## Main results

* `CloseTo.bind_of_eq_on`: charge only the probability of inputs where the kernels may differ.

This original application supports cache programming: a memoized query and fresh programming
agree when the query point is absent from the current cache.
-/

public section

namespace Cslib.Interactive

open Crypto Probability
open scoped ENNReal

/-- Mixtures of kernels that agree on supported inputs outside `bad` are close within the
probability of `bad`. The conclusion controls all output events, including on infinite types. -/
theorem CloseTo.bind_of_eq_on {α β : Type} (μ : PMF α) (f g : α → PMF β) (bad : Set α)
    (h : ∀ a ∈ μ.support, a ∉ bad → f a = g a) :
    CloseTo (μ.bind f) (μ.bind g) (μ.toOuterMeasure bad) := by
  classical
  let g' : α → PMF β := fun a => if a ∈ μ.support then g a else f a
  have hg : μ.bind g' = μ.bind g := Probability.PMF.bind_congr_on_support μ _ _
    (fun a ha => by simp only [g', ha, ↓reduceIte])
  rw [← hg]
  apply Game.closeTo_of_coe_advantage_decide_le
  intro event
  let test : β → Bool := fun b => decide (b ∈ event)
  let err : α → Game := fun a => PMF.pure (decide (a ∈ bad))
  have he (a : α) :
      ((f a).map test) true ≤ ((g' a).map test) true + err a true ∧
      ((g' a).map test) true ≤ ((f a).map test) true + err a true := by
    by_cases ha : a ∈ bad
    · simp only [err, ha, decide_true, PMF.pure_apply_self]
      exact ⟨(PMF.coe_le_one _ _).trans le_add_self,
        (PMF.coe_le_one _ _).trans le_add_self⟩
    · have heq : f a = g' a := by
        by_cases hs : a ∈ μ.support
        · simpa only [g', hs, ↓reduceIte] using h a hs ha
        · simp only [g', hs, ↓reduceIte]
      simp [heq, err, ha]
  have hadv := Game.advantage_bind_le_succProbability_bind μ
    (fun a => (f a).map test) (fun a => (g' a).map test) err he
  have herr : (μ.bind err) true = μ.toOuterMeasure bad := by
    change (μ.map (fun a => decide (a ∈ bad))) true = _
    rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
    congr 1
    ext a
    simp
  have hc := ENNReal.coe_le_coe.mpr hadv
  rw [Game.succProbability, ENNReal.coe_toNNReal (PMF.apply_ne_top _ _), herr] at hc
  simpa only [PMF.map_bind] using hc

end Cslib.Interactive
