/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (addition to `Cslib/Probability/PMF.lean`)

public import CslibFrontier.Probability.PMF

/-!
# Boolean distributions and Boolean predicates

The masses of `true` and `false` under a Boolean distribution sum to one
(`apply_true_add_apply_false`, and `toReal_true_add_toReal_false` in real-valued units). Pushing
a distribution forward along Boolean predicates (`PMF.map`), the `true`-mass is monotone under
pointwise implication on the support (`map_true_mono`), satisfies union bounds
(`map_true_le_add`, `map_any_range_true_le_sum`), and is complemented by negation
(`map_not_true`).

## Main results

* `Cslib.Probability.PMF.apply_true_add_apply_false`,
  `Cslib.Probability.PMF.toReal_true_add_toReal_false`,
  `Cslib.Probability.PMF.toReal_false_eq_one_sub`,
  `Cslib.Probability.PMF.toReal_true_eq_one_sub`: Boolean outcome masses.
* `Cslib.Probability.PMF.map_true_mono`, `Cslib.Probability.PMF.map_true_le_add`,
  `Cslib.Probability.PMF.map_any_range_true_le_sum`, `Cslib.Probability.PMF.map_not_true`:
  monotonicity, union bounds, and complementation for Boolean predicates pushed forward along
  `PMF.map`.
-/

@[expose] public section

namespace Cslib.Probability.PMF

open scoped ENNReal

variable {α : Type*}

/-- The probabilities of `true` and `false` under a Boolean distribution sum to one. -/
theorem apply_true_add_apply_false (p : PMF Bool) : p true + p false = 1 := by
  rw [add_comm, ← tsum_bool, p.tsum_coe]

/-- The real-valued probabilities of `true` and `false` under a Boolean distribution sum to one. -/
theorem toReal_true_add_toReal_false (p : PMF Bool) :
    (p true).toReal + (p false).toReal = 1 := by
  simpa only [Fintype.sum_bool] using sum_toReal p

/-- The real-valued probability of `false` under a Boolean distribution is one minus the
probability of `true`. -/
theorem toReal_false_eq_one_sub (p : PMF Bool) :
    (p false).toReal = 1 - (p true).toReal :=
  eq_sub_of_add_eq' (toReal_true_add_toReal_false p)

/-- The real-valued probability of `true` under a Boolean distribution is one minus the
probability of `false`. -/
theorem toReal_true_eq_one_sub (p : PMF Bool) :
    (p true).toReal = 1 - (p false).toReal :=
  eq_sub_of_add_eq (toReal_true_add_toReal_false p)

/-- Pointwise implication on the support makes the mapped `true`-mass monotone. -/
theorem map_true_mono (p : PMF α) {E F : α → Bool}
    (h : ∀ a ∈ p.support, E a = true → F a = true) :
    (p.map E) true ≤ (p.map F) true := by
  rw [PMF.map_apply, PMF.map_apply]
  refine tsum_le_tsum fun a => ?_
  by_cases ha : a ∈ p.support
  · by_cases hE : true = E a
    · simp [← hE, h a ha hE.symm]
    · simp [hE]
  · simp [(PMF.apply_eq_zero_iff p a).mpr ha]

/-- Union bound for two Boolean predicates pushed forward along `p.map`. -/
theorem map_true_le_add (p : PMF α) {E A B : α → Bool}
    (h : ∀ a ∈ p.support, E a = true → A a = true ∨ B a = true) :
    (p.map E) true ≤ (p.map A) true + (p.map B) true := by
  rw [PMF.map_apply, PMF.map_apply, PMF.map_apply, ← tsum_add]
  refine tsum_le_tsum fun a => ?_
  by_cases ha : a ∈ p.support
  · by_cases hE : true = E a
    · rcases h a ha hE.symm with hA | hB
      · simp [← hE, hA]
      · simp [← hE, hB]
    · simp [hE]
  · simp [(PMF.apply_eq_zero_iff p a).mpr ha]

/-- Union bound for `List.any` over `List.range K` pushed forward along `p.map`. -/
theorem map_any_range_true_le_sum (p : PMF α) (K : ℕ) (F : ℕ → α → Bool) :
    (p.map (fun a => (List.range K).any (fun j => F j a))) true ≤
      ∑ j ∈ Finset.range K, (p.map (F j)) true := by
  induction K with
  | zero =>
    simp [PMF.map_apply]
  | succ K ih =>
    have hsplit : ∀ a ∈ p.support, ((List.range (K + 1)).any (fun j => F j a)) = true →
        ((List.range K).any (fun j => F j a)) = true ∨ F K a = true := by
      intro a _ ha
      rw [List.range_succ, List.any_append, Bool.or_eq_true] at ha
      simpa using ha
    rw [Finset.sum_range_succ]
    exact (map_true_le_add p hsplit).trans (add_le_add_left ih _)

/-- Negating a Boolean predicate complements its `true`-mass in `ℝ≥0∞`. -/
theorem map_not_true (p : PMF α) (E : α → Bool) :
    (p.map (fun a => !E a)) true = 1 - (p.map E) true := by
  have hsum : (p.map (fun a => !E a)) true + (p.map E) true = 1 := by
    have h := (p.map E).tsum_coe
    rw [tsum_bool] at h
    have hnot : (p.map (fun a => !E a)) true = (p.map E) false := by
      rw [PMF.map_apply, PMF.map_apply]
      congr 1
      funext a
      cases E a <;> simp
    rwa [hnot]
  exact ENNReal.eq_sub_of_add_eq
    (((PMF.coe_le_one _ _).trans_lt ENNReal.one_lt_top).ne) hsum

end Cslib.Probability.PMF
