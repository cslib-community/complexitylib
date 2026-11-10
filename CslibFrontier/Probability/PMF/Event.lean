/-
Copyright (c) 2026 Samuel Schlesinger, Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josha Dekker, Devon Tuma, Kexing Ying, Samuel Schlesinger, Renfei Zhou
-/

module
-- upstream: candidate (addition to `Cslib/Probability/PMF.lean`)

public import CslibFrontier.Probability.PMF

/-!
# Event probabilities of discrete distributions

The probability `p.toOuterMeasure s` of an event under a discrete distribution is finite and at
most one (`toOuterMeasure_ne_top`, `toOuterMeasure_le_one`); on a finite type its real value is the
sum of the masses of the event's members (`toOuterMeasure_apply_toReal`), and an event and its
complement have total probability one (`toOuterMeasure_add_compl_ennreal`,
`toOuterMeasure_toReal_add_compl`). Conditioning keeps the event's masses and divides them by its
probability (`filter_apply_toReal`).

Event probabilities after a random first stage are in `CslibFrontier.Probability.PMF.EventBind`, and
the outcome masses of Boolean distributions and Boolean predicates are in
`CslibFrontier.Probability.PMF.Bool`.

## Main results

* `Cslib.Probability.PMF.toOuterMeasure_ne_top`, `Cslib.Probability.PMF.toOuterMeasure_le_one`:
  events have probability at most one.
* `Cslib.Probability.PMF.toOuterMeasure_eq_tsum_mul_indicator`: an event's probability is the
  expectation of its indicator.
* `Cslib.Probability.PMF.toOuterMeasure_abs_sub_ge_le`,
  `Cslib.Probability.PMF.toOuterMeasure_abs_sub_ge_toReal_le`: two-sided tail bounds from upper
  and lower tails.
* `Cslib.Probability.PMF.toOuterMeasure_apply_toReal`,
  `Cslib.Probability.PMF.toOuterMeasure_toReal_add_compl`,
  `Cslib.Probability.PMF.toOuterMeasure_toReal_pos_iff`: real-valued event probabilities.
* `Cslib.Probability.PMF.toOuterMeasure_add_compl_ennreal`,
  `Cslib.Probability.PMF.toOuterMeasure_compl_le_one_sub`: complementation and failure bounds.
* `Cslib.Probability.PMF.filter_apply_toReal`: conditioned masses.

## References

Adapted in part from Probability/PMF.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`. The `ENNReal` complement lemmas were extracted from
Renfei Zhou's Karger algorithm development.
-/

@[expose] public section

namespace Cslib.Probability.PMF

open scoped ENNReal

variable {α β : Type*}

/-- Every event has finite probability, including on an infinite ambient type.
Adapted from the cslib `crypto` branch at `5ff69ca`. -/
theorem toOuterMeasure_ne_top (p : PMF α) (event : Set α) : p.toOuterMeasure event ≠ ⊤ := by
  simpa only [PMF.toOuterMeasure_apply] using p.tsum_coe_indicator_ne_top event

/-- An event has probability at most one. -/
theorem toOuterMeasure_le_one (p : PMF α) (event : Set α) : p.toOuterMeasure event ≤ 1 := by
  rw [PMF.toOuterMeasure_apply, ← p.tsum_coe]
  exact tsum_le_tsum (fun a => Set.indicator_apply_le (fun _ => le_rfl))

/-- The probability of an event is the expectation of its indicator. -/
theorem toOuterMeasure_eq_tsum_mul_indicator (p : PMF α) (event : Set α) :
    p.toOuterMeasure event = ∑' a, p a * event.indicator 1 a := by
  classical
  rw [PMF.toOuterMeasure_apply]
  exact tsum_congr fun a => by by_cases ha : a ∈ event <;> simp [ha]

/-- The event that `f a` deviates from `m` by at least `ε` is covered by the upper tail
`m + ε ≤ f a` and the lower tail `f a ≤ m - ε`. -/
theorem toOuterMeasure_abs_sub_ge_le (p : PMF α) (f : α → ℝ) (m ε : ℝ) :
    p.toOuterMeasure {a | ε ≤ |f a - m|} ≤
      p.toOuterMeasure {a | m + ε ≤ f a} + p.toOuterMeasure {a | f a ≤ m - ε} := by
  refine (MeasureTheory.measure_mono (μ := p.toOuterMeasure) fun a ha => ?_).trans
    (MeasureTheory.measure_union_le _ _)
  rcases le_abs.mp (show ε ≤ |f a - m| from ha) with h | h
  · exact Or.inl (add_comm m ε ▸ le_sub_iff_add_le.mp h)
  · exact Or.inr (le_sub_comm.mp (neg_sub (f a) m ▸ h))

/-- In real-valued probabilities, the two-sided tail `ε ≤ |f a - m|` is bounded by the sum of
the upper tail `m + ε ≤ f a` and the lower tail `f a ≤ m - ε`. -/
theorem toOuterMeasure_abs_sub_ge_toReal_le (p : PMF α) (f : α → ℝ) (m ε : ℝ) :
    (p.toOuterMeasure {a | ε ≤ |f a - m|}).toReal ≤
      (p.toOuterMeasure {a | m + ε ≤ f a}).toReal +
        (p.toOuterMeasure {a | f a ≤ m - ε}).toReal :=
  ENNReal.toReal_le_add (toOuterMeasure_abs_sub_ge_le p f m ε)
    (toOuterMeasure_ne_top _ _) (toOuterMeasure_ne_top _ _)

open Classical in
/-- Event probabilities on finite spaces are sums of the masses of their members. -/
theorem toOuterMeasure_apply_toReal [Fintype α] (p : PMF α) (event : Set α) :
    (p.toOuterMeasure event).toReal = ∑ a, if a ∈ event then (p a).toReal else 0 := by
  classical
  rw [PMF.toOuterMeasure_apply_fintype, ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro a _
    by_cases ha : a ∈ event <;> simp [ha]
  · intro a _
    by_cases ha : a ∈ event <;> simp [ha, PMF.apply_ne_top]

/-- Exact complementation law `p.toOuterMeasure s + p.toOuterMeasure sᶜ = 1` for discrete `PMF`s,
valid on arbitrary types without measurability hypotheses. -/
theorem toOuterMeasure_add_compl_ennreal {α : Type*} (p : PMF α) (s : Set α) :
    p.toOuterMeasure s + p.toOuterMeasure sᶜ = 1 := by
  classical
  rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply, ← tsum_add]
  have hpt : (fun x => s.indicator p x + sᶜ.indicator p x) = p := by
    ext x
    by_cases hx : x ∈ s <;> simp [hx]
  rw [hpt, p.tsum_coe]

/-- A lower bound on success gives the complementary upper bound on failure. -/
theorem toOuterMeasure_compl_le_one_sub {α : Type*} (p : PMF α) (s : Set α) {q : ℝ≥0∞}
    (hq : q ≤ p.toOuterMeasure s) :
    p.toOuterMeasure sᶜ ≤ 1 - q := by
  have hsum := toOuterMeasure_add_compl_ennreal p s
  have hq_top : q ≠ ⊤ :=
    ne_top_of_le_ne_top (Cslib.Probability.PMF.toOuterMeasure_ne_top p s) hq
  refine ENNReal.le_sub_of_add_le_right hq_top ?_
  calc
    p.toOuterMeasure sᶜ + q ≤ p.toOuterMeasure sᶜ + p.toOuterMeasure s := by gcongr
    _ = 1 := by rw [add_comm, hsum]

/-- An event and its complement have total probability one, in real-valued probability units. -/
theorem toOuterMeasure_toReal_add_compl (p : PMF α) (event : Set α) :
    (p.toOuterMeasure event).toReal + (p.toOuterMeasure eventᶜ).toReal = 1 := by
  simpa only [ENNReal.toReal_add (toOuterMeasure_ne_top p _) (toOuterMeasure_ne_top p _),
    ENNReal.toReal_one] using congrArg ENNReal.toReal (toOuterMeasure_add_compl_ennreal p event)

/-- An event has positive real probability exactly when it contains a possible outcome. -/
theorem toOuterMeasure_toReal_pos_iff (p : PMF α) (event : Set α) :
    0 < (p.toOuterMeasure event).toReal ↔ ∃ a ∈ event, a ∈ p.support := by
  classical
  simp [ENNReal.toReal_pos_iff, lt_top_iff_ne_top, toOuterMeasure_ne_top, pos_iff_ne_zero,
    PMF.toOuterMeasure_apply_eq_zero_iff, Set.disjoint_left, and_comm]

open Classical in
/-- Conditioning keeps the event's masses and divides them by its probability. -/
theorem filter_apply_toReal (p : PMF α) (event : Set α)
    (hevent : ∃ a ∈ event, a ∈ p.support) (a : α) :
    ((p.filter event hevent) a).toReal =
      if a ∈ event then (p a).toReal / (p.toOuterMeasure event).toReal else 0 := by
  rw [PMF.filter_apply, ← PMF.toOuterMeasure_apply]
  by_cases ha : a ∈ event <;> simp [ha, ENNReal.toReal_mul, div_eq_mul_inv]

end Cslib.Probability.PMF
