/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josha Dekker, Devon Tuma, Kexing Ying, Samuel Schlesinger
-/

module
-- upstream: candidate (addition to `Cslib/Probability/PMF.lean`)

public import Complexity.Probability.PMF

/-!
# Event probabilities of discrete distributions

The probability `p.toOuterMeasure s` of an event under a discrete distribution is finite and at
most one (`toOuterMeasure_ne_top`, `toOuterMeasure_le_one`); on a finite type its real value is the
sum of the masses of the event's members (`toOuterMeasure_apply_toReal`), and an event and its
complement have total probability one (`toOuterMeasure_toReal_add_compl`). Conditioning keeps the
event's masses and divides them by its probability (`filter_apply_toReal`).

After a random first stage, an event's probability is the average of its conditional
probabilities (`toOuterMeasure_bind_toReal`). Failure and success bounds compose without
independence: a randomized continuation fails because its precondition already failed or because
it fails from a valid input (`toOuterMeasure_bind_failure_le`), lower bounds on a first stage and
on its continuation from supported members multiply (`toOuterMeasure_bind_ge_mul`), and average
bias turns into the probability of good first stages (`toOuterMeasure_rate_ge`). The real-valued
masses of `true` and `false` under a Boolean distribution sum to one
(`toReal_true_add_toReal_false`).

## Main results

* `Cslib.Probability.PMF.toOuterMeasure_ne_top`, `Cslib.Probability.PMF.toOuterMeasure_le_one`:
  events have probability at most one.
* `Cslib.Probability.PMF.toOuterMeasure_abs_sub_ge_le`,
  `Cslib.Probability.PMF.toOuterMeasure_abs_sub_ge_toReal_le`: two-sided tail bounds from upper
  and lower tails.
* `Cslib.Probability.PMF.toOuterMeasure_apply_toReal`,
  `Cslib.Probability.PMF.toOuterMeasure_toReal_add_compl`,
  `Cslib.Probability.PMF.toOuterMeasure_toReal_pos_iff`: real-valued event probabilities.
* `Cslib.Probability.PMF.filter_apply_toReal`: conditioned masses.
* `Cslib.Probability.PMF.toOuterMeasure_bind_toReal`: averaging over a first stage.
* `Cslib.Probability.PMF.toOuterMeasure_bind_failure_le`,
  `Cslib.Probability.PMF.toOuterMeasure_bind_failure_toReal_le`,
  `Cslib.Probability.PMF.toOuterMeasure_bind_ge_mul`: composing failure and success bounds.
* `Cslib.Probability.PMF.toOuterMeasure_rate_ge`: average bias as the probability of good inputs.
* `Cslib.Probability.PMF.toReal_true_add_toReal_false`,
  `Cslib.Probability.PMF.toReal_false_eq_one_sub`,
  `Cslib.Probability.PMF.toReal_true_eq_one_sub`: Boolean outcome masses.
* `Cslib.Probability.PMF.map_true_mono`, `Cslib.Probability.PMF.map_true_le_add`,
  `Cslib.Probability.PMF.map_any_range_true_le_sum`, `Cslib.Probability.PMF.map_not_true`:
  monotonicity, union bounds, and complementation for Boolean predicates pushed forward along
  `PMF.map`.

## References

Adapted in part from Probability/PMF.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`.
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

/-- An event and its complement have total probability one, in real-valued probability units. -/
theorem toOuterMeasure_toReal_add_compl (p : PMF α) (event : Set α) :
    (p.toOuterMeasure event).toReal + (p.toOuterMeasure eventᶜ).toReal = 1 := by
  have h : p.toOuterMeasure event + p.toOuterMeasure eventᶜ = 1 := by
    rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply, ← tsum_add]
    convert p.tsum_coe using 1
    congr 1
    funext a
    by_cases ha : a ∈ event <;> simp [ha]
  simpa only [ENNReal.toReal_add (toOuterMeasure_ne_top p _) (toOuterMeasure_ne_top p _),
    ENNReal.toReal_one] using congrArg ENNReal.toReal h

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

/-- Event probability after a finite random choice is the average conditional probability. -/
theorem toOuterMeasure_bind_toReal [Fintype α] (p : PMF α) (kernel : α → PMF β)
    (event : Set β) :
    ((p.bind kernel).toOuterMeasure event).toReal =
      ∑ a, (p a).toReal * ((kernel a).toOuterMeasure event).toReal := by
  rw [PMF.toOuterMeasure_bind_apply, tsum_fintype, ENNReal.toReal_sum
    (fun a _ => ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (toOuterMeasure_ne_top _ _))]
  simp only [ENNReal.toReal_mul]

/-- A randomized continuation can fail because its precondition was already false or because
it fails from a valid input. No independence or finite-state assumption is needed. -/
theorem toOuterMeasure_bind_failure_le (p : PMF α) (kernel : α → PMF β)
    (pre : Set α) (failure : Set β) (error : ENNReal)
    (hstep : ∀ a ∈ p.support, a ∈ pre → (kernel a).toOuterMeasure failure ≤ error) :
    (p.bind kernel).toOuterMeasure failure ≤ p.toOuterMeasure preᶜ + error := by
  classical
  rw [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_apply]
  calc
    _ ≤ ∑' a, ((preᶜ).indicator p a + p a * error) := by
      apply tsum_le_tsum
      intro a
      by_cases ha : a ∈ pre
      · simp only [Set.indicator_of_notMem (show a ∉ preᶜ by simpa), zero_add]
        by_cases hs : a ∈ p.support
        · exact mul_le_mul_of_nonneg_left (hstep a hs ha) zero_le
        · have hz : p a = 0 := by simpa only [PMF.mem_support_iff, not_not] using hs
          simp [hz]
      · simp only [Set.indicator_of_mem (show a ∈ preᶜ from ha)]
        exact (mul_le_mul_of_nonneg_left (toOuterMeasure_le_one (kernel a) failure)
          zero_le).trans (by simp)
    _ = _ := by rw [tsum_add, ENNReal.tsum_mul_right, p.tsum_coe, one_mul]

/-- The real-valued error rule for a randomized continuation. -/
theorem toOuterMeasure_bind_failure_toReal_le (p : PMF α) (kernel : α → PMF β)
    (pre : Set α) (failure : Set β) {error : ℝ} (herror : 0 ≤ error)
    (hstep : ∀ a ∈ p.support, a ∈ pre →
      ((kernel a).toOuterMeasure failure).toReal ≤ error) :
    ((p.bind kernel).toOuterMeasure failure).toReal ≤
      (p.toOuterMeasure preᶜ).toReal + error := by
  have h := toOuterMeasure_bind_failure_le p kernel pre failure (ENNReal.ofReal error)
    (fun a ha hpre => (ENNReal.le_ofReal_iff_toReal_le (toOuterMeasure_ne_top _ _) herror).mpr
      (hstep a ha hpre))
  have hfinite : p.toOuterMeasure preᶜ + ENNReal.ofReal error ≠ ⊤ := ENNReal.add_ne_top.mpr
    ⟨toOuterMeasure_ne_top p preᶜ, ENNReal.ofReal_ne_top⟩
  simpa only [ENNReal.toReal_add (toOuterMeasure_ne_top p preᶜ) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal herror] using ENNReal.toReal_mono hfinite h

/-- If a first stage `p` lands in `pre` with probability at least `s₁` and for every supported
`a ∈ pre` the continuation `kernel a` lands in `event` with probability at least `s₂`, then
`p.bind kernel` lands in `event` with probability at least `s₁ * s₂`. -/
theorem toOuterMeasure_bind_ge_mul (p : PMF α) (kernel : α → PMF β)
    (pre : Set α) (event : Set β) {s₁ s₂ : ℝ} (hs₂ : 0 ≤ s₂)
    (hp : s₁ ≤ (p.toOuterMeasure pre).toReal)
    (hstep : ∀ a ∈ p.support, a ∈ pre → s₂ ≤ ((kernel a).toOuterMeasure event).toReal) :
    s₁ * s₂ ≤ ((p.bind kernel).toOuterMeasure event).toReal := by
  classical
  have hle : p.toOuterMeasure pre * ENNReal.ofReal s₂ ≤ (p.bind kernel).toOuterMeasure event := by
    rw [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_apply, ← ENNReal.tsum_mul_right]
    refine tsum_le_tsum fun a => ?_
    by_cases ha : a ∈ pre
    · simp only [Set.indicator_of_mem ha]
      by_cases hs : a ∈ p.support
      · exact mul_le_mul_of_nonneg_left
          ((ENNReal.ofReal_le_iff_le_toReal (toOuterMeasure_ne_top _ _)).mpr (hstep a hs ha))
          zero_le
      · have hz : p a = 0 := by simpa only [PMF.mem_support_iff, not_not] using hs
        simp [hz]
    · simp [Set.indicator_of_notMem ha]
  have htoReal := ENNReal.toReal_mono (toOuterMeasure_ne_top _ _) hle
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hs₂] at htoReal
  exact (mul_le_mul_of_nonneg_right hp hs₂).trans htoReal

/-- If a randomized test beats a threshold on average, at least its excess probability mass
consists of inputs whose conditional acceptance probability reaches that threshold. -/
theorem toOuterMeasure_rate_ge (p : PMF α) (kernel : α → PMF β) (event : Set β)
    {threshold : ℝ} (hthreshold : 0 ≤ threshold) :
    ((p.bind kernel).toOuterMeasure event).toReal - threshold ≤
      (p.toOuterMeasure {a | threshold ≤ ((kernel a).toOuterMeasure event).toReal}).toReal := by
  have h := toOuterMeasure_bind_failure_toReal_le p kernel
    {a | ((kernel a).toOuterMeasure event).toReal < threshold} event hthreshold
    (fun a _ ha => le_of_lt ha)
  simpa only [Set.compl_ofPred, not_lt] using (sub_le_iff_le_add.mpr h)

/-! ### Boolean distributions -/

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
