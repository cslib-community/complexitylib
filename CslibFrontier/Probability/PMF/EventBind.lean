/-
Copyright (c) 2026 Samuel Schlesinger, Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Renfei Zhou
-/

module
-- upstream: candidate (addition to `Cslib/Probability/PMF.lean`)

public import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Event

/-!
# Event probabilities after a random first stage

After a random first stage, an event's probability is the average of its conditional
probabilities (`toOuterMeasure_bind_toReal`). Failure and success bounds compose without
independence: a randomized continuation fails because its precondition already failed or because
it fails from a valid input (`toOuterMeasure_bind_failure_le`), lower bounds on a first stage and
on its continuation from supported members multiply (`toOuterMeasure_bind_ge_mul_ennreal`,
`toOuterMeasure_bind_ge_mul`), and failure bounds multiply when success is retained
(`toOuterMeasure_bind_le_mul_ennreal`). Average bias turns into the probability of good first
stages (`toOuterMeasure_rate_ge`).

## Main results

* `Cslib.Probability.PMF.toOuterMeasure_bind_toReal`: averaging over a first stage.
* `Cslib.Probability.PMF.toOuterMeasure_bind_le`,
  `Cslib.Probability.PMF.toOuterMeasure_bind_failure_le`,
  `Cslib.Probability.PMF.toOuterMeasure_bind_failure_toReal_le`,
  `Cslib.Probability.PMF.toOuterMeasure_bind_ge_mul`,
  `Cslib.Probability.PMF.toOuterMeasure_bind_ge_mul_ennreal`,
  `Cslib.Probability.PMF.toOuterMeasure_bind_le_mul_ennreal`: composing failure and success bounds.
* `Cslib.Probability.PMF.toOuterMeasure_rate_ge`: average bias as the probability of good inputs.

## References

`toOuterMeasure_bind_toReal`, `toOuterMeasure_bind_failure_le` and
`toOuterMeasure_bind_failure_toReal_le` are adapted from Probability/PMF.lean on the cslib `crypto`
branch at `5ff69ca93402e7c947208dc56396d6d86203ccd8`. The `ENNReal` event-composition lemmas were
extracted from Renfei Zhou's Karger algorithm development.
-/

public section

namespace Cslib.Probability.PMF

open scoped ENNReal

variable {α β : Type*}

/-- Event probability after a finite random choice is the average conditional probability. -/
theorem toOuterMeasure_bind_toReal [Fintype α] (p : PMF α) (kernel : α → PMF β)
    (event : Set β) :
    ((p.bind kernel).toOuterMeasure event).toReal =
      ∑ a, (p a).toReal * ((kernel a).toOuterMeasure event).toReal := by
  rw [PMF.toOuterMeasure_bind_apply, tsum_fintype, ENNReal.toReal_sum
    (fun a _ => ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (toOuterMeasure_ne_top _ _))]
  simp only [ENNReal.toReal_mul]

/-- A uniform upper bound on `(kernel a).toOuterMeasure event` bounds
`(p.bind kernel).toOuterMeasure event`. -/
theorem toOuterMeasure_bind_le (p : PMF α) (kernel : α → PMF β) (event : Set β)
    {error : ENNReal} (h : ∀ a, (kernel a).toOuterMeasure event ≤ error) :
    (p.bind kernel).toOuterMeasure event ≤ error := by
  rw [PMF.toOuterMeasure_bind_apply]
  exact tsum_mul_le_of_forall_le _ h

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

/-- `ENNReal` multiplication rule for sequential success lower bounds across `PMF.bind`. -/
theorem toOuterMeasure_bind_ge_mul_ennreal {α β : Type*} (p : PMF α) (kernel : α → PMF β)
    (pre : Set α) (event : Set β) {s₁ s₂ : ℝ≥0∞}
    (hp : s₁ ≤ p.toOuterMeasure pre)
    (hstep : ∀ a ∈ p.support, a ∈ pre → s₂ ≤ (kernel a).toOuterMeasure event) :
    s₁ * s₂ ≤ (p.bind kernel).toOuterMeasure event := by
  classical
  calc
    s₁ * s₂ ≤ p.toOuterMeasure pre * s₂ := mul_le_mul_of_nonneg_right hp zero_le
    _ ≤ (p.bind kernel).toOuterMeasure event := by
      rw [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_apply, ← ENNReal.tsum_mul_right]
      refine tsum_le_tsum fun a => ?_
      by_cases ha : a ∈ pre
      · simp only [Set.indicator_of_mem ha]
        by_cases hs : a ∈ p.support
        · exact mul_le_mul_of_nonneg_left (hstep a hs ha) zero_le
        · have hz : p a = 0 := by simpa only [PMF.mem_support_iff, not_not] using hs
          simp [hz]
      · simp [Set.indicator_of_notMem ha]

/-- `ENNReal` multiplication rule for sequential failure upper bounds: if `p` stays in
`stillFailing` with probability at most `q₁`, every supported `a ∈ stillFailing` fails under
`kernel a` with probability at most `q₂`, and every supported `a ∉ stillFailing` has zero failure
probability under `kernel a`, then `p.bind kernel` fails with probability at most `q₁ * q₂`. -/
theorem toOuterMeasure_bind_le_mul_ennreal {α β : Type*} (p : PMF α) (kernel : α → PMF β)
    (stillFailing : Set α) (failure : Set β) {q₁ q₂ : ℝ≥0∞}
    (hp : p.toOuterMeasure stillFailing ≤ q₁)
    (hfail : ∀ a ∈ p.support, a ∈ stillFailing → (kernel a).toOuterMeasure failure ≤ q₂)
    (hsucc : ∀ a ∈ p.support, a ∉ stillFailing → (kernel a).toOuterMeasure failure = 0) :
    (p.bind kernel).toOuterMeasure failure ≤ q₁ * q₂ := by
  classical
  calc
    (p.bind kernel).toOuterMeasure failure
      ≤ p.toOuterMeasure stillFailing * q₂ := by
        rw [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_apply, ← ENNReal.tsum_mul_right]
        refine tsum_le_tsum fun a => ?_
        by_cases hs : a ∈ p.support
        · by_cases ha : a ∈ stillFailing
          · simp only [Set.indicator_of_mem ha]
            exact mul_le_mul_of_nonneg_left (hfail a hs ha) zero_le
          · simp [Set.indicator_of_notMem ha, hsucc a hs ha]
        · have hz : p a = 0 := by simpa only [PMF.mem_support_iff, not_not] using hs
          simp [hz]
    _ ≤ q₁ * q₂ := mul_le_mul_of_nonneg_right hp zero_le

/-- If a first stage `p` lands in `pre` with probability at least `s₁` and for every supported
`a ∈ pre` the continuation `kernel a` lands in `event` with probability at least `s₂`, then
`p.bind kernel` lands in `event` with probability at least `s₁ * s₂`. -/
theorem toOuterMeasure_bind_ge_mul (p : PMF α) (kernel : α → PMF β)
    (pre : Set α) (event : Set β) {s₁ s₂ : ℝ} (hs₂ : 0 ≤ s₂)
    (hp : s₁ ≤ (p.toOuterMeasure pre).toReal)
    (hstep : ∀ a ∈ p.support, a ∈ pre → s₂ ≤ ((kernel a).toOuterMeasure event).toReal) :
    s₁ * s₂ ≤ ((p.bind kernel).toOuterMeasure event).toReal := by
  have hle := toOuterMeasure_bind_ge_mul_ennreal p kernel pre event le_rfl
    (fun a ha hpre =>
      (ENNReal.ofReal_le_iff_le_toReal (toOuterMeasure_ne_top _ _)).mpr (hstep a ha hpre))
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

end Cslib.Probability.PMF
