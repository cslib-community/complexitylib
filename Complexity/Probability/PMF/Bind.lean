/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josha Dekker, Devon Tuma, Kexing Ying, Samuel Schlesinger
-/

module
-- upstream: candidate (addition to `Cslib/Probability/PMF.lean`)

public import Complexity.Probability.PMF

/-!
# Two-stage experiments

A two-stage experiment `μ.bind f` gives an outcome `b` the probability `c` when every possible
second stage does (`bind_apply_of_forall`), and some possible first stage gives `b` at least the
probability of the whole experiment (`exists_bind_apply_le`). Continuations need agree, or be
compared, only on outcomes the first stage can produce (`bind_congr_on_support`,
`le_bind_apply_on_support`, `bind_apply_mono_on_support`). Averages of bounded values are bounded
(`tsum_mul_le_of_forall_le`, `tsum_mul_le_card_mul_add`), and the pairing law holds for dependent
second samples (`bind_sigma_apply`).

## Main results

* `Cslib.Probability.PMF.bind_congr_on_support`: continuations need agree only on possible inputs.
* `Cslib.Probability.PMF.bind_apply_of_forall`, `Cslib.Probability.PMF.exists_bind_apply_le`:
  outcome probabilities of two-stage experiments.
* `Cslib.Probability.PMF.le_bind_apply_on_support`,
  `Cslib.Probability.PMF.bind_apply_le_on_support`,
  `Cslib.Probability.PMF.bind_apply_mono_on_support`: comparing continuations at one outcome.
* `Cslib.Probability.PMF.tsum_mul_le_of_forall_le`,
  `Cslib.Probability.PMF.tsum_mul_le_card_mul_add`: averages of bounded values.
* `Cslib.Probability.PMF.bind_sigma_apply`: the pairing law for dependent second samples.

## References

Adapted in part from Probability/PMF.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`.
-/

@[expose] public section

namespace Cslib.Probability.PMF

open scoped ENNReal

variable {α β : Type*}

/-- The pairing law also holds when the second sample's type depends on the first.
Adapted from the cslib `crypto` branch at `5ff69ca`. -/
theorem bind_sigma_apply {β : α → Type*} (p : PMF α) (f : (a : α) → PMF (β a))
    (a : α) (b : β a) :
    (p.bind (fun a => (f a).map (Sigma.mk a))) ⟨a, b⟩ = p a * f a b := by
  classical
  simp only [PMF.bind_apply, PMF.map_apply, ← ENNReal.tsum_mul_left, mul_ite, mul_zero]
  rw [← tsum_sigma]
  simp

/-- A continuation only needs to agree on outcomes the preceding distribution can produce. -/
theorem bind_congr_on_support (p : PMF α) (f g : α → PMF β)
    (h : ∀ a ∈ p.support, f a = g a) : p.bind f = p.bind g := by
  rw [← PMF.bindOnSupport_eq_bind p f, ← PMF.bindOnSupport_eq_bind p g]
  congr 1
  funext a ha
  exact h a ha

/-- If every second stage of a two-stage experiment gives the outcome `b` probability `c`, so
does the experiment. -/
theorem bind_apply_of_forall (μ : PMF α) {f : α → PMF β} {b : β} {c : ℝ≥0∞}
    (h : ∀ a, f a b = c) : μ.bind f b = c := by
  simp only [PMF.bind_apply, h, ENNReal.tsum_mul_right, μ.tsum_coe, one_mul]

/-- A lower bound on an outcome's probability for every possible first-stage result bounds its
probability in the whole experiment. -/
theorem le_bind_apply_on_support (μ : PMF α) {f : α → PMF β} {b : β} {c : ℝ≥0∞}
    (h : ∀ a ∈ μ.support, c ≤ f a b) : c ≤ μ.bind f b := by
  rw [PMF.bind_apply]
  calc c = ∑' a, μ a * c := by rw [ENNReal.tsum_mul_right, μ.tsum_coe, one_mul]
    _ ≤ ∑' a, μ a * f a b := tsum_le_tsum fun a => by
        by_cases ha : a ∈ μ.support
        · exact mul_le_mul_right (h a ha) _
        · simp [(PMF.apply_eq_zero_iff μ a).2 ha]

/-- An upper bound on an outcome's probability for every possible first-stage result bounds its
probability in the whole experiment. -/
theorem bind_apply_le_on_support (μ : PMF α) {f : α → PMF β} {b : β} {c : ℝ≥0∞}
    (h : ∀ a ∈ μ.support, f a b ≤ c) : μ.bind f b ≤ c := by
  rw [PMF.bind_apply]
  calc ∑' a, μ a * f a b
    _ ≤ ∑' a, μ a * c := tsum_le_tsum fun a => by
        by_cases ha : a ∈ μ.support
        · exact mul_le_mul_right (h a ha) _
        · simp [(PMF.apply_eq_zero_iff μ a).2 ha]
    _ = c := by rw [ENNReal.tsum_mul_right, μ.tsum_coe, one_mul]

/-- Increasing an outcome's probability on every possible first-stage result increases its
probability in the whole experiment. The sample spaces may be infinite. -/
theorem bind_apply_mono_on_support (μ : PMF α) {f g : α → PMF β} (b : β)
    (h : ∀ a ∈ μ.support, f a b ≤ g a b) : μ.bind f b ≤ μ.bind g b := by
  simp only [PMF.bind_apply]
  apply tsum_le_tsum
  intro a
  by_cases ha : a ∈ μ.support
  · exact mul_le_mul_right (h a ha) _
  · simp [(μ.apply_eq_zero_iff a).mpr ha]

/-- Some possible outcome of the first stage of a two-stage experiment does at least as well as
the experiment. -/
theorem exists_bind_apply_le [Finite α] (μ : PMF α) (f : α → PMF β) (b : β) :
    ∃ a ∈ μ.support, μ.bind f b ≤ f a b := by
  obtain ⟨a, ha, hmax⟩ :=
    μ.support.exists_max_image (fun a => f a b) μ.support.toFinite μ.support_nonempty
  refine ⟨a, ha, ?_⟩
  exact (bind_apply_mono_on_support μ b hmax).trans_eq
    (bind_apply_of_forall μ fun _ => rfl)

/-- An average of values at most `B` is at most `B`. -/
theorem tsum_mul_le_of_forall_le (μ : PMF α) {f : α → ℝ≥0∞} {B : ℝ≥0∞} (h : ∀ a, f a ≤ B) :
    ∑' a, μ a * f a ≤ B :=
  calc ∑' a, μ a * f a ≤ ∑' a, μ a * B := tsum_le_tsum fun a => mul_le_mul_right (h a) _
    _ = B := by rw [ENNReal.tsum_mul_right, μ.tsum_coe, one_mul]

/-- Values at most `1` on a finite set `T` and at most `B` elsewhere average to at most
`|T| * ε + B` under a distribution giving every point probability at most `ε`. -/
theorem tsum_mul_le_card_mul_add [DecidableEq α] (μ : PMF α) {ε : ℝ≥0∞} (hμ : ∀ a, μ a ≤ ε)
    (T : Finset α) {f : α → ℝ≥0∞} {B : ℝ≥0∞} (h : ∀ a, f a ≤ (if a ∈ T then 1 else 0) + B) :
    ∑' a, μ a * f a ≤ T.card * ε + B := by
  calc ∑' a, μ a * f a ≤ ∑' a, (μ a * (if a ∈ T then 1 else 0) + μ a * B) :=
        tsum_le_tsum fun a => (mul_le_mul_right (h a) _).trans_eq (mul_add _ _ _)
    _ = ∑ a ∈ T, μ a + B := by
        rw [tsum_add, ENNReal.tsum_mul_right, μ.tsum_coe, one_mul,
          tsum_eq_sum (s := T) fun a ha => by simp only [ha, ↓reduceIte, mul_zero]]
        congr 1
        exact Finset.sum_congr rfl fun a ha => by simp only [ha, ↓reduceIte, mul_one]
    _ ≤ T.card * ε + B := by
        gcongr
        calc ∑ a ∈ T, μ a ≤ ∑ _a ∈ T, ε := Finset.sum_le_sum fun a _ => hμ a
          _ = T.card * ε := by rw [Finset.sum_const, nsmul_eq_mul]

end Cslib.Probability.PMF
