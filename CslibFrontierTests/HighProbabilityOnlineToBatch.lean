/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.MachineLearning.OnlineLearning.HighProbabilityOnlineToBatch

/-! Checks for the high-probability online-to-batch conversion.

* Hoeffding's inequality, as the special case of a learner that ignores the sample: a fixed
  hypothesis with losses in `[0, 1]` has true risk within `√(ln (1 / δ) / (2 T))` of its
  empirical risk, except with probability at most `δ`.
* A learner that predicts the previous example of a Boolean sample, under the 0-1 loss, for an
  arbitrary distribution on `Bool`. Its iterates depend on the sample.
* The convex corollary for the absolute loss `|w - z|` on `K = [0, 1]` and a learner that plays
  the previous example clipped to `[0, 1]`. Only the trivial regret bound `T` is used, so the
  bound is weak. -/

namespace CslibFrontierTests.HighProbabilityOnlineToBatch

open Cslib.MachineLearning Cslib.MachineLearning.OnlineLearning MeasureTheory

/-! ### Hoeffding's inequality -/

/-- A fixed hypothesis `u` with losses in `[0, 1]`: except with probability at most `δ`, its true
risk exceeds its empirical risk on `T` i.i.d. examples by at most `√(ln (1 / δ) / (2 T))`. -/
example {Z W : Type*} [MeasurableSpace Z] (D : Measure Z) [IsProbabilityMeasure D] {T : ℕ}
    (hT : 0 < T) {ℓ : W → Z → ℝ} {u : W} (hℓ : Measurable (ℓ u))
    (h01 : ∀ z, ℓ u z ∈ Set.Icc 0 1) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (Measure.pi fun _ : Fin T => D).real {S | (T : ℝ)⁻¹ * ∑ t, ℓ u (S t) +
      √(Real.log (1 / δ) / (2 * T)) < trueRisk ℓ D u} ≤ δ := by
  have h := measureReal_average_integral_gt_le (D := D) (f := fun (_ : Fin T) _ z => ℓ u z)
    (fun _ => hℓ.comp measurable_snd) (fun _ _ _ _ _ => rfl) (fun _ _ z => h01 z) hδ hδ1
  have hTr : (T : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
  simpa [trueRisk_def, Finset.sum_const, Finset.card_univ, hTr] using h

/-! ### Predicting the previous example -/

/-- The prediction of the previous example: `S (t - 1)` in round `t > 0`, and `x₀` in round `0`. -/
def previous {α : Type*} (x₀ : α) {T : ℕ} (t : Fin T) (S : Fin T → α) : α :=
  if h : 0 < t.val then S ⟨t.val - 1, by omega⟩ else x₀

theorem previous_update {α : Type*} (x₀ : α) {T : ℕ} (t s : Fin T) (hts : t ≤ s) (S : Fin T → α)
    (z : α) : previous x₀ t (Function.update S s z) = previous x₀ t S := by
  unfold previous
  split_ifs with h
  · rw [Function.update_of_ne]
    intro heq
    have := congrArg Fin.val heq
    simp only at this
    have : t.val ≤ s.val := hts
    omega
  · rfl

theorem measurable_previous {α : Type*} [MeasurableSpace α] (x₀ : α) {T : ℕ} (t : Fin T) :
    Measurable (previous x₀ t) := by
  by_cases h : 0 < t.val
  · have e : previous x₀ t = fun S : Fin T → α => S ⟨t.val - 1, by omega⟩ :=
      funext fun S => dite_eq_left h
    rw [e]
    exact measurable_pi_apply _
  · have e : previous x₀ t = fun _ : Fin T → α => x₀ := funext fun S => dite_eq_right h
    rw [e]
    exact measurable_const

/-- The 0-1 loss of the prediction `w` on the example `z`. -/
noncomputable def zeroOne (w z : Bool) : ℝ := if w = z then 0 else 1

theorem zeroOne_mem_Icc (w z : Bool) : zeroOne w z ∈ Set.Icc 0 1 := by
  unfold zeroOne
  split_ifs <;> norm_num

/-- For every distribution on `Bool`, except with probability at most `δ`, the average true risk
of the previous-example predictions exceeds their average 0-1 loss by at most
`√(ln (1 / δ) / (2 T))`. -/
example (D : Measure Bool) [IsProbabilityMeasure D] {T : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) :
    (Measure.pi fun _ : Fin T => D).real {S | (T : ℝ)⁻¹ * ∑ t, zeroOne (previous false t S) (S t) +
      √(Real.log (1 / δ) / (2 * T)) < (T : ℝ)⁻¹ * ∑ t, trueRisk zeroOne D (previous false t S)}
      ≤ δ := by
  simpa using measureReal_average_trueRisk_gt_le (D := D) (ℓ := zeroOne)
    (measurable_of_countable _) (measurable_previous false) (previous_update false)
    (fun _ _ _ => zeroOne_mem_Icc _ _) hδ hδ1

/-! ### The convex corollary -/

/-- The absolute loss of the prediction `w` on the example `z`. -/
noncomputable def absLoss (w z : ℝ) : ℝ := |w - z|

/-- The previous example, clipped to `[0, 1]`. -/
noncomputable def clipPrevious {T : ℕ} (t : Fin T) (S : Fin T → ℝ) : ℝ :=
  max 0 (min 1 (previous 0 t S))

theorem clipPrevious_mem {T : ℕ} (t : Fin T) (S : Fin T → ℝ) : clipPrevious t S ∈ Set.Icc 0 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

/-- For a distribution `D` on `ℝ` with a first moment and a comparator `u ∈ [0, 1]`, except with
probability at most `δ`, the average clipped previous example has true risk at most
`L_D u + 1 + √(2 ln (1 / δ) / T)`. -/
example (D : Measure ℝ) [IsProbabilityMeasure D] (hD : Integrable id D) {T : ℕ} (hT : 0 < T)
    {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (Measure.pi fun _ : Fin T => D).real {S | trueRisk absLoss D u + 1 +
      √(2 * Real.log (1 / δ) / T) < trueRisk absLoss D ((T : ℝ)⁻¹ • ∑ t, clipPrevious t S)}
      ≤ δ := by
  have hui : Integrable (absLoss u) D :=
    ((integrable_const u).sub hD).abs.congr (Filter.Eventually.of_forall fun z => rfl)
  have hTr : (T : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
  have hdiff : ∀ w ∈ Set.Icc (0 : ℝ) 1, ∀ z, |absLoss w z - absLoss u z| ≤ 1 := fun w hw z => by
    unfold absLoss
    refine (abs_abs_sub_abs_le_abs_sub _ _).trans ?_
    rw [sub_sub_sub_cancel_right, abs_le]
    constructor <;> linarith [hw.1, hw.2, hu.1, hu.2]
  have hℓ : Measurable (Function.uncurry absLoss) :=
    (continuous_abs.comp (continuous_fst.sub continuous_snd)).measurable
  have h := measureReal_trueRisk_average_gt_le (D := D) (ℓ := absLoss) hT (convex_Icc 0 1) hℓ
    (fun z => (convexOn_dist z (convex_Icc (0 : ℝ) 1)).congr fun w _ => Real.dist_eq w z)
    hui hdiff clipPrevious_mem
    (fun t => measurable_const.max (measurable_const.min (measurable_previous 0 t)))
    (fun t s hts S z => by rw [clipPrevious, clipPrevious, previous_update 0 t s hts])
    (R := T) (fun S => by
      calc ∑ t, (absLoss (clipPrevious t S) (S t) - absLoss u (S t))
          ≤ ∑ _t : Fin T, (1 : ℝ) := Finset.sum_le_sum fun t _ =>
            (le_abs_self _).trans (hdiff _ (clipPrevious_mem t S) _)
        _ = T := by simp)
    hδ hδ1
  simpa [div_self hTr] using h

end CslibFrontierTests.HighProbabilityOnlineToBatch
