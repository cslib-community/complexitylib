/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Smooth switches with Lipschitz roots

A *switch* `χ_{α,β}` is a nondecreasing function that vanishes on `(-∞, α]` and is one on
`[β, ∞)`. The stochastic atoms of the OpenAI preprint need switches such that `χ_{α,β} ^ (1/s)`
and `(1 - χ_{α,β}) ^ (1/s)` are Lipschitz, so that errors in the root metrics of the later
estimates propagate linearly through every cutoff [OpenAI2026LogSpace, Section 5.1].

We take Mathlib's `Real.smoothTransition`, rescaled to `[α, β]` (`Cslib.smoothSwitch`). The
preprint instead rescales a normalized integral of `z^{s-1} (1 - z)^{s-1}`; any fixed switch with
these properties serves. Every positive power of `Real.smoothTransition` is again continuously
differentiable, since `exp (-1/x) ^ p = exp (-1/(x/p))`, and it is constant outside `[0, 1]`. Hence
every positive power is Lipschitz (`Real.smoothTransition.exists_lipschitzWith_rpow`).
The complement is the reflection
`1 - smoothTransition x = smoothTransition (1 - x)` (`Real.smoothTransition.one_sub`), so its powers
are Lipschitz too.

## Main definitions

* `Cslib.smoothSwitch`: the switch `χ_{α,β}`.

## Main results

* `Real.smoothTransition.one_sub`: the complement of the transition is its reflection.
* `Real.smoothTransition.exists_lipschitzWith_rpow`,
  `Real.smoothTransition.exists_lipschitzWith_one_sub_rpow`: positive powers of the transition
  and of its complement are Lipschitz.
* `Cslib.smoothSwitch_eq_zero_iff`, `Cslib.smoothSwitch_eq_one_iff`, `Cslib.smoothSwitch_nonneg`,
  `Cslib.smoothSwitch_le_one`, `Cslib.monotone_smoothSwitch`: the switch properties.
* `Cslib.exists_lipschitzWith_smoothSwitch_rpow`,
  `Cslib.exists_lipschitzWith_one_sub_smoothSwitch_rpow`: the root-Lipschitz properties.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Section 5.1 (preprint, not peer reviewed)
-/

public section

open Set

namespace Real.smoothTransition

/-- The complement of the smooth transition is its reflection at `1/2`. -/
theorem one_sub (x : ℝ) : 1 - smoothTransition x = smoothTransition (1 - x) := by
  have hD := pos_denom x
  simp only [smoothTransition, sub_sub_cancel]
  rw [add_comm (expNegInvGlue (1 - x)), eq_div_iff hD.ne', sub_mul, div_mul_cancel₀ _ hD.ne']
  ring

/-- A positive power of `expNegInvGlue` is a rescaling of it. -/
private theorem expNegInvGlue_rpow {p : ℝ} (hp : 0 < p) (x : ℝ) :
    expNegInvGlue x ^ p = expNegInvGlue (x / p) := by
  rcases le_or_gt x 0 with hx | hx
  · rw [expNegInvGlue.zero_of_nonpos hx, expNegInvGlue.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg hx hp.le), Real.zero_rpow hp.ne']
  · have hxp : ¬ x / p ≤ 0 := not_le.2 (div_pos hx hp)
    simp only [expNegInvGlue, not_le.2 hx, hxp, ite_false, ← Real.exp_mul]
    congr 1
    field_simp

/-- Positive powers of the smooth transition are smooth. -/
private theorem contDiff_rpow {p : ℝ} (hp : 0 < p) :
    ContDiff ℝ 1 fun x => smoothTransition x ^ p := by
  have h : (fun x => smoothTransition x ^ p) = fun x =>
      expNegInvGlue (x / p) / (expNegInvGlue x + expNegInvGlue (1 - x)) ^ p := by
    funext x
    rw [smoothTransition, Real.div_rpow (expNegInvGlue.nonneg x) (pos_denom x).le,
      expNegInvGlue_rpow hp]
  rw [h]
  refine (expNegInvGlue.contDiff.comp (contDiff_id.div_const p)).div ?_ fun x =>
    (Real.rpow_pos_of_pos (pos_denom x) p).ne'
  exact (expNegInvGlue.contDiff.add (expNegInvGlue.contDiff.comp
    (contDiff_const.sub contDiff_id))).rpow_const_of_ne fun x => (pos_denom x).ne'

/-- A function of the smooth transition that is `C¹` is Lipschitz, since the transition is
constant outside `[0, 1]`. -/
private theorem exists_lipschitzWith_comp {g : ℝ → ℝ}
    (hg : ContDiff ℝ 1 fun x => g (smoothTransition x)) :
    ∃ K, LipschitzWith K fun x => g (smoothTransition x) := by
  obtain ⟨K, hK⟩ := hg.contDiffOn.exists_lipschitzOnWith (s := Icc (0 : ℝ) 1) one_ne_zero
    (convex_Icc 0 1) isCompact_Icc
  refine ⟨K, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  have hproj := (LipschitzWith.projIcc (zero_le_one' ℝ)).dist_le_mul x y
  rw [← smoothTransition.projIcc (x := x), ← smoothTransition.projIcc (x := y)]
  refine (hK.dist_le_mul _ (projIcc 0 1 _ x).2 _ (projIcc 0 1 _ y).2).trans ?_
  rw [Subtype.dist_eq] at hproj
  simp only [NNReal.coe_one, one_mul] at hproj
  exact mul_le_mul_of_nonneg_left hproj K.2

/-- Every positive power of the smooth transition is Lipschitz. -/
theorem exists_lipschitzWith_rpow {p : ℝ} (hp : 0 < p) :
    ∃ K, LipschitzWith K fun x => smoothTransition x ^ p :=
  exists_lipschitzWith_comp (g := fun t => t ^ p) (contDiff_rpow hp)

/-- Every positive power of the complement of the smooth transition is Lipschitz. -/
theorem exists_lipschitzWith_one_sub_rpow {p : ℝ} (hp : 0 < p) :
    ∃ K, LipschitzWith K fun x => (1 - smoothTransition x) ^ p := by
  obtain ⟨K, hK⟩ := exists_lipschitzWith_rpow hp
  refine ⟨K, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  simp only [one_sub]
  simpa only [dist_sub_left] using hK.dist_le_mul (1 - x) (1 - y)

end smoothTransition

end Real

namespace Cslib

open Real

/-- The switch `χ_{α,β}`: `Real.smoothTransition` rescaled from `[0, 1]` to `[α, β]`. It vanishes
on `(-∞, α]`, is one on `[β, ∞)` and is nondecreasing [OpenAI2026LogSpace, Section 5.1]. -/
noncomputable def smoothSwitch (α β t : ℝ) : ℝ :=
  smoothTransition ((t - α) / (β - α))

variable {α β t : ℝ}

theorem smoothSwitch_nonneg (α β t : ℝ) : 0 ≤ smoothSwitch α β t :=
  smoothTransition.nonneg _

theorem smoothSwitch_le_one (α β t : ℝ) : smoothSwitch α β t ≤ 1 :=
  smoothTransition.le_one _

theorem smoothSwitch_eq_zero_iff (hαβ : α < β) : smoothSwitch α β t = 0 ↔ t ≤ α := by
  rw [smoothSwitch, smoothTransition.zero_iff_nonpos, div_le_iff₀ (sub_pos.2 hαβ), zero_mul,
    sub_nonpos]

theorem smoothSwitch_eq_one_iff (hαβ : α < β) : smoothSwitch α β t = 1 ↔ β ≤ t := by
  rw [smoothSwitch, smoothTransition.eq_one_iff_one_le, one_le_div (sub_pos.2 hαβ),
    sub_le_sub_iff_right]

theorem smoothSwitch_of_le (hαβ : α < β) (ht : t ≤ α) : smoothSwitch α β t = 0 :=
  (smoothSwitch_eq_zero_iff hαβ).2 ht

theorem smoothSwitch_of_ge (hαβ : α < β) (ht : β ≤ t) : smoothSwitch α β t = 1 :=
  (smoothSwitch_eq_one_iff hαβ).2 ht

theorem monotone_smoothSwitch (hαβ : α ≤ β) : Monotone (smoothSwitch α β) :=
  fun _ _ h => smoothTransition.monotone
    (div_le_div_of_nonneg_right (sub_le_sub_right h α) (sub_nonneg.2 hαβ))

/-- Rescaling the argument of a Lipschitz function. -/
private theorem lipschitzWith_comp_rescale {g : ℝ → ℝ} {K : NNReal} (hg : LipschitzWith K g)
    (hαβ : α < β) :
    LipschitzWith (K * (β - α)⁻¹.toNNReal) fun t => g ((t - α) / (β - α)) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  refine (hg.dist_le_mul _ _).trans (le_of_eq ?_)
  rw [NNReal.coe_mul, Real.coe_toNNReal _ (inv_nonneg.2 (sub_pos.2 hαβ).le), Real.dist_eq,
    Real.dist_eq, ← sub_div, sub_sub_sub_cancel_right, abs_div, abs_of_pos (sub_pos.2 hαβ),
    div_eq_mul_inv]
  ring

/-- Every positive power of a switch is Lipschitz; for `p = 1/s` this is the root-Lipschitz
property of [OpenAI2026LogSpace, Section 5.1]. -/
theorem exists_lipschitzWith_smoothSwitch_rpow (hαβ : α < β) {p : ℝ} (hp : 0 < p) :
    ∃ K, LipschitzWith K fun t => smoothSwitch α β t ^ p := by
  obtain ⟨K, hK⟩ := smoothTransition.exists_lipschitzWith_rpow hp
  exact ⟨_, lipschitzWith_comp_rescale hK hαβ⟩

/-- Every positive power of the complement of a switch is Lipschitz. -/
theorem exists_lipschitzWith_one_sub_smoothSwitch_rpow (hαβ : α < β) {p : ℝ} (hp : 0 < p) :
    ∃ K, LipschitzWith K fun t => (1 - smoothSwitch α β t) ^ p := by
  obtain ⟨K, hK⟩ := smoothTransition.exists_lipschitzWith_one_sub_rpow hp
  exact ⟨_, lipschitzWith_comp_rescale hK hαβ⟩

end Cslib
