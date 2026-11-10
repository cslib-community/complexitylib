/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.PMF
public import Mathlib.Topology.UnitInterval

/-!
# Biased coins

`Cslib.Probability.PMF.coin p` is the coin on `Bool` showing `true` with probability `p ∈ [0, 1]`.
Mathlib's `PMF.bernoulli` is deprecated in favor of `ProbabilityTheory.bernoulliMeasure`, which is a
`Measure`; this is the `PMF` form, for building discrete distributions such as independent products
(`Cslib.Probability.PMF.pi`) of coins.

## Main definitions

* `Cslib.Probability.PMF.coin`: the coin showing `true` with probability `p`.

## Main results

* `Cslib.Probability.PMF.coin_apply`, `Cslib.Probability.PMF.coin_apply_toReal`: the masses of the
  two faces.
* `Cslib.Probability.PMF.coin_eq_uniformOfFintype`: a fair coin is the uniform distribution on
  `Bool`.
-/

public section

namespace Cslib.Probability.PMF

open scoped unitInterval

/-- The coin showing `true` with probability `p` and `false` with probability `1 - p`. -/
noncomputable def coin (p : I) : PMF Bool :=
  PMF.ofFintype (fun b => if b then ENNReal.ofReal p else ENNReal.ofReal (1 - p)) (by
    rw [Fintype.sum_bool, ite_eq_left rfl, ite_eq_right Bool.false_ne_true,
      ← ENNReal.ofReal_add p.2.1 (sub_nonneg.mpr p.2.2), add_sub_cancel, ENNReal.ofReal_one])

theorem coin_apply (p : I) (b : Bool) :
    coin p b = if b then ENNReal.ofReal p else ENNReal.ofReal (1 - p) := by
  rw [coin, PMF.ofFintype_apply]

theorem coin_apply_toReal (p : I) (b : Bool) :
    (coin p b).toReal = if b then (p : ℝ) else 1 - p := by
  cases b
  · simp [coin_apply, p.2.2]
  · simp [coin_apply, p.2.1]

/-- A fair coin is the uniform distribution on `Bool`. -/
theorem coin_eq_uniformOfFintype {p : I} (hp : (p : ℝ) = 1 / 2) :
    coin p = uniformOfFintype Bool := by
  ext b
  have h : (1 : ℝ) - p = 2⁻¹ := by rw [hp]; norm_num
  rw [one_div] at hp
  rw [coin_apply, uniformOfFintype_apply, Fintype.card_bool, Nat.cast_ofNat]
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · rw [h, ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]
  · rw [hp, ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]

end Cslib.Probability.PMF
