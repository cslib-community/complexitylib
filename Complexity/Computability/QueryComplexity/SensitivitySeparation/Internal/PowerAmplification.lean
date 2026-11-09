/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.QueryComplexity.SensitivitySeparation.Internal.Iterates
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Superquadratic sensitivity separation: power amplification

Amplification by iterated composition. If a Boolean function `f` vanishing at the all-false input
has `sensitivity f ≤ A` and block sensitivity at least `B` there, where `1 < A` and `A ^ 2 < B`,
then its iterates `iterateFin f m` satisfy `s ^ α ≤ bs` for the fixed exponent
`α = Real.log B / Real.log A > 2`, their ratio `bs / s ^ 2` is at least `(B / A ^ 2) ^ m`, and their
block sensitivity tends to infinity.

## Main results

* `log_exponent_gt_two`: `2 < Real.log B / Real.log A` when `1 < A` and `A ^ 2 < B`.
* `rpow_log_exponent`: `A ^ (Real.log B / Real.log A) = B` for `1 < A` and `0 < B`.
* `power_amplification`: the iterates of a seed with a strict quadratic gap give a separation with a
  fixed exponent `α > 2`.

## References

* Adapted from OpenAI's formalization [OpenAI2026Sensitivity] at revision
  adc7f1241b42e322a6451854ab7e4b4c146bf78a (file
  lean/OAI/Combinatorics/Sensitivity/PowerAmplification.lean), via the complexitylib port
  [Schlesinger2026Sensitivity] at revision add0aca8ee0d71e68969f2cb45cf91554a50f787.
-/

@[expose] public section

namespace Cslib.QueryComplexity.SensitivitySeparation

noncomputable section

namespace Internal

/-- If `1 < A` and `A ^ 2 < B`, then `2 < Real.log B / Real.log A`. -/
theorem log_exponent_gt_two {A B : ℝ} (hA : 1 < A) (hB : A ^ 2 < B) :
    2 < Real.log B / Real.log A := by
  apply (lt_div_iff₀ (Real.log_pos hA)).mpr
  calc
    2 * Real.log A = Real.log (A ^ 2) := by rw [Real.log_pow]; norm_num
    _ < Real.log B := Real.log_lt_log (pow_pos (by linarith) _) hB

/-- If `1 < A` and `0 < B`, then `A ^ (Real.log B / Real.log A) = B`. -/
theorem rpow_log_exponent {A B : ℝ} (hA : 1 < A) (hB : 0 < B) :
    A ^ (Real.log B / Real.log A) = B := by
  apply (Real.mul_log_eq_log_iff (by linarith) hB).mp
  exact div_mul_cancel₀ _ (ne_of_gt (Real.log_pos hA))

/-- Let `f (fun _ => false) = false`, `sensitivity f ≤ A` and
`B ≤ blockSensitivityAt f (fun _ => false)` with `1 < A` and `A ^ 2 < B`, and let
`α = Real.log B / Real.log A`. Then `2 < α`; for every `m`, the iterate `g = iterateFin f m` has
`Fintype.card I ^ m > 0` variables, vanishes at the all-false input, is nonconstant, and satisfies
`sensitivity g ^ α ≤ blockSensitivityAt g (fun _ => false)` and
`(B / A ^ 2) ^ m ≤ blockSensitivity g / sensitivity g ^ 2`; and the block sensitivity of the
iterates at the all-false input tends to infinity. -/
theorem power_amplification {I : Type} [Fintype I]
    (f : (I → Bool) → Bool) (hf : f (fun _ => false) = false)
    (A B : ℕ) (hs : sensitivity f ≤ A)
    (hb : B ≤ blockSensitivityAt f (fun _ => false))
    (hA : 1 < A) (hB : A ^ 2 < B) :
    let α := Real.log (B : ℝ) / Real.log (A : ℝ)
    2 < α ∧
      (∀ m : ℕ,
        0 < Fintype.card I ^ m ∧
        iterateFin f m (fun _ => false) = false ∧
        (∃ x y, iterateFin f m x ≠ iterateFin f m y) ∧
        (sensitivity (iterateFin f m) : ℝ) ^ α ≤
          (blockSensitivityAt (iterateFin f m) (fun _ => false) : ℝ) ∧
        ((B : ℝ) / (A : ℝ) ^ 2) ^ m ≤
          (blockSensitivity (iterateFin f m) : ℝ) /
            (sensitivity (iterateFin f m) : ℝ) ^ 2) ∧
      Filter.Tendsto
        (fun m : ℕ => (blockSensitivityAt (iterateFin f m) (fun _ => false) : ℝ))
        Filter.atTop Filter.atTop := by
  have hAr : 1 < (A : ℝ) := by exact_mod_cast hA
  have hBr : (A : ℝ) ^ 2 < (B : ℝ) := by exact_mod_cast hB
  have hAp : 0 < (A : ℝ) := by linarith
  have hB1 : 1 < (B : ℝ) := by nlinarith
  have hBp : 0 < (B : ℝ) := by linarith
  have hBn : 0 < B := by exact_mod_cast hBp
  have hbf : 0 < blockSensitivityAt f (fun _ => false) := lt_of_lt_of_le hBn hb
  have hcard : 0 < Fintype.card I := by
    by_contra h
    have : IsEmpty I := Fintype.card_eq_zero_iff.mp (Nat.eq_zero_of_not_pos h)
    obtain ⟨x, y, hxy⟩ := nonconstant_of_blockSensitivityAt_pos f (fun _ => false) hbf
    exact hxy (congrArg f (funext fun i => isEmptyElim i))
  have hα := log_exponent_gt_two hAr hBr
  have hpow := rpow_log_exponent hAr hBp
  have hs' (m : ℕ) : (sensitivity (iterateFin f m) : ℝ) ≤ (A : ℝ) ^ m := by
    have hp : sensitivity f ^ m ≤ A ^ m := by gcongr
    exact_mod_cast (sensitivity_iterateFin_le f m).trans hp
  have hb' (m : ℕ) : (B : ℝ) ^ m ≤
      (blockSensitivityAt (iterateFin f m) (fun _ => false) : ℝ) := by
    have hp : B ^ m ≤ blockSensitivityAt f (fun _ => false) ^ m := by gcongr
    exact_mod_cast hp.trans (blockSensitivityAt_iterateFin_zero f hf m)
  refine ⟨hα, ?_, Filter.tendsto_atTop_mono hb' (tendsto_pow_atTop_atTop_of_one_lt hB1)⟩
  intro m
  have hnc := iterateFin_nonconstant f hf hbf m
  have hspos : 0 < (sensitivity (iterateFin f m) : ℝ) := by
    exact_mod_cast sensitivity_pos_of_nonconstant (iterateFin f m) hnc
  refine ⟨pow_pos hcard m, iterateFin_zero f hf m, hnc, ?_, ?_⟩
  · calc
      _ ≤ ((A : ℝ) ^ m) ^ (Real.log (B : ℝ) / Real.log (A : ℝ)) :=
        Real.rpow_le_rpow (le_of_lt hspos) (hs' m) (by linarith)
      _ = ((A : ℝ) ^ (Real.log (B : ℝ) / Real.log (A : ℝ))) ^ m := by
        rw [← Real.rpow_natCast_mul hAp.le,
          mul_comm (m : ℝ), Real.rpow_mul_natCast hAp.le]
      _ = (B : ℝ) ^ m := by rw [hpow]
      _ ≤ _ := hb' m
  · apply (le_div_iff₀ (pow_pos hspos 2)).mpr
    have hsq : (sensitivity (iterateFin f m) : ℝ) ^ 2 ≤ ((A : ℝ) ^ m) ^ 2 := by
      gcongr
      exact hs' m
    have hden : ((A : ℝ) ^ 2) ^ m = ((A : ℝ) ^ m) ^ 2 := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm 2 m]
    calc
      _ ≤ ((B : ℝ) / (A : ℝ) ^ 2) ^ m * ((A : ℝ) ^ m) ^ 2 := by gcongr
      _ = (B : ℝ) ^ m := by
        rw [div_pow, hden]
        exact div_mul_cancel₀ _ (ne_of_gt (pow_pos (pow_pos hAp m) 2))
      _ ≤ (blockSensitivityAt (iterateFin f m) (fun _ => false) : ℝ) := hb' m
      _ ≤ (blockSensitivity (iterateFin f m) : ℝ) := by
        exact_mod_cast blockSensitivityAt_le_blockSensitivity (iterateFin f m) (fun _ => false)

end Internal

end

end Cslib.QueryComplexity.SensitivitySeparation
