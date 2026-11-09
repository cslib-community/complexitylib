/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.Sign
public import CslibFrontier.Foundations.Data.BitString.Threshold
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith

/-!
# The discriminator lemma for unweighted threshold votes

Suppose that on every point `u` of a finite set `U`, the threshold vote `threshold t θ (v u)` of
`t` voters `v u i` equals a target bit `F u`. In `±1` signs, the votes then correlate with the
target in total: `∑ i, ∑ u, signVal (v u i) * signVal (F u) ≥ |U| - (t + 1) |∑ u, signVal (F u)|`
(`Cslib.sub_le_sum_sum_signVal_mul_of_threshold_eq`). If the target is nearly balanced, some voter
therefore has correlation about `|U| / t` with it; this is the correlation form of the
discriminator lemma of [Hajnal et al.][HMPST1993] for unweighted threshold gates, with any
threshold `θ`, including majority with either tie rule.

The proof is pointwise: with `c = 2 θ - 1 - t`, the signed margin
`signVal (F u) * (c + ∑ i, signVal (v u i))` is at least `1` at every point `u`, and
`|c| ≤ t + 1` unless the vote is constantly `false`.

## Main results

* `Cslib.BitString.sum_signVal_eq_sub_two_mul_weight`: the sign sum of a bit string is its length
  minus twice its weight.
* `Cslib.sub_le_sum_sum_signVal_mul_of_threshold_eq`: the discriminator lemma.

## References

* [A. Hajnal, W. Maass, P. Pudlák, M. Szegedy, G. Turán, *Threshold circuits of bounded
  depth*][HMPST1993]
-/

public section

namespace Cslib

open Finset BitString

/-- The sign sum of a bit string is its length minus twice its weight. -/
theorem BitString.sum_signVal_eq_sub_two_mul_weight {t : ℕ} (x : BitString t) :
    ∑ i, signVal (x i) = t - 2 * (weight x : ℝ) := by
  have h (i : Fin t) : signVal (x i) = 1 - 2 * ((x i).toNat : ℝ) := by
    cases x i <;> norm_num
  rw [sum_congr rfl fun i _ => h i, sum_sub_distrib, ← mul_sum, weight_eq_sum_toNat]
  simp

/-- **The discriminator lemma for unweighted threshold votes**: if the threshold vote
`threshold t θ (v u)` equals `F u` at every point `u` of a finite type `U`, then the votes
correlate with `F` in total by at least `|U| - (t + 1) |∑ u, signVal (F u)|`. This is a
correlation form of the discriminator lemma of [Hajnal et al.][HMPST1993]. -/
theorem sub_le_sum_sum_signVal_mul_of_threshold_eq {U : Type*} [Fintype U] {t θ : ℕ}
    (v : U → BitString t) (F : U → Bool) (h : ∀ u, threshold t θ (v u) = F u) :
    (Fintype.card U : ℝ) - (t + 1) * |∑ u, signVal (F u)| ≤
      ∑ i, ∑ u, signVal (v u i) * signVal (F u) := by
  rw [sum_comm]
  by_cases hθ : t + 1 < θ
  · -- the vote is constantly `false`
    have hF (u : U) : F u = false := by
      rw [← h u]
      exact threshold_eq_false_of_lt (by omega) (v u)
    have hsum : |∑ u, signVal (F u)| = Fintype.card U := by
      simp [hF]
    have hlow (u : U) : -(t : ℝ) ≤ ∑ i, signVal (v u i) * signVal (F u) := by
      rw [hF, signVal_false]
      simp only [mul_one]
      have := weight_le_length (v u)
      rw [sum_signVal_eq_sub_two_mul_weight]
      have : (weight (v u) : ℝ) ≤ t := by exact_mod_cast this
      linarith
    calc (Fintype.card U : ℝ) - (t + 1) * |∑ u, signVal (F u)| = ∑ _u : U, -(t : ℝ) := by
          rw [hsum, sum_const, card_univ, nsmul_eq_mul]
          ring
      _ ≤ _ := sum_le_sum fun u _ => hlow u
  · -- the signed margin is at least one at every point
    set c : ℝ := 2 * θ - 1 - t with hc
    have hc_abs : |c| ≤ t + 1 := by
      have : (θ : ℝ) ≤ t + 1 := by exact_mod_cast not_lt.mp hθ
      rw [abs_le]
      constructor <;> linarith [(Nat.cast_nonneg θ : (0 : ℝ) ≤ θ)]
    have hmargin (u : U) :
        1 ≤ signVal (F u) * c + ∑ i, signVal (v u i) * signVal (F u) := by
      rw [← sum_mul, sum_signVal_eq_sub_two_mul_weight, ← h u, threshold_apply]
      by_cases hle : θ ≤ weight (v u)
      · have : (θ : ℝ) ≤ weight (v u) := by exact_mod_cast hle
        simp only [hle, decide_true, signVal_true, hc]
        linarith
      · have : (weight (v u) : ℝ) + 1 ≤ θ := by exact_mod_cast not_le.mp hle
        simp only [hle, decide_false, signVal_false, hc]
        linarith
    have hsum := sum_le_sum fun u (_ : u ∈ univ) => hmargin u
    rw [sum_add_distrib, ← sum_mul, sum_const, card_univ, nsmul_eq_mul, mul_one] at hsum
    have hcS : (∑ u, signVal (F u)) * c ≤ (t + 1) * |∑ u, signVal (F u)| := by
      calc (∑ u, signVal (F u)) * c ≤ |(∑ u, signVal (F u)) * c| := le_abs_self _
        _ = |c| * |∑ u, signVal (F u)| := by rw [abs_mul, mul_comm]
        _ ≤ (t + 1) * |∑ u, signVal (F u)| :=
            mul_le_mul_of_nonneg_right hc_abs (abs_nonneg _)
    linarith

end Cslib
