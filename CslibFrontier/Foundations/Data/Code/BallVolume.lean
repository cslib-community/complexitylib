/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import Mathlib.InformationTheory.Hamming
import CslibFrontier.Foundations.Data.Code.HammingBound
import CslibFrontier.Foundations.Data.Nat.Choose.Entropy

/-!
# The entropy bound on the volume of a Hamming ball

Over an alphabet of `q` letters at each of `n` positions, a Hamming ball of radius `r ≤ α n`
with `α ≤ 1 - 1 / q` has at most `exp (n H_q(α))` words, where `H_q = Real.qaryEntropy q` is the
`q`-ary entropy in nats
[Guruswami, Rudra and Sudan, Proposition 3.3.3][GuruswamiRudraSudan2019]. This is the size of the
ball (`Cslib.Code.card_filter_hammingDist_le_eq_sum`,
`Cslib.Code.card_filter_hammingDist_eq_choose_mul_pow`) combined with the entropy bound on partial
binomial sums `Cslib.sum_choose_mul_pow_le_exp_mul_qaryEntropy`.

## Main results

* `Cslib.Code.card_filter_hammingDist_le_le_exp_mul_qaryEntropy`: the entropy bound on the volume
  of a Hamming ball.

## References

* [V. Guruswami, A. Rudra, M. Sudan, *Essential Coding Theory*][GuruswamiRudraSudan2019], draft of
  26 August 2025
-/

public section

namespace Cslib.Code

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {β : ι → Type*} [∀ i, Fintype (β i)]
  [∀ i, DecidableEq (β i)]

/-- **The entropy bound on the volume of a Hamming ball** [Guruswami, Rudra and Sudan,
Proposition 3.3.3][GuruswamiRudraSudan2019]: over `q` letters at each of `n` positions, the
ball of radius `r ≤ α n` about any word has at most `exp (n H_q(α))` words when
`α ≤ 1 - 1 / q`. -/
theorem card_filter_hammingDist_le_le_exp_mul_qaryEntropy {q : ℕ}
    (hq : ∀ i, Fintype.card (β i) = q) (x : ∀ i, β i) {r : ℕ} {α : ℝ}
    (hα : α ≤ 1 - 1 / q) (hr : (r : ℝ) ≤ α * Fintype.card ι) :
    (#{y : ∀ i, β i | hammingDist x y ≤ r} : ℝ) ≤ exp (Fintype.card ι * qaryEntropy q α) := by
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with hcard | hcard
  · have : IsEmpty ι := Fintype.card_eq_zero_iff.mp hcard
    calc (#{y : ∀ i, β i | hammingDist x y ≤ r} : ℝ)
        ≤ (Fintype.card (∀ i, β i) : ℝ) := by exact_mod_cast card_le_univ _
      _ = 1 := by simp
      _ = exp (Fintype.card ι * qaryEntropy q α) := by simp
  have hα₀ : 0 ≤ α := by
    by_contra! hneg
    have : (r : ℝ) < 0 := hr.trans_lt (mul_neg_of_neg_of_pos hneg (by exact_mod_cast hcard))
    linarith [Nat.cast_nonneg (α := ℝ) r]
  have hq0 : q ≠ 0 := by
    rintro rfl
    obtain ⟨i₀⟩ := Fintype.card_pos_iff.mp hcard
    exact (Fintype.card_eq_zero_iff.mp (hq i₀)).false (x i₀)
  rcases lt_or_ge q 2 with hq1 | hq₂
  · obtain rfl : q = 1 := by omega
    have hα0 : α = 0 := le_antisymm (by simpa using hα) hα₀
    have huniv : Fintype.card (∀ i, β i) = 1 := by simp [Fintype.card_pi, hq]
    calc (#{y : ∀ i, β i | hammingDist x y ≤ r} : ℝ)
        ≤ (Fintype.card (∀ i, β i) : ℝ) := by exact_mod_cast card_le_univ _
      _ = 1 := by simp [huniv]
      _ = exp (Fintype.card ι * qaryEntropy 1 α) := by simp [hα0]
  rw [card_filter_hammingDist_le_eq_sum,
    sum_congr rfl fun j _ => card_filter_hammingDist_eq_choose_mul_pow hq x j]
  exact sum_choose_mul_pow_le_exp_mul_qaryEntropy hq₂ hα₀ hα hr

end Cslib.Code
