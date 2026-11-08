/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import Mathlib.InformationTheory.Hamming
import Complexity.Foundations.Data.Code.HammingBound
import Complexity.Foundations.Data.Nat.Choose.Entropy

/-!
# The entropy bound on the volume of a Hamming ball

Over an alphabet of `q ≥ 2` letters at each of `n` positions, a Hamming ball of radius
`r ≤ α n` with `0 ≤ α ≤ 1 - 1 / q` has at most `exp (n H_q(α))` words, where
`H_q = Real.qaryEntropy q` is the `q`-ary entropy in nats
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
Proposition 3.3.3][GuruswamiRudraSudan2019]: over `q ≥ 2` letters at each of `n` positions, the
ball of radius `r ≤ α n` about any word has at most `exp (n H_q(α))` words when
`0 ≤ α ≤ 1 - 1 / q`. -/
theorem card_filter_hammingDist_le_le_exp_mul_qaryEntropy {q : ℕ} (hq₂ : 2 ≤ q)
    (hq : ∀ i, Fintype.card (β i) = q) (x : ∀ i, β i) {r : ℕ} {α : ℝ} (hα₀ : 0 ≤ α)
    (hα : α ≤ 1 - 1 / q) (hr : (r : ℝ) ≤ α * Fintype.card ι) :
    (#{y : ∀ i, β i | hammingDist x y ≤ r} : ℝ) ≤ exp (Fintype.card ι * qaryEntropy q α) := by
  rw [card_filter_hammingDist_le_eq_sum,
    sum_congr rfl fun j _ => card_filter_hammingDist_eq_choose_mul_pow hq x j]
  exact sum_choose_mul_pow_le_exp_mul_qaryEntropy hq₂ hα₀ hα hr

end Cslib.Code
