/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Foundations.Data.Code.OddCircuitFourier
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Tests: the odd-circuit argument

* The extra parity check: the standard basis of `𝔽₂ⁿ` has no nonempty zero-sum subset, so the
  all-ones vector is `1` on all of it, as `exists_dotProduct_eq_one_of_even` predicts.
* Distance two with one parity check: the nonzero words of weight less than `2` contain no
  circuit at all, so the odd-circuit argument with `m = 0` gives the even-weight code of every
  length `n`, with minimum distance at least `2` and at least `2 ^ (n - 1)` words.
* The moment and tail hypothesis of `exists_le_minDist_parityCheckCode_of_moment_tail` holds for
  `n = 4`, `d = 2`, `m = 4`: there `V = 4`, `τ = 1 / 4`, the tail term vanishes because
  `|μ̂| ≤ 1 < 1 / τ`, and the moment term is at most `16 (sinh 1 - 1) / 64 < 1`.
-/

namespace CslibFrontierTests.OddCircuit

open Finset Matrix Cslib Cslib.Code Real

variable {n : ℕ}

/-- A nonzero word of weight less than `2` over `𝔽₂` is the indicator of any coordinate where it is
nonzero. -/
theorem eq_of_hammingNorm_lt_two {x y : Fin n → ZMod 2} (hx : hammingNorm x < 2)
    (hy : hammingNorm y < 2) {i : Fin n} (hxi : x i ≠ 0) (hyi : y i ≠ 0) : x = y := by
  have hsingle : ∀ z : Fin n → ZMod 2, hammingNorm z < 2 → z i ≠ 0 → z = Pi.single i 1 := by
    intro z hz hzi
    ext j
    by_cases hj : j = i
    · subst hj
      simp only [Pi.single_eq_same]
      revert hzi; generalize z j = a; decide +revert
    · rw [Pi.single_eq_of_ne hj]
      by_contra hzj
      have : 1 < hammingNorm z := by
        rw [hammingNorm, one_lt_card]
        exact ⟨i, by simpa using hzi, j, by simpa using hzj, Ne.symm hj⟩
      omega
  rw [hsingle x hx hxi, hsingle y hy hyi]

/-- No nonempty set of nonzero words of weight less than `2` sums to zero. -/
theorem sum_ne_zero_of_subset {S : Finset (Fin n → ZMod 2)}
    (hS : S ⊆ ({x | x ≠ 0 ∧ hammingNorm x < 2} : Finset (Fin n → ZMod 2)))
    (hne : S.Nonempty) : ∑ x ∈ S, x ≠ 0 := by
  obtain ⟨x, hx⟩ := hne
  have hxB := mem_filter.1 (hS hx)
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra! h
    exact hxB.2.1 (funext h)
  intro hsum
  have hcoord : (∑ y ∈ S, y) i = x i := by
    rw [Finset.sum_apply i S fun y => y, sum_eq_single_of_mem x hx]
    intro y hy hyx
    by_contra hyi
    have hyB := mem_filter.1 (hS hy)
    exact hyx (eq_of_hammingNorm_lt_two hyB.2.2 hxB.2.2 hyi hi)
  rw [hsum] at hcoord
  exact hi hcoord.symm

/-- The standard basis vectors are all `1` under one linear form. -/
example : ∃ v : Fin 3 → ZMod 2, ∀ x ∈ ({Pi.single 0 1, Pi.single 1 1, Pi.single 2 1} :
    Finset (Fin 3 → ZMod 2)), v ⬝ᵥ x = 1 := by
  refine exists_dotProduct_eq_one_of_even fun T hT hT0 => ?_
  have hTB : T ⊆ ({x | x ≠ 0 ∧ hammingNorm x < 2} : Finset (Fin 3 → ZMod 2)) := fun x hx => by
    have := hT hx
    simp only [mem_insert, mem_singleton] at this
    rcases this with rfl | rfl | rfl <;> decide
  rcases T.eq_empty_or_nonempty with rfl | hne
  · simp
  · exact absurd hT0 (sum_ne_zero_of_subset hTB hne)

/-- **The even-weight code from the odd-circuit argument.** With `m = 0` rows before the extra
parity check, the odd-circuit argument produces a one-row parity-check matrix whose code has minimum
distance at least `2` and at least `2 ^ (n - 1)` words. -/
theorem exists_parityCheck_two_le_minDist (n : ℕ) :
    ∃ H : Matrix (Fin 1) (Fin n) (ZMod 2),
      ((2 : ℕ) : ℕ∞) ≤ minDist (parityCheckCode H : Set (Fin n → ZMod 2)) ∧
        2 ^ (n - 1) ≤ Nat.card (parityCheckCode H) := by
  have h := exists_le_minDist_parityCheckCode_of_sum_lt_one (ι := Fin n) 2 0 ?_
  · simpa using h
  rw [sum_eq_zero fun S hS => ?_]
  · norm_num
  obtain ⟨hSB, hS, -⟩ := mem_filter.1 hS
  exact absurd hS.sum_eq_zero (sum_ne_zero_of_subset (mem_powerset.1 hSB)
    ((isZeroSumCircuit_iff.1 hS).1))

/-- The moment and tail hypothesis is satisfiable: `n = 4`, `d = 2`, `m = 4`. -/
theorem exists_code_four_two_four :
    ∃ H : Matrix (Fin (4 + 1)) (Fin 4) (ZMod 2),
      ((2 : ℕ) : ℕ∞) ≤ minDist (parityCheckCode H : Set (Fin 4 → ZMod 2)) ∧
        2 ^ (Fintype.card (Fin 4) - (4 + 1)) ≤ Nat.card (parityCheckCode H) := by
  refine exists_le_minDist_parityCheckCode_of_moment_tail 2 4 ?_
  intro B τ μ
  have hV : #B = 4 := by decide
  have hτ : τ = 1 / 4 := by simp only [τ, hV]; norm_num
  have hμ : ∀ y, |μ y| ≤ 1 := fun y => by
    simp only [μ, abs_div, Nat.abs_cast]
    rw [div_le_one (by rw [hV]; norm_num)]
    exact abs_charSum_le B y
  have htail : #{y | 1 / τ < μ y} = 0 := by
    rw [card_eq_zero, filter_eq_empty_iff]
    intro y _
    rw [hτ, not_lt]
    linarith [le_abs_self (μ y), hμ y]
  have hmoment : (∑ y, |μ y| ^ 3) / 2 ^ Fintype.card (Fin 4) ≤ 1 := by
    rw [div_le_one (by positivity)]
    calc ∑ y, |μ y| ^ 3 ≤ ∑ _y : Fin 4 → ZMod 2, (1 : ℝ) :=
          sum_le_sum fun y _ => pow_le_one₀ (abs_nonneg _) (hμ y)
      _ = 2 ^ Fintype.card (Fin 4) := by simp [ZMod.card]; norm_num
  have hs1 : sinh 1 - 1 < 1 := by
    have := Real.exp_one_lt_three
    rw [sinh_eq]
    nlinarith [exp_pos (-1)]
  have hs0 : 0 ≤ sinh 1 - 1 := sub_nonneg.2 (self_le_sinh_iff.2 zero_le_one)
  rw [htail, hV, hτ]
  generalize (∑ y, |μ y| ^ 3) / 2 ^ Fintype.card (Fin 4) = E at hmoment ⊢
  norm_num
  nlinarith [mul_le_mul_of_nonneg_left hmoment hs0]

end CslibFrontierTests.OddCircuit
