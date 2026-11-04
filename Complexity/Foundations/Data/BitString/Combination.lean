/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.Nat.Choose.Basic

/-!
# Unranking combinations

The weight-`k` indicators of length `m`, ordered lexicographically with `false` first, are
numbered `0, …, C(m, k) - 1`. `Cslib.BitString.unrankCombination m k r` is the indicator of rank
`r`: its first bit is `false` exactly when `r` is below the `C(m - 1, k)` indicators that start
with `false`.

## Main definitions

* `Cslib.BitString.unrankCombination`: the weight-`k` indicator of length `m` of a given rank.

## Main results

* `Cslib.BitString.length_unrankCombination`: the indicator has length `m`.
* `Cslib.BitString.count_true_unrankCombination`: a rank below `C(m, k)` gives weight `k`.
* `Cslib.BitString.unrankCombination_injective`: distinct ranks below `C(m, k)` give distinct
  indicators.
-/

@[expose] public section

namespace Cslib.BitString

/-- **The combination of rank `r`** among the weight-`k` indicators of length `m`, in the
lexicographic order with `false` first. A rank `r < C(m, k)` gives an indicator of weight `k`
(`count_true_unrankCombination`), and distinct ranks give distinct indicators
(`unrankCombination_injective`). -/
def unrankCombination : ℕ → ℕ → ℕ → List Bool
  | 0, _, _ => []
  | m + 1, k, r =>
    if r < m.choose k then false :: unrankCombination m k r
    else true :: unrankCombination m (k - 1) (r - m.choose k)

@[simp] theorem length_unrankCombination (m k r : ℕ) : (unrankCombination m k r).length = m := by
  induction m generalizing k r with
  | zero => rfl
  | succ m ih => simp only [unrankCombination]; split_ifs <;> simp [ih]

/-- A rank below `C(m, k)` unranks to an indicator of weight `k`. -/
theorem count_true_unrankCombination {m k r : ℕ} (hr : r < m.choose k) :
    (unrankCombination m k r).count true = k := by
  induction m generalizing k r with
  | zero => cases k with | zero => rfl | succ k => simp at hr
  | succ m ih =>
    simp only [unrankCombination]; split_ifs with hlt
    · simp [ih hlt]
    · cases k with
      | zero => simp only [Nat.choose_zero_right] at hr hlt; omega
      | succ k =>
        rw [Nat.choose_succ_succ, Nat.succ_eq_add_one] at hr
        simp [ih (by omega : r - m.choose (k + 1) < m.choose k)]

/-- Distinct ranks below `C(m, k)` unrank to distinct indicators. -/
theorem unrankCombination_injective {m k r₁ r₂ : ℕ}
    (hr₁ : r₁ < m.choose k) (hr₂ : r₂ < m.choose k)
    (heq : unrankCombination m k r₁ = unrankCombination m k r₂) : r₁ = r₂ := by
  induction m generalizing k r₁ r₂ with
  | zero =>
    cases k with
    | zero => simp only [Nat.choose_zero_right, Nat.lt_one_iff] at hr₁ hr₂; omega
    | succ k => simp at hr₁
  | succ m ih =>
    simp only [unrankCombination] at heq; split_ifs at heq with h₁ h₂ h₂
    · simp only [List.cons.injEq, true_and] at heq; exact ih h₁ h₂ heq
    · simp at heq
    · simp at heq
    · simp only [List.cons.injEq, true_and] at heq
      cases k with
      | zero => simp only [Nat.choose_zero_right] at hr₁ h₁; omega
      | succ k =>
        rw [Nat.choose_succ_succ, Nat.succ_eq_add_one] at hr₁ hr₂
        have := ih (by omega : r₁ - m.choose (k + 1) < m.choose k) (by omega) heq; omega

end Cslib.BitString
