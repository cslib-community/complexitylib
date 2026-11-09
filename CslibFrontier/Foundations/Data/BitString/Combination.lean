/-
Copyright (c) 2026 Anton Kovsharov, Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov, Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.BitString.Support
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Logic.Equiv.Defs

/-!
# Ranking and unranking combinations

The weight-`k` indicators of length `m`, ordered lexicographically with `false` first, are
numbered `0, …, C(m, k) - 1`. `Cslib.BitString.unrankCombination m k r` is the indicator of rank
`r`: its first bit is `false` exactly when `r` is below the `C(m - 1, k)` indicators that start
with `false`. Conversely, `Cslib.BitString.rankCombination bs` recovers the lexicographic rank of
`bs`, and `Cslib.BitString.subsetEquiv m k` packages this ranking/unranking pair with
`Cslib.BitString.supportOfList` into a computable bijection between `k`-element subsets of `Fin m`
and `Fin (m.choose k)`.

## Main definitions

* `Cslib.BitString.unrankCombination`: the weight-`k` indicator of length `m` of a given rank.
* `Cslib.BitString.rankCombination`: the lexicographic rank of a Boolean indicator list.
* `Cslib.BitString.subsetEquiv`: computable bijection `{ S : Finset (Fin m) // S.card = k } ≃
  Fin (m.choose k)`.

## Main results

* `Cslib.BitString.length_unrankCombination`: the indicator has length `m`.
* `Cslib.BitString.count_true_unrankCombination`: a rank below `C(m, k)` gives weight `k`.
* `Cslib.BitString.unrankCombination_injective`: distinct ranks below `C(m, k)` give distinct
  indicators.
* `Cslib.BitString.rankCombination_lt_choose`, `Cslib.BitString.unrankCombination_rankCombination`,
  `Cslib.BitString.rankCombination_unrankCombination`: range and round-trip identities for
  `rankCombination` and `unrankCombination`.
-/

public section

namespace Cslib.BitString

/-- **The combination of rank `r`** among the weight-`k` indicators of length `m`, in the
lexicographic order with `false` first. A rank `r < C(m, k)` gives an indicator of weight `k`
(`count_true_unrankCombination`), and distinct ranks give distinct indicators
(`unrankCombination_injective`). -/
@[expose]
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

/-- **The lexicographic rank of a Boolean indicator `bs`** among all indicators of length
`bs.length` and weight `bs.count true` (`false` before `true`), inverting `unrankCombination`. -/
@[expose]
def rankCombination : List Bool → ℕ
  | [] => 0
  | false :: xs => rankCombination xs
  | true :: xs => xs.length.choose (xs.count true + 1) + rankCombination xs

/-- The rank of `bs` is strictly below `C(bs.length, bs.count true)`. -/
theorem rankCombination_lt_choose :
    ∀ bs : List Bool, rankCombination bs < bs.length.choose (bs.count true)
  | [] => by simp [rankCombination]
  | false :: xs =>
    lt_of_lt_of_le (rankCombination_lt_choose xs) (Nat.choose_le_succ xs.length (xs.count true))
  | true :: xs => by
    have ih := rankCombination_lt_choose xs
    simp only [rankCombination, List.length_cons, List.count_cons_self]
    rw [Nat.choose_succ_succ, Nat.succ_eq_add_one]
    omega

/-- Unranking the rank of `bs` at `(bs.length, bs.count true)` recovers `bs`. -/
@[simp]
theorem unrankCombination_rankCombination :
    ∀ bs : List Bool,
      unrankCombination bs.length (bs.count true) (rankCombination bs) = bs
  | [] => rfl
  | false :: xs => by
    have hlt := rankCombination_lt_choose xs
    simp [rankCombination, unrankCombination, hlt, unrankCombination_rankCombination xs]
  | true :: xs => by
    have hnot : ¬ (xs.length.choose (xs.count true + 1) + rankCombination xs <
        xs.length.choose (xs.count true + 1)) := by omega
    simp [rankCombination, unrankCombination, hnot, unrankCombination_rankCombination xs]

/-- Ranking `unrankCombination m k r` for `r < C(m, k)` recovers `r`. -/
@[simp]
theorem rankCombination_unrankCombination {m k r : ℕ} (hr : r < m.choose k) :
    rankCombination (unrankCombination m k r) = r := by
  set bs := unrankCombination m k r
  have hlen : bs.length = m := length_unrankCombination m k r
  have hcnt : bs.count true = k := count_true_unrankCombination hr
  have hr' : rankCombination bs < m.choose k := by
    have hlt := rankCombination_lt_choose bs
    rwa [hlen, hcnt] at hlt
  refine unrankCombination_injective hr' hr ?_
  have hunr := unrankCombination_rankCombination bs
  rwa [hlen, hcnt] at hunr

/-- The indicator list of a `k`-element subset of `Fin m` has `k` entries `true`. -/
private theorem count_true_ofFn_decide_mem {m k : ℕ} {S : Finset (Fin m)} (hS : S.card = k) :
    (List.ofFn fun u : Fin m => decide (u ∈ S)).count true = k := by
  rw [← card_supportOfList_of_length List.length_ofFn, supportOfList_ofFn_decide, hS]

/-- Computable bijection between `k`-element subsets of `Fin m` and `Fin (m.choose k)`, obtained by
composing `rankCombination` / `unrankCombination` with `supportOfList`. -/
def subsetEquiv (m k : ℕ) : { S : Finset (Fin m) // S.card = k } ≃ Fin (m.choose k) where
  toFun S := ⟨rankCombination (List.ofFn fun u : Fin m => decide (u ∈ S.1)), by
    simpa only [List.length_ofFn, count_true_ofFn_decide_mem S.2] using
      rankCombination_lt_choose (List.ofFn fun u : Fin m => decide (u ∈ S.1))⟩
  invFun r := ⟨supportOfList m (unrankCombination m k r.val), by
    rw [card_supportOfList_of_length (length_unrankCombination m k r.val)]
    exact count_true_unrankCombination r.isLt⟩
  left_inv S := Subtype.ext <| by
    dsimp only
    have hunr := unrankCombination_rankCombination (List.ofFn fun u : Fin m => decide (u ∈ S.1))
    rw [List.length_ofFn, count_true_ofFn_decide_mem S.2] at hunr
    rw [hunr, supportOfList_ofFn_decide]
  right_inv r := Fin.ext <| by
    dsimp only
    rw [ofFn_decide_mem_supportOfList (length_unrankCombination m k r.val)]
    exact rankCombination_unrankCombination r.isLt

@[simp]
theorem val_subsetEquiv {m k : ℕ} (S : { S : Finset (Fin m) // S.card = k }) :
    (subsetEquiv m k S).val = rankCombination (List.ofFn fun u : Fin m => decide (u ∈ S.1)) := by
  simp [subsetEquiv]

@[simp]
theorem coe_subsetEquiv_symm {m k : ℕ} (r : Fin (m.choose k)) :
    ((subsetEquiv m k).symm r).1 = supportOfList m (unrankCombination m k r.val) := by
  simp [subsetEquiv]

end Cslib.BitString
