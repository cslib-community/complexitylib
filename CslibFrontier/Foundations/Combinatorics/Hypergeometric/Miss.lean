/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Analysis.SpecialFunctions.Exp
import CslibFrontier.Foundations.Data.Nat.Choose
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Random subsets rarely miss a fixed set

For a set `U` of `u` elements of an `n`-element set `s`, the `ℓ`-subsets of `s` disjoint from `U`
are the `ℓ`-subsets of `s \ U` (`card_filter_disjoint_powersetCard`), so a uniformly random
`ℓ`-subset misses `U` with probability `C(n - u, ℓ) / C(n, ℓ)`. The library's
`Nat.choose_mul_pow_le` bounds this by `(1 - u / n) ^ ℓ`, and hence by `exp (-u ℓ / n)`
(`choose_sub_le_choose_mul_exp`). This is the zero tail of the hypergeometric distribution of
`#(U ∩ J)` studied in `CslibFrontier.Foundations.Combinatorics.Hypergeometric`.

## Main results

* `Cslib.card_filter_disjoint_powersetCard`: the `ℓ`-subsets of `s` that miss `U`.
* `Cslib.choose_sub_le_choose_mul_exp`: `C(n - u, ℓ) ≤ C(n, ℓ) exp (-u ℓ / n)`.
* `Cslib.card_filter_disjoint_powersetCard_le`: few `ℓ`-subsets of `s` miss `U`.
-/

public section

namespace Cslib

open Finset

/-- **Missing a set, exponential form**: `C(n - u, ℓ) ≤ C(n, ℓ) exp (-u ℓ / n)`, for `u ≤ n`. -/
theorem choose_sub_le_choose_mul_exp {n u : ℕ} (hu : u ≤ n) (ℓ : ℕ) :
    ((n - u).choose ℓ : ℝ) ≤ n.choose ℓ * Real.exp (-(u * ℓ / n)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · obtain rfl : u = 0 := Nat.le_zero.1 hu
    simp
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hcast : ((n - u : ℕ) : ℝ) = n - u := by push_cast [hu]; ring
  have h : ((n - u).choose ℓ : ℝ) * (n : ℝ) ^ ℓ ≤ n.choose ℓ * ((n : ℝ) - u) ^ ℓ := by
    exact_mod_cast (hcast ▸ (by exact_mod_cast Nat.choose_mul_pow_le (Nat.sub_le n u) ℓ :
      ((n - u).choose ℓ : ℝ) * ((n : ℕ) : ℝ) ^ ℓ ≤ n.choose ℓ * ((n - u : ℕ) : ℝ) ^ ℓ))
  have hratio : ((n : ℝ) - u) ^ ℓ = (n : ℝ) ^ ℓ * (1 - u / n) ^ ℓ := by
    rw [← mul_pow]
    congr 1
    field_simp
  have hbase : 0 ≤ 1 - (u : ℝ) / n := by
    rw [sub_nonneg, div_le_one hnR]
    exact_mod_cast hu
  have hexp : (1 - (u : ℝ) / n) ^ ℓ ≤ Real.exp (-(u * ℓ / n)) := by
    calc (1 - (u : ℝ) / n) ^ ℓ ≤ Real.exp (-(u / n)) ^ ℓ :=
          pow_le_pow_left₀ hbase (Real.one_sub_le_exp_neg _) ℓ
      _ = Real.exp (-(u * ℓ / n)) := by
          rw [← Real.exp_nat_mul]
          congr 1
          ring
  rw [hratio] at h
  have hpow : (0 : ℝ) < (n : ℝ) ^ ℓ := by positivity
  have h' : ((n - u).choose ℓ : ℝ) ≤ n.choose ℓ * (1 - u / n) ^ ℓ := by
    nlinarith
  exact h'.trans (mul_le_mul_of_nonneg_left hexp (Nat.cast_nonneg _))

variable {α : Type*} [DecidableEq α]

/-- The `ℓ`-subsets of `s` that miss `U ⊆ s` are the `ℓ`-subsets of `s \ U`. -/
theorem card_filter_disjoint_powersetCard {s U : Finset α} (hU : U ⊆ s) (ℓ : ℕ) :
    #{J ∈ s.powersetCard ℓ | Disjoint U J} = (#s - #U).choose ℓ := by
  rw [← card_sdiff_of_subset hU, ← card_powersetCard]
  congr 1
  ext J
  simp only [mem_filter, mem_powersetCard, subset_sdiff]
  constructor
  · rintro ⟨⟨hJ, hc⟩, hd⟩
    exact ⟨⟨hJ, hd.symm⟩, hc⟩
  · rintro ⟨⟨hJ, hd⟩, hc⟩
    exact ⟨⟨hJ, hc⟩, hd.symm⟩

/-- **Few subsets miss a fixed set**: at most a `exp (-#U ℓ / #s)` fraction of the `ℓ`-subsets of
`s` are disjoint from `U ⊆ s`. -/
theorem card_filter_disjoint_powersetCard_le {s U : Finset α} (hU : U ⊆ s) (ℓ : ℕ) :
    (#{J ∈ s.powersetCard ℓ | Disjoint U J} : ℝ) ≤
      #(s.powersetCard ℓ) * Real.exp (-(#U * ℓ / #s)) := by
  rw [card_filter_disjoint_powersetCard hU, card_powersetCard]
  exact choose_sub_le_choose_mul_exp (card_le_card hU) ℓ

end Cslib
