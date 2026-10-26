/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Algebra/Order/BigOperators/Expect.lean`)

public import Complexity.Init
public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Finset.Density
public import Mathlib.Data.Fintype.Pi
import Complexity.Foundations.Data.Finset.Expect
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# Finding a good sample

Two estimates for finding, by uniform sampling, a point of a finite type at which a function is
large.

*Reverse averaging.* If `f ≤ 1` has average `μ`, then `f ≤ θ + (1 - θ) 𝟙[θ ≤ f]` pointwise, so
`μ ≤ θ + (1 - θ) dens {θ ≤ f}` (`Fintype.expect_le_add_mul_dens_filter`): `f` is at least `θ` on
a set of density at least `(μ - θ) / (1 - θ)` when `θ < 1`
(`Fintype.expect_sub_div_le_dens_filter`), and at least `μ - θ` when `0 ≤ θ`
(`Fintype.expect_sub_le_dens_filter`). This is the reverse of Markov's inequality
`Fintype.mul_dens_filter_le_expect`, for functions bounded above instead of below.

*Repeated trials.* `k` independent uniform samples all miss a set of density `p` with probability
`(1 - p) ^ k` (`Fintype.dens_filter_forall_apply_notMem`), so some sample lands in it with
probability `1 - (1 - p) ^ k` (`Fintype.dens_filter_exists_apply_mem`). This is at least `1 / 2`
once `k p ≥ 1` (`Fintype.half_le_dens_filter_exists_apply_mem`): by Bernoulli's inequality
`(1 + p) ^ k ≥ 1 + k p ≥ 2`, while `(1 - p) ^ k (1 + p) ^ k = (1 - p ^ 2) ^ k ≤ 1`
(`one_sub_pow_le_half`).

## Main results

* `Fintype.expect_le_add_mul_dens_filter`, `Fintype.expect_sub_div_le_dens_filter`,
  `Fintype.expect_sub_le_dens_filter`: reverse averaging.
* `Fintype.dens_filter_forall_apply_notMem`, `Fintype.dens_filter_exists_apply_mem`,
  `Fintype.cast_dens_filter_exists_apply_mem`: the exact law of repeated trials.
* `Fintype.one_sub_pow_le_dens_filter_exists_apply_mem`,
  `Fintype.half_le_dens_filter_exists_apply_mem`: lower bounds for repeated trials.
* `one_sub_pow_le_half`: `k` trials of success probability `p ≥ 1 / k` all fail with probability
  at most `1 / 2`.
-/

@[expose] public section

open Finset
open scoped BigOperators

/-- If `0 ≤ p ≤ 1` and `k p ≥ 1`, then `(1 - p) ^ k ≤ 1 / 2`: `k` independent trials, each
succeeding with probability `p`, all fail with probability at most `1 / 2`. -/
theorem one_sub_pow_le_half {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    {p : 𝕜} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) {k : ℕ} (hk : 1 ≤ k * p) : (1 - p) ^ k ≤ 1 / 2 := by
  have hbern : 2 ≤ (1 + p) ^ k := by
    linarith [one_add_mul_le_pow (show (-2 : 𝕜) ≤ p by linarith) k]
  have hprod : (1 - p) ^ k * (1 + p) ^ k ≤ 1 := by
    rw [← mul_pow]
    exact pow_le_one₀ (by nlinarith) (by nlinarith)
  have hnonneg : 0 ≤ (1 - p) ^ k := pow_nonneg (by linarith) k
  nlinarith

namespace Fintype

variable {ι α 𝕜 : Type*} [Fintype ι] [Fintype α]

/-! ### Reverse averaging -/

section ReverseAveraging

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [Nonempty α] {f : α → 𝕜}

/-- **Reverse averaging.** A function bounded above by `1` averages to at most `θ` plus `1 - θ`
times the density of the set where it is at least `θ`. -/
theorem expect_le_add_mul_dens_filter (hf : ∀ a, f a ≤ 1) (θ : 𝕜)
    [DecidablePred fun a => θ ≤ f a] :
    𝔼 a, f a ≤ θ + (1 - θ) * (dens {a | θ ≤ f a} : 𝕜) := by
  have h (a : α) : f a ≤ θ + (1 - θ) * (if θ ≤ f a then 1 else 0) := by
    split_ifs with ha
    · linarith [hf a]
    · linarith [not_le.mp ha]
  calc 𝔼 a, f a ≤ 𝔼 a, (θ + (1 - θ) * (if θ ≤ f a then 1 else 0 : 𝕜)) :=
        expect_le_expect fun a _ => h a
    _ = _ := by rw [expect_add_distrib, expect_const, ← mul_expect, expect_boole]

/-- **Reverse averaging.** If `θ < 1`, a function bounded above by `1` with average `μ` is at
least `θ` on a set of density at least `(μ - θ) / (1 - θ)`. -/
theorem expect_sub_div_le_dens_filter (hf : ∀ a, f a ≤ 1) {θ : 𝕜}
    [DecidablePred fun a => θ ≤ f a] (hθ : θ < 1) :
    (𝔼 a, f a - θ) / (1 - θ) ≤ dens {a | θ ≤ f a} := by
  rw [div_le_iff₀ (sub_pos.mpr hθ)]
  linarith [expect_le_add_mul_dens_filter hf θ]

/-- **Reverse averaging.** If `0 ≤ θ`, a function bounded above by `1` with average `μ` is at least
`θ` on a set of density at least `μ - θ`. -/
theorem expect_sub_le_dens_filter (hf : ∀ a, f a ≤ 1) {θ : 𝕜} [DecidablePred fun a => θ ≤ f a]
    (hθ : 0 ≤ θ) : 𝔼 a, f a - θ ≤ dens {a | θ ≤ f a} := by
  have hd : (0 : 𝕜) ≤ dens {a | θ ≤ f a} := NNRat.cast_nonneg _
  nlinarith [expect_le_add_mul_dens_filter hf θ]

end ReverseAveraging

/-! ### Repeated trials -/

section RepeatedTrials

variable [DecidableEq ι]

/-- Independent uniform coordinates all belong to `t` with probability `dens t ^ card ι`. -/
theorem dens_piFinset_const (t : Finset α) :
    dens (piFinset fun _ : ι => t) = dens t ^ card ι := by
  rw [dens_eq_card_div_card, card_piFinset, prod_const, card_univ, card_fun,
    dens_eq_card_div_card]
  push_cast
  rw [div_pow]

private theorem dens_add_dens_compl {β : Type*} [Fintype β] [DecidableEq β] [Nonempty β]
    (t : Finset β) : dens t + dens tᶜ = 1 := by
  rw [dens_eq_card_div_card, dens_eq_card_div_card, ← add_div, ← Nat.cast_add,
    card_add_card_compl, div_self (Nat.cast_ne_zero.mpr card_ne_zero)]

private theorem dens_compl {β : Type*} [Fintype β] [DecidableEq β] [Nonempty β]
    (t : Finset β) : dens tᶜ = 1 - dens t :=
  eq_tsub_of_add_eq ((add_comm _ _).trans (dens_add_dens_compl t))

variable (s : Finset α)

/-- **Repeated trials.** `card ι` independent uniform samples all miss `s` with probability
`dens sᶜ ^ card ι`. -/
theorem dens_filter_forall_apply_notMem [DecidableEq α]
    [DecidablePred fun ω : ι → α => ∀ j, ω j ∉ s] :
    dens {ω : ι → α | ∀ j, ω j ∉ s} = dens sᶜ ^ card ι := by
  have h : ({ω : ι → α | ∀ j, ω j ∉ s} : Finset (ι → α)) = piFinset fun _ => sᶜ := by
    ext ω
    simp [mem_piFinset]
  rw [h, dens_piFinset_const]

private theorem filter_exists_apply_mem_eq [DecidableEq α]
    [DecidablePred fun ω : ι → α => ∃ j, ω j ∈ s] :
    ({ω : ι → α | ∃ j, ω j ∈ s} : Finset (ι → α)) = (piFinset fun _ => sᶜ)ᶜ := by
  ext ω
  simp [mem_piFinset]

variable [Nonempty α] [DecidablePred fun ω : ι → α => ∃ j, ω j ∈ s]

/-- **Repeated trials.** Some of `card ι` independent uniform samples lands in `s` with
probability `1 - (1 - dens s) ^ card ι`. -/
theorem dens_filter_exists_apply_mem :
    dens {ω : ι → α | ∃ j, ω j ∈ s} = 1 - (1 - dens s) ^ card ι := by
  classical
  rw [filter_exists_apply_mem_eq, dens_compl, dens_piFinset_const, dens_compl]

/-- **Repeated trials**, in a field: some of `card ι` independent uniform samples lands in `s`
with probability `1 - (1 - dens s) ^ card ι`. -/
theorem cast_dens_filter_exists_apply_mem [Field 𝕜] [CharZero 𝕜] :
    (dens {ω : ι → α | ∃ j, ω j ∈ s} : 𝕜) = 1 - (1 - (dens s : 𝕜)) ^ card ι := by
  classical
  have h₁ := congrArg (NNRat.cast : ℚ≥0 → 𝕜) (dens_add_dens_compl s)
  have h₂ := congrArg (NNRat.cast : ℚ≥0 → 𝕜)
    (dens_add_dens_compl (piFinset fun _ : ι => sᶜ))
  rw [NNRat.cast_add, NNRat.cast_one] at h₁
  rw [NNRat.cast_add, NNRat.cast_one, dens_piFinset_const, NNRat.cast_pow,
    show (dens sᶜ : 𝕜) = 1 - dens s by linear_combination h₁] at h₂
  rw [filter_exists_apply_mem_eq]
  linear_combination h₂

variable {s}

/-- **Repeated trials.** If a uniform sample lands in `s` with probability at least `q`, some of
`card ι` independent uniform samples lands in `s` with probability at least
`1 - (1 - q) ^ card ι`. -/
theorem one_sub_pow_le_dens_filter_exists_apply_mem [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] {q : 𝕜} (hq : q ≤ dens s) :
    1 - (1 - q) ^ card ι ≤ dens {ω : ι → α | ∃ j, ω j ∈ s} := by
  rw [cast_dens_filter_exists_apply_mem]
  have h₀ : (0 : 𝕜) ≤ 1 - dens s := sub_nonneg.mpr (mod_cast dens_le_one)
  exact sub_le_sub_left (pow_le_pow_left₀ h₀ (sub_le_sub_left hq 1) _) 1

/-- **Repeated trials.** If a uniform sample lands in `s` with probability at least `q ≥ 0` and
`card ι * q ≥ 1`, some of `card ι` independent uniform samples lands in `s` with probability at
least `1 / 2`. -/
theorem half_le_dens_filter_exists_apply_mem [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    {q : 𝕜} (hq₀ : 0 ≤ q) (hq : q ≤ dens s) (hι : 1 ≤ card ι * q) :
    1 / 2 ≤ (dens {ω : ι → α | ∃ j, ω j ∈ s} : 𝕜) := by
  have hq₁ : q ≤ 1 := hq.trans (mod_cast dens_le_one)
  linarith [one_sub_pow_le_half hq₀ hq₁ hι,
    one_sub_pow_le_dens_filter_exists_apply_mem (ι := ι) hq]

end RepeatedTrials

end Fintype
