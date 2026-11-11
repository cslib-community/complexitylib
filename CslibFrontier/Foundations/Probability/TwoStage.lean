/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Density
public import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import CslibFrontier.Foundations.Data.Finset.Markov
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Two-stage sampling in finite products

Draw `a` uniformly from a finite type `α` and then `b` uniformly from `β`. Suppose a `ρ₁`
fraction of the `a` are good, and for each good `a` a `ρ₂` fraction of the `b` satisfy `q a b`.
Then a `ρ₁ ρ₂` fraction of the pairs satisfy `q`. The event on the second coordinate may depend
on the first, unlike in `Cslib.Probability.dens_filter_fst_and_snd`, where the two events are
independent.

The count form `Cslib.Probability.mul_le_card_filter_product` works over finsets `s ×ˢ t`, so
that the first stage may range over a subset such as `powersetCard`; the density form over a
whole product type is derived from it.

## Main results

* `Cslib.Probability.mul_le_card_filter_product`: if at least `ρ₁` elements of `s` are good and
  each good `a` has at least `ρ₂` partners `b ∈ t` with `q a b`, then at least `ρ₁ ρ₂` pairs of
  `s ×ˢ t` satisfy `q`.
* `Cslib.Probability.mul_le_dens_filter_prod`: the lower bound `ρ₁ ρ₂` on the density of pairs.
-/

public section

namespace Cslib.Probability

open Finset

/-- **Two-stage counting.** If at least `ρ₁` elements of `s` are good, and each good `a` has at
least `ρ₂` partners `b ∈ t` with `q a b`, then at least `ρ₁ ρ₂` pairs of `s ×ˢ t` satisfy `q`. -/
theorem mul_le_card_filter_product {α β : Type*} (s : Finset α) (t : Finset β) (good : α → Prop)
    [DecidablePred good] (q : α → β → Prop) [∀ a, DecidablePred (q a)] {ρ₁ ρ₂ : ℝ}
    (hρ₂ : 0 ≤ ρ₂) (h₁ : ρ₁ ≤ #{a ∈ s | good a})
    (h₂ : ∀ a ∈ s, good a → ρ₂ ≤ #{b ∈ t | q a b}) :
    ρ₁ * ρ₂ ≤ #{ab ∈ s ×ˢ t | q ab.1 ab.2} := by
  have hcount : (#{ab ∈ s ×ˢ t | q ab.1 ab.2} : ℝ) = ∑ a ∈ s, (#{b ∈ t | q a b} : ℝ) := by
    rw [← Nat.cast_sum, card_filter, sum_product]
    simp only [card_filter]
  rw [hcount]
  exact (mul_le_mul_of_nonneg_right h₁ hρ₂).trans
    (card_filter_mul_le_sum s good _ (fun _ _ => by positivity) h₂)

/-- **Two-stage sampling.** If a `ρ₁` fraction of the `a` are good, and for each good `a` a `ρ₂`
fraction of the `b` satisfy `q a b`, then a `ρ₁ ρ₂` fraction of the pairs satisfy `q`. -/
theorem mul_le_dens_filter_prod {α β : Type*} [Fintype α] [Fintype β] (good : α → Prop)
    [DecidablePred good] (q : α → β → Prop) [∀ a, DecidablePred (q a)] {ρ₁ ρ₂ : ℝ}
    (hρ₂ : 0 ≤ ρ₂) (h₁ : ρ₁ ≤ (dens {a | good a} : ℝ))
    (h₂ : ∀ a, good a → ρ₂ ≤ (dens {b | q a b} : ℝ)) :
    ρ₁ * ρ₂ ≤ (dens {ab : α × β | q ab.1 ab.2} : ℝ) := by
  have hpair : (0 : ℝ) ≤ dens {ab : α × β | q ab.1 ab.2} := by positivity
  by_cases hex : ∃ a, good a
  swap
  · push Not at hex
    have h0 : (dens {a | good a} : ℝ) = 0 := by simp [hex]
    nlinarith
  obtain ⟨a₀, ha₀⟩ := hex
  rcases hρ₂.eq_or_lt with rfl | hρ₂'
  · simpa using hpair
  have : Nonempty α := ⟨a₀⟩
  have : Nonempty β := by
    by_contra hβ
    rw [not_nonempty_iff] at hβ
    have := h₂ a₀ ha₀
    simp only [univ_eq_empty, filter_empty, dens_empty, NNRat.cast_zero] at this
    linarith
  simp only [nnratCast_dens, Fintype.card_prod, Nat.cast_mul] at h₁ h₂ ⊢
  have hα : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hβ : (0 : ℝ) < Fintype.card β := by exact_mod_cast Fintype.card_pos
  rw [le_div_iff₀ hα] at h₁
  have := mul_le_card_filter_product univ univ good q (by positivity) h₁
    fun a _ ha => (le_div_iff₀ hβ).1 (h₂ a ha)
  rw [univ_product_univ] at this
  rw [le_div_iff₀ (by positivity)]
  linarith

end Cslib.Probability
