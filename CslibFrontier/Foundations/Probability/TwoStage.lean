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
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Two-stage sampling in finite products

Draw `a` uniformly from a finite type `α` and then `b` uniformly from `β`. Suppose a `ρ₁`
fraction of the `a` are good, and for each good `a` a `ρ₂` fraction of the `b` satisfy `q a b`.
Then a `ρ₁ ρ₂` fraction of the pairs satisfy `q`. The event on the second coordinate may depend
on the first, unlike in `Cslib.Probability.dens_filter_fst_and_snd`, where the two events are
independent.

## Main results

* `Cslib.Probability.mul_le_dens_filter_prod`: the lower bound `ρ₁ ρ₂` on the density of pairs.
-/

public section

namespace Cslib.Probability

open Finset

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
  have hcount : (#{ab : α × β | q ab.1 ab.2} : ℝ) = ∑ a, (#{b | q a b} : ℝ) := by
    rw [← Nat.cast_sum]
    congr 1
    rw [← univ_product_univ, card_filter, sum_product]
    simp only [card_filter]
  have hsum : (#{a | good a} : ℝ) * (ρ₂ * Fintype.card β) ≤ ∑ a, (#{b | q a b} : ℝ) := by
    rw [← nsmul_eq_mul, ← sum_const, ← sum_filter_add_sum_filter_not univ good]
    refine le_add_of_le_of_nonneg (sum_le_sum fun a ha => ?_) (sum_nonneg fun _ _ => by positivity)
    have := h₂ a (mem_filter.1 ha).2
    rwa [le_div_iff₀ hβ] at this
  rw [hcount, le_div_iff₀ (by positivity)]
  rw [le_div_iff₀ hα] at h₁
  calc ρ₁ * ρ₂ * (Fintype.card α * Fintype.card β)
        = ρ₁ * Fintype.card α * ρ₂ * Fintype.card β := by ring
    _ ≤ #{a | good a} * ρ₂ * Fintype.card β := by gcongr
    _ ≤ _ := by linarith [hsum]

end Cslib.Probability
