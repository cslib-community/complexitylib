/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, new `Mathlib/Combinatorics/Tournament.lean`)

public import Complexity.Init
public import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Dominating sets of tournaments

Let `R` be a total relation on a finite set `T`: for all `x, y ∈ T`, `R x y` or `R y x`, as in a
tournament; read `R x y` as "`y` covers `x`". Counting the pairs, some `y ∈ T` covers at least half
of `T` (`Finset.exists_card_le_two_mul_card_filter_rel`). Taking such a `y` and recursing on the
elements it does not cover, fewer than `2 ^ k` elements are dominated by at most `k` of them: every
element is covered by one of them (`Finset.exists_dominating_subset_of_card_lt_two_pow`). This is
the combinatorial core of Ko's theorem that P-selective sets have polynomial advice: the at most
`2 ^ n` members of length `n` are dominated by at most `n + 1` of them [Ko1983].

## Main results

* `Finset.exists_card_le_two_mul_card_filter_rel`: some element covers at least half of `T`.
* `Finset.exists_dominating_subset_of_card_lt_two_pow`: a set of fewer than `2 ^ k` elements has
  a dominating subset of at most `k` elements.

## References

* [K.-I. Ko, *On self-reducibility and weak P-selectivity*][Ko1983]
-/

public section

namespace Finset

variable {α : Type*}

/-- **A good vertex of a tournament.** If `R` is total on a nonempty finite set `T`, some `y ∈ T`
covers at least half of `T`: `R x y` for at least `|T| / 2` elements `x ∈ T`. -/
theorem exists_card_le_two_mul_card_filter_rel (T : Finset α) (R : α → α → Prop)
    [DecidableRel R] (htot : ∀ x ∈ T, ∀ y ∈ T, R x y ∨ R y x) (hT : T.Nonempty) :
    ∃ y ∈ T, T.card ≤ 2 * (T.filter fun x => R x y).card := by
  classical
  by_contra hne
  push Not at hne
  have hsum : ∑ y ∈ T, 2 * (T.filter fun x => R x y).card < ∑ y ∈ T, T.card :=
    sum_lt_sum_of_nonempty hT hne
  have hswap : ∑ y ∈ T, (T.filter fun x => R x y).card =
      ∑ y ∈ T, (T.filter fun x => R y x).card := by
    simp only [card_filter]
    exact sum_comm
  have hpair : ∀ y ∈ T,
      T.card ≤ (T.filter fun x => R x y).card + (T.filter fun x => R y x).card := fun y hy => by
    rw [← card_union_add_card_inter]
    refine le_trans (card_le_card fun x hx => ?_) (Nat.le_add_right _ _)
    rcases htot x hx y hy with h | h
    · exact mem_union_left _ (mem_filter.2 ⟨hx, h⟩)
    · exact mem_union_right _ (mem_filter.2 ⟨hx, h⟩)
  have hle := sum_le_sum hpair
  rw [sum_add_distrib, ← hswap] at hle
  rw [← mul_sum] at hsum
  simp only [sum_const, smul_eq_mul] at hsum hle
  omega

/-- **Dominating sets of tournaments.** If `R` is total on a finite set `T` of fewer than `2 ^ k`
elements, some `S ⊆ T` of at most `k` elements dominates `T`: every `x ∈ T` is covered by some
`y ∈ S`, i.e. `R x y`. -/
theorem exists_dominating_subset_of_card_lt_two_pow (R : α → α → Prop) :
    ∀ (k : ℕ) (T : Finset α), (∀ x ∈ T, ∀ y ∈ T, R x y ∨ R y x) → T.card < 2 ^ k →
      ∃ S ⊆ T, S.card ≤ k ∧ ∀ x ∈ T, ∃ y ∈ S, R x y
  | 0, T, _, hT => ⟨∅, empty_subset _, le_rfl, fun x hx => by
      rw [pow_zero, Nat.lt_one_iff, card_eq_zero] at hT
      exact absurd hx (hT ▸ notMem_empty x)⟩
  | k + 1, T, htot, hT => by
    classical
    rcases T.eq_empty_or_nonempty with rfl | hne
    · exact ⟨∅, le_rfl, Nat.zero_le _, fun x hx => absurd hx (notMem_empty x)⟩
    obtain ⟨y, hy, hcnt⟩ := exists_card_le_two_mul_card_filter_rel T R htot hne
    have hsplit := card_filter_add_card_filter_not (s := T) (fun x => R x y)
    have hlt : (T.filter fun x => ¬R x y).card < 2 ^ k := by
      rw [pow_succ] at hT
      omega
    obtain ⟨S', hS'T, hS'card, hS'⟩ := exists_dominating_subset_of_card_lt_two_pow R k _
      (fun x hx z hz => htot x (mem_filter.1 hx).1 z (mem_filter.1 hz).1) hlt
    refine ⟨insert y S', insert_subset hy (hS'T.trans (filter_subset _ _)),
      (card_insert_le _ _).trans (by omega), fun x hx => ?_⟩
    by_cases hxy : R x y
    · exact ⟨y, mem_insert_self _ _, hxy⟩
    · obtain ⟨z, hz, hxz⟩ := hS' x (mem_filter.2 ⟨hx, hxy⟩)
      exact ⟨z, mem_insert_of_mem hz, hxz⟩

end Finset
