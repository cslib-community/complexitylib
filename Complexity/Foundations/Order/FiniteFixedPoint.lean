/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, finite iteration bounds for `Mathlib/Order/FixedPoints.lean`)

public import Complexity.Init
public import Mathlib.Order.FixedPoints
public import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Card
import Mathlib.Order.Iterate

/-!
# Least fixed points on finite powersets

A monotone map on subsets of a finite type reaches its least fixed point by iterating from the
empty set at most the cardinality of the underlying type times. This is the number of elements,
not the cardinality of the powerset. No inflationarity assumption is needed: the iteration from
the empty set is increasing by monotonicity.

## Main results

* `OrderHom.iterate_bot_le_lfp`: every iterate from the bottom lies below the least fixed point.
* `OrderHom.iterate_card_bot_eq_lfp`: on `Set α`, the iterate at `Fintype.card α` is the least
  fixed point, including when `α` is empty.
* `OrderHom.iterate_bot_eq_lfp_of_card_le`: every subsequent iterate has the same value.
-/

public section

namespace OrderHom

variable {α β : Type*}

/-- Every finite iterate from the bottom lies below the least fixed point. -/
theorem iterate_bot_le_lfp [CompleteLattice β] (f : β →o β) (n : ℕ) :
    (f^[n]) ⊥ ≤ f.lfp := by
  induction n with
  | zero => exact bot_le
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (f.monotone ih).trans_eq f.map_lfp

/-- A monotone map on a finite powerset reaches its least fixed point from the empty set after
at most the cardinality of the underlying type many iterations. -/
theorem iterate_card_bot_eq_lfp [Fintype α] (f : Set α →o Set α) :
    (f^[Fintype.card α]) ⊥ = f.lfp := by
  have hmono : Monotone fun n => (f^[n]) ⊥ :=
    f.monotone.monotone_iterate_of_le_map bot_le
  have hgrowth : ∀ n, (f^[n]) ⊥ = f.lfp ∨ n ≤ ((f^[n]) ⊥).ncard := by
    intro n
    induction n with
    | zero => exact Or.inr (Nat.zero_le _)
    | succ n ih =>
      rcases ih with hfixed | hcard
      · left
        rw [Function.iterate_succ_apply', hfixed, f.map_lfp]
      · by_cases heq : (f^[n]) ⊥ = (f^[n + 1]) ⊥
        · left
          have hfixed : f ((f^[n]) ⊥) = (f^[n]) ⊥ := by
            exact (Function.iterate_succ_apply' f n ⊥).symm.trans heq.symm
          rw [← heq]
          exact le_antisymm (f.iterate_bot_le_lfp n) (f.lfp_le_fixed hfixed)
        · right
          have hlt : ((f^[n]) ⊥).ncard < ((f^[n + 1]) ⊥).ncard :=
            Set.ncard_lt_ncard (lt_of_le_of_ne (hmono (Nat.le_succ n)) heq)
          omega
  rcases hgrowth (Fintype.card α) with hfixed | hcard
  · exact hfixed
  · have huniv : (f^[Fintype.card α]) ⊥ = Set.univ := by
      apply (Set.eq_univ_iff_ncard _).2
      rw [Nat.card_eq_fintype_card]
      apply le_antisymm ?_ hcard
      simpa only [Nat.card_eq_fintype_card] using
        (Set.ncard_le_card ((f^[Fintype.card α]) ⊥))
    apply le_antisymm (f.iterate_bot_le_lfp _)
    rw [huniv]
    exact Set.subset_univ _

/-- Every iteration at or beyond the finite powerset bound equals the least fixed point. -/
theorem iterate_bot_eq_lfp_of_card_le [Fintype α] (f : Set α →o Set α) {n : ℕ}
    (hn : Fintype.card α ≤ n) : (f^[n]) ⊥ = f.lfp := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm, Function.iterate_add_apply, f.iterate_card_bot_eq_lfp]
  exact Function.iterate_fixed f.map_lfp k

end OrderHom
