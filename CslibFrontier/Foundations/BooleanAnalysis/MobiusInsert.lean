/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.Mobius
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-!
# Adding a coordinate to a subset Möbius transform

The insertion rule relates coefficient extraction to a signed traversal of Boolean choices.

## Main results

* `Cslib.BitString.subsetMobius_insert`: insertion of a fresh coordinate is a finite difference.
-/

public section

namespace Cslib.BitString

open Finset

/-- Adding a fresh coordinate subtracts the old coefficient from the coefficient with that
coordinate fixed to one. -/
theorem subsetMobius_insert {α M : Type*} [DecidableEq α] [AddCommGroup M]
    (f : Finset α → M) {a : α} {S : Finset α} (ha : a ∉ S) :
    subsetMobius f (insert a S) =
      subsetMobius (fun T => f (insert a T)) S - subsetMobius f S := by
  unfold subsetMobius
  rw [sum_powerset_insert ha]
  have hfirst : (∑ T ∈ S.powerset, (-1 : ℤ) ^ (#(insert a S) - #T) • f T) =
      -(∑ T ∈ S.powerset, (-1 : ℤ) ^ (#S - #T) • f T) := by
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro T hT
    have hcard := card_le_card (mem_powerset.mp hT)
    rw [card_insert_of_notMem ha, show #S + 1 - #T = (#S - #T) + 1 by omega, pow_succ]
    simp
  have hsecond : (∑ T ∈ S.powerset,
      (-1 : ℤ) ^ (#(insert a S) - #(insert a T)) • f (insert a T)) =
      ∑ T ∈ S.powerset, (-1 : ℤ) ^ (#S - #T) • f (insert a T) := by
    apply sum_congr rfl
    intro T hT
    have hat : a ∉ T := notMem_mono (mem_powerset.mp hT) ha
    rw [card_insert_of_notMem ha, card_insert_of_notMem hat, Nat.add_sub_add_right]
  rw [hfirst, hsecond]
  abel

end Cslib.BitString
