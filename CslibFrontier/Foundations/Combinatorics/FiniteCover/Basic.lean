/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Finite covers from an exact union bound

If a uniformly chosen test misses each obligation with probability at most `p / q`, then
`t` tests hit every obligation as soon as `|W| p ^ t < q ^ t`. The proof counts bad test
sequences and takes their union over the obligations, using only finite cardinalities.
Covers from a uniform density lower bound are in the companion `FiniteCover` module.

## Main results

* `Cslib.exists_cover_of_scaled_card_lt`: the union bound for covers with integer cardinalities.
-/

public section

namespace Cslib

open Finset

/-- **The union bound for covers**, with integer cardinalities: if a uniform test misses each
obligation with probability at most `p / q`, and `|W| p ^ t < q ^ t`, then some `t` tests hit
every obligation. -/
theorem exists_cover_of_scaled_card_lt
    {S W : Type*} [Fintype S] [Nonempty S] [Fintype W]
    (hit : S → W → Prop) [DecidableRel hit] (p q t : Nat)
    (localBound : ∀ w,
      q * Fintype.card {s : S // ¬ hit s w} ≤ p * Fintype.card S)
    (small : Fintype.card W * p ^ t < q ^ t) :
    ∃ tests : Fin t → S, ∀ w, ∃ i, hit (tests i) w := by
  classical
  let bad (w : W) : Finset (Fin t → S) :=
    univ.filter fun tests => ∀ i, ¬ hit (tests i) w
  have badCard (w : W) :
      (bad w).card = (Fintype.card {s : S // ¬ hit s w}) ^ t := by
    calc
      (bad w).card =
          Fintype.card {tests : Fin t → S // ∀ i, ¬ hit (tests i) w} := by
            simp [bad, Fintype.card_subtype]
      _ = Fintype.card (Fin t → {s : S // ¬ hit s w}) :=
        Fintype.card_congr (Equiv.subtypePiEquivPi
          (p := fun (_ : Fin t) (s : S) => ¬ hit s w))
      _ = _ := by simp
  have localPower (w : W) :
      q ^ t * (bad w).card ≤ p ^ t * (Fintype.card S) ^ t := by
    rw [badCard, ← mul_pow, ← mul_pow]
    exact Nat.pow_le_pow_left (localBound w) t
  let failures := univ.biUnion bad
  have unionBound : q ^ t * failures.card ≤
      Fintype.card W * p ^ t * (Fintype.card S) ^ t := by
    calc
      q ^ t * failures.card ≤ q ^ t * ∑ w, (bad w).card :=
        Nat.mul_le_mul_left _ card_biUnion_le
      _ = ∑ w, q ^ t * (bad w).card := mul_sum ..
      _ ≤ ∑ _w : W, p ^ t * (Fintype.card S) ^ t :=
        sum_le_sum fun w _ => localPower w
      _ = _ := by simp [Nat.mul_assoc]
  have strict : q ^ t * failures.card <
      q ^ t * Fintype.card (Fin t → S) := by
    apply lt_of_le_of_lt unionBound
    simpa [Fintype.card_fun] using
      Nat.mul_lt_mul_of_pos_right small
        (Nat.pow_pos (Fintype.card_pos))
  have smaller : failures.card < Fintype.card (Fin t → S) := by
    exact Nat.lt_of_mul_lt_mul_left strict
  obtain ⟨tests, _, absent⟩ := exists_mem_notMem_of_card_lt_card
    (show failures.card < (univ : Finset (Fin t → S)).card by simpa using smaller)
  refine ⟨tests, fun w => ?_⟩
  by_contra none
  apply absent
  simp only [failures, mem_biUnion, mem_univ, true_and]
  exact ⟨w, by simpa [bad] using none⟩

end Cslib
