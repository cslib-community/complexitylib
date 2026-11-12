/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Combinatorics.FiniteCover.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Order.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import CslibFrontier.Foundations.Data.Nat.Choose
import Mathlib.Tactic.Linarith

/-!
# Finite covers from uniform local density

If a uniformly chosen test misses each of the obligations `w : W` with probability at most `p / q`,
then `t` tests hit every obligation as soon as `|W| p ^ t < q ^ t`
(`exists_cover_of_scaled_card_lt`): the bad sequences of tests are counted, with a union bound
over the obligations. In particular, if every obligation is hit by at least a `1 / q` fraction of
the tests, then `q (n + 1)` tests hit `2 ^ n` obligations (`exists_cover_of_density`). Its
budget is the integer form `2 ^ n (q - 1) ^ (q (n + 1)) < q ^ (q (n + 1))` of
`2 ^ n (1 - 1 / q) ^ (q (n + 1)) < 1` (`Nat.two_pow_mul_pred_pow_mul_succ_lt`), which follows from
`2 (q - 1) ^ q ≤ q ^ q` without exponential estimates. The exact bound is reexported from
`FiniteCover.Basic`, so clients that need only the union bound can import that module alone.

## Main results

* `Cslib.exists_cover_of_scaled_card_lt`: the union bound for covers.
* `Nat.two_pow_mul_pred_pow_mul_succ_lt`: the power bound behind the density budget.
* `Cslib.exists_cover_of_density`: covers from density.
-/

public section

/-- For `1 ≤ b`, `2 ^ n * (b - 1) ^ (b * (n + 1)) < b ^ (b * (n + 1))`: the integer form of
`2 ^ n * (1 - 1 / b) ^ (b * (n + 1)) < 1`, from `2 * (b - 1) ^ b ≤ b ^ b`. -/
theorem Nat.two_pow_mul_pred_pow_mul_succ_lt {b : ℕ} (hb : 1 ≤ b) (n : ℕ) :
    2 ^ n * (b - 1) ^ (b * (n + 1)) < b ^ (b * (n + 1)) := by
  have h := Nat.pow_le_pow_left (Nat.two_mul_pred_pow_le hb) (n + 1)
  rw [mul_pow, ← pow_mul, ← pow_mul, pow_succ] at h
  have hp := Nat.pow_pos (n := b * (n + 1)) hb
  nlinarith

namespace Cslib

open Finset

/-- **Covers from density**: if every obligation `w` is hit by at least a `1 / q` fraction of the
tests, then `q (n + 1)` tests, with repetitions, hit all of at most `2 ^ n` obligations. -/
theorem exists_cover_of_density {S W : Type*} [Fintype S] [Nonempty S] [Fintype W]
    (hit : S → W → Prop) [DecidableRel hit] (q n : ℕ) (hq : 0 < q)
    (hw : Fintype.card W ≤ 2 ^ n)
    (density : ∀ w, Fintype.card S ≤ q * Fintype.card {s : S // hit s w}) :
    ∃ tests : Fin (q * (n + 1)) → S, ∀ w, ∃ i, hit (tests i) w := by
  classical
  apply exists_cover_of_scaled_card_lt
    hit (q - 1) q (q * (n + 1))
  · intro w
    rw [Fintype.card_subtype_compl]
    have hc : Fintype.card {s : S // hit s w} ≤ Fintype.card S :=
      Fintype.card_subtype_le _
    have hd := density w
    have hsub := Nat.sub_add_cancel hc
    have hqsub : q - 1 + 1 = q := by omega
    nlinarith
  · exact (Nat.mul_le_mul_right _ hw).trans_lt (Nat.two_pow_mul_pred_pow_mul_succ_lt hq n)

end Cslib
