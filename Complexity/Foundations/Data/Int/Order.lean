/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger, Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger, Karn Seth, Anton Kovsharov
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Data/Int/Order/Basic.lean`)

public import Complexity.Init
public import Mathlib.Data.Int.Order.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Ring

/-!
# Magnitude bounds on integer powers and list sums

Bounds on the absolute value `Int.natAbs` of powers of integers, and bounds on the absolute
value of sums and prefix sums of lists of integers bounded termwise.

## Main results

* `Int.natAbs_pow_le`: `(z ^ q).natAbs ≤ H ^ M` when `z.natAbs ≤ H` and `q ≤ M`.
* `List.natAbs_sum_le_length_mul`: `l.sum.natAbs ≤ l.length * C` when every element of `l` is
  bounded by `C`.
* `List.natAbs_sum_take_le_length_mul`: every prefix sum of `l` is bounded by `l.length * C`.
* `List.natAbs_sum_take_le_of_length_le`: prefix sums are bounded by `m * C` when `l.length ≤ m`.
* `List.natAbs_getD_le_of_forall`: `getD` with default `0` preserves elementwise `natAbs` bounds.
-/

@[expose] public section

namespace Int

/-- A power of an integer is bounded in magnitude by the corresponding power of a bound on the
base. -/
lemma natAbs_pow_le {z : ℤ} {H : ℕ} (hH : 1 ≤ H) (hz : z.natAbs ≤ H) {q M : ℕ} (hq : q ≤ M) :
    (z ^ q).natAbs ≤ H ^ M := by
  rw [Int.natAbs_pow]
  exact (Nat.pow_le_pow_left hz q).trans (Nat.pow_le_pow_right hH hq)

end Int

namespace List

/-- The magnitude of a sum of integers is at most the length times a termwise bound. -/
lemma natAbs_sum_le_length_mul {l : List ℤ} {C : ℕ} (h : ∀ x ∈ l, x.natAbs ≤ C) :
    l.sum.natAbs ≤ l.length * C := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.sum_cons, List.length_cons]
    calc (x + l.sum).natAbs ≤ x.natAbs + l.sum.natAbs := Int.natAbs_add_le _ _
      _ ≤ C + l.length * C :=
          Nat.add_le_add (h x List.mem_cons_self) (ih fun y hy => h y (List.mem_cons_of_mem x hy))
      _ = (l.length + 1) * C := by ring

/-- Every prefix sum of a list is bounded by its length times a bound on its entries. -/
lemma natAbs_sum_take_le_length_mul {l : List ℤ} {C : ℕ} (h : ∀ x ∈ l, x.natAbs ≤ C) (m : ℕ) :
    (l.take m).sum.natAbs ≤ l.length * C :=
  (natAbs_sum_le_length_mul fun x hx => h x (List.mem_of_mem_take hx)).trans
    (Nat.mul_le_mul_right _ (List.length_take_le' _ _))

/-- Every prefix sum and the sum of a list of terms bounded by `C` are bounded by
`m * C`, where `m` bounds the length. -/
lemma natAbs_sum_take_le_of_length_le {l : List ℤ} {C m : ℕ} (hl : l.length ≤ m)
    (h : ∀ x ∈ l, x.natAbs ≤ C) (k : ℕ) : (l.take k).sum.natAbs ≤ m * C :=
  (natAbs_sum_take_le_length_mul h k).trans (Nat.mul_le_mul_right C hl)

/-- Looking up `l.getD i 0` preserves any uniform bound on `Int.natAbs` of elements of `l`. -/
lemma natAbs_getD_le_of_forall {l : List ℤ} {B : ℕ} (hl : ∀ x ∈ l, x.natAbs ≤ B) (i : ℕ) :
    (l.getD i 0).natAbs ≤ B := by
  by_cases hi : i < l.length
  · rw [List.getD_eq_getElem l 0 hi]; exact hl _ (List.getElem_mem hi)
  · rw [List.getD_eq_default l 0 (Nat.le_of_not_lt hi), Int.natAbs_zero]; exact Nat.zero_le B

end List
