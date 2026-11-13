/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate (Mathlib, weighted subset counts)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Combinatorics.SmallSubsets
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Geometrically weighted subsets

The sum of `q ^ card t` over the nonempty subsets of `s` is at most one when
`card s * q ≤ 1 / 2` and `0 ≤ q ≤ 1`. This is the subset-counting estimate in the pointwise
Vazirani lemma used for query-to-communication lifting. Counting the subsets below a
cardinality threshold also gives the elementary bound used in its min-entropy variant.

## Main results

* `Finset.sum_nonempty_powerset_pow_card_le_one`: geometric subset weights.
* `Finset.card_filter_card_lt_add_one_le_pow`: a small-subset count.
-/

public section

namespace Finset

private theorem one_add_pow_le_two_of_mul_le_half {q : ℝ} {n : ℕ}
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hn : n * q ≤ 1 / 2) : (1 + q) ^ n ≤ 2 := by
  have hB := one_add_mul_le_pow (a := -q) (by linarith) n
  have hprod : (1 + q) ^ n * (1 - q) ^ n ≤ 1 := by
    rw [← mul_pow]
    apply pow_le_one₀
    · nlinarith
    · nlinarith
  have hmul := mul_le_mul_of_nonneg_left hB (pow_nonneg (by linarith : 0 ≤ 1 + q) n)
  have hnonneg : 0 ≤ (1 + q) ^ n := pow_nonneg (by linarith) n
  have hhalf : (1 + q) ^ n * (1 / 2) ≤ (1 + q) ^ n * (1 + n * -q) :=
    mul_le_mul_of_nonneg_left (by linarith) hnonneg
  have hsame : (1 + -q) ^ n = (1 - q) ^ n := by rw [sub_eq_add_neg]
  rw [hsame] at hmul
  linarith

/-- The total geometric weight of nonempty subsets is at most one if `card s * q ≤ 1 / 2`.
The empty ambient set is allowed. -/
theorem sum_nonempty_powerset_pow_card_le_one {α : Type*} (s : Finset α) {q : ℝ}
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hs : s.card * q ≤ 1 / 2) :
    ∑ t ∈ s.powerset.filter Finset.Nonempty, q ^ t.card ≤ 1 := by
  classical
  have hexp : (∑ t ∈ s.powerset, q ^ t.card) = (1 + q) ^ s.card := by
    simpa using (prod_one_add (f := fun _ : α => q) s).symm
  have hsplit := sum_filter_add_sum_filter_not s.powerset Finset.Nonempty (fun t => q ^ t.card)
  have hempty : (∑ t ∈ s.powerset with ¬ t.Nonempty, q ^ t.card) = 1 := by
    rw [sum_eq_single ∅]
    · simp
    · intro t ht hne
      exact False.elim (hne ((not_nonempty_iff_eq_empty).mp (mem_filter.mp ht).2))
    · simp
  rw [hempty, hexp] at hsplit
  have hpow := one_add_pow_le_two_of_mul_le_half hq hq1 hs
  linarith

/-- For a ground set of size at least two, the number of subsets of size less than `t`,
plus one, is at most the `t`th power of the ground-set size. -/
theorem card_filter_card_lt_add_one_le_pow {α : Type*} [Fintype α]
    (hn : 2 ≤ Fintype.card α) (t : ℕ) :
    #{S : Finset α | S.card < t} + 1 ≤ Fintype.card α ^ t := by
  classical
  have hsum : ∀ k : ℕ,
      (∑ j ∈ range k, Fintype.card α ^ j) + 1 ≤ Fintype.card α ^ k := by
    intro k
    rw [Nat.geomSum_eq hn k]
    have hdiv := Nat.div_le_self (Fintype.card α ^ k - 1) (Fintype.card α - 1)
    have hpos : 0 < Fintype.card α ^ k := pow_pos (by omega) k
    omega
  cases t with
  | zero => simp
  | succ t =>
    have heq : #{S : Finset α | S.card < t + 1} =
        ∑ j ∈ range (t + 1), (Fintype.card α).choose j := by
      simpa only [Nat.lt_succ_iff] using card_filter_card_le_eq_sum_choose (α := α) t
    rw [heq]
    have hchoose : (∑ j ∈ range (t + 1), (Fintype.card α).choose j) ≤
        ∑ j ∈ range (t + 1), Fintype.card α ^ j :=
      sum_le_sum fun j _ => Nat.choose_le_pow _ _
    exact (Nat.add_le_add_right hchoose 1).trans (hsum (t + 1))

/-- The small-subset estimate with an ambient upper bound on the ground-set cardinality.
This includes ground sets of size zero or one when the ambient bound is at least two. -/
theorem card_filter_card_lt_add_one_le_pow_of_card_le {α : Type*} [Fintype α]
    {N : ℕ} (hN : 2 ≤ N) (hcard : Fintype.card α ≤ N) (t : ℕ) :
    #{S : Finset α | S.card < t} + 1 ≤ N ^ t := by
  classical
  have hamb := card_filter_card_lt_add_one_le_pow (α := Fin N) (by simpa using hN) t
  simp only [Fintype.card_fin] at hamb
  refine (Nat.add_le_add_right ?_ 1).trans hamb
  cases t with
  | zero => simp
  | succ t =>
    simp only [Nat.lt_succ_iff]
    rw [card_filter_card_le_eq_sum_choose, card_filter_card_le_eq_sum_choose]
    simp only [Fintype.card_fin]
    exact sum_le_sum fun j _ => Nat.choose_le_choose j hcard

end Finset
