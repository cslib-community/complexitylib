/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
import CslibFrontier.Foundations.Data.Finset.Markov
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Few subsets meet a fixed set in few points

A uniformly random subset `x` of a finite set `S` meets a fixed `K ⊆ S` in about `#K / 2` points.
Weighting each subset `x` by `2 ^ #(K \ x)` gives total weight `3 ^ #K 2 ^ #(S \ K)`
(`Cslib.sum_powerset_two_pow_card_sdiff`), and every subset meeting `K` in at most `j` points has
weight at least `2 ^ (#K - j)`. So at most a `(3 / 4) ^ #K 2 ^ j` fraction of the subsets of `S`
meet `K` in at most `j` points (`Cslib.two_pow_mul_card_filter_card_inter_le`); for instance at
most a `(27 / 32) ^ r / 2` fraction meet a set of `3 r` points in fewer than `r` points. Weighting
by `2 ^ #x` instead bounds the subsets missing at most `j` points of `S`
(`Cslib.two_pow_mul_card_filter_card_sdiff_le`). This is the exponential-moment (Chernoff) bound
with the single weight `2` [Alon and Spencer, Appendix A][AlonSpencer2016], stated by counting; for
the subsets of `K` itself, Hoeffding's bound for fair coins
(`Cslib.BitString.card_filter_le_card_filter_sub_half_le`) is sharper.

A family of sets for which many points of `S` are avoided by most of its members inside `S` is
therefore small (`Cslib.four_mul_sum_card_filter_notMem_le`): by Markov's inequality, many of its
members meet the avoided points in few points, or miss few points of `S`. This is the counting
step of Razborov's corruption bound for disjointness [Razborov1992].

## Main results

* `Cslib.two_pow_mul_card_filter_card_inter_le`: few subsets of `S` meet `K` in few points.
* `Cslib.two_pow_mul_card_filter_card_sdiff_le`: few subsets of `S` miss few of its points.
* `Cslib.four_mul_sum_card_filter_notMem_le`: families avoiding many points are small.

## References

* [N. Alon and J. H. Spencer, *The Probabilistic Method*][AlonSpencer2016]
* [A. A. Razborov, *On the distributional complexity of disjointness*][Razborov1992]
-/

@[expose] public section

namespace Cslib

open Finset

variable {U : Type*} [DecidableEq U]

/-- Weighting each subset `x` of `S` by `2 ^ #(K \ x)` gives total weight `3 ^ #K 2 ^ #(S \ K)`. -/
theorem sum_powerset_two_pow_card_sdiff {K S : Finset U} (hKS : K ⊆ S) :
    ∑ x ∈ S.powerset, 2 ^ #(K \ x) = 3 ^ #K * 2 ^ (#S - #K) := by
  have h := prod_add (fun _ => (1 : ℕ)) (fun i => if i ∈ K then 2 else 1) S
  simp only [prod_const_one, one_mul, prod_ite_mem] at h
  have hl : ∏ i ∈ S, (1 + if i ∈ K then 2 else 1) = 3 ^ #K * 2 ^ (#S - #K) := by
    have : ∀ i ∈ S, (1 + if i ∈ K then 2 else 1) = if i ∈ K then 3 else 2 := by
      intro i _
      split_ifs <;> rfl
    have hK : S.filter (· ∈ K) = K := by
      rw [filter_mem_eq_inter, inter_eq_right.mpr hKS]
    have hK' : S.filter (· ∉ K) = S \ K := by
      ext i
      simp only [mem_filter, mem_sdiff]
    rw [prod_congr rfl this, prod_ite, prod_const, prod_const, hK, hK',
      card_sdiff_of_subset hKS]
  rw [← hl, h]
  refine sum_congr rfl fun t _ => ?_
  rw [prod_const]
  congr 2
  ext i
  have := @hKS i
  simp only [mem_inter, mem_sdiff]
  tauto

/-- Few subsets of `S` meet `K ⊆ S` in at most `j` points: `2 ^ (#K - j)` times their number is at
most `3 ^ #K 2 ^ #(S \ K)`. -/
theorem two_pow_mul_card_filter_card_inter_le {K S : Finset U} (hKS : K ⊆ S) (j : ℕ) :
    2 ^ (#K - j) * #{x ∈ S.powerset | #(K ∩ x) ≤ j} ≤ 3 ^ #K * 2 ^ (#S - #K) := by
  rw [← sum_powerset_two_pow_card_sdiff hKS]
  refine mul_card_filter_le_sum _ _ _ fun x _ hx => Nat.pow_le_pow_right (Nat.succ_pos 1) ?_
  have h := card_sdiff_add_card_inter K x
  omega

/-- Few subsets of `S` miss at most `j` of its points: `2 ^ (#S - j)` times their number is at
most `3 ^ #S`. -/
theorem two_pow_mul_card_filter_card_sdiff_le (S : Finset U) (j : ℕ) :
    2 ^ (#S - j) * #{x ∈ S.powerset | #(S \ x) ≤ j} ≤ 3 ^ #S := by
  have h := sum_pow_mul_eq_add_pow (2 : ℕ) 1 S
  simp only [one_pow, mul_one] at h
  rw [show (3 : ℕ) = 2 + 1 from rfl, ← h]
  refine mul_card_filter_le_sum _ _ _ fun x hx hj => Nat.pow_le_pow_right (Nat.succ_pos 1) ?_
  have := card_sdiff_add_card_eq_card (mem_powerset.mp hx)
  omega

/-! ### Families of sets that avoid many points -/

/-- If `S` contains at least `3 * r` points `i` with `4 * #{x ∈ AS | i ∈ x} ≤ #AS`, where
`AS = A.filter (· ⊆ S)`, then `#AS * 32 ^ r ≤ 2 * 27 ^ r * 2 ^ #S`. -/
private theorem card_filter_subset_mul_pow_le (A : Finset (Finset U)) (S : Finset U) {r : ℕ}
    (hbad : 3 * r ≤ #{i ∈ S | 4 * #{x ∈ A.filter (· ⊆ S) | i ∈ x} ≤ #(A.filter (· ⊆ S))}) :
    #(A.filter (· ⊆ S)) * 32 ^ r ≤ 2 * 27 ^ r * 2 ^ #S := by
  set AS := A.filter (· ⊆ S)
  have hASsub : AS ⊆ S.powerset := fun x hx => mem_powerset.mpr (mem_filter.mp hx).2
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · have := (card_le_card hASsub).trans (card_powerset S).le
    simp only [pow_zero, mul_one]; omega
  obtain ⟨K, hKbad, hKcard⟩ := exists_subset_card_eq hbad
  have hKS : K ⊆ S := hKbad.trans (filter_subset _ _)
  have h4sum : 4 * ∑ x ∈ AS, #(K ∩ x) ≤ 3 * r * #AS := by
    have hsumK : ∑ i ∈ K, #{x ∈ AS | i ∈ x} = ∑ x ∈ AS, #(K ∩ x) := by
      rw [show ∑ i ∈ K, #{x ∈ AS | i ∈ x} = ∑ x ∈ AS, #{i ∈ K | i ∈ x} from
        sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow _]
      exact sum_congr rfl fun x _ => by rw [filter_mem_eq_inter]
    rw [← hsumK, mul_sum]
    calc ∑ i ∈ K, 4 * #{x ∈ AS | i ∈ x} ≤ ∑ _i ∈ K, #AS :=
          sum_le_sum fun i hi => (mem_filter.mp (hKbad hi)).2
      _ = 3 * r * #AS := by rw [sum_const, hKcard, smul_eq_mul]
  have hG : r * #{x ∈ AS | r ≤ #(K ∩ x)} ≤ ∑ x ∈ AS, #(K ∩ x) :=
    mul_card_filter_le_sum _ _ _ fun _ _ => id
  have h4G : 4 * #{x ∈ AS | r ≤ #(K ∩ x)} ≤ 3 * #AS := Nat.le_of_mul_le_mul_left (by nlinarith) hr
  have hGL : #{x ∈ AS | r ≤ #(K ∩ x)} + #{x ∈ AS | ¬r ≤ #(K ∩ x)} = #AS :=
    card_filter_add_card_filter_not _
  have hL : #{x ∈ AS | ¬r ≤ #(K ∩ x)} ≤ #{x ∈ S.powerset | #(K ∩ x) ≤ r - 1} :=
    card_le_card fun x hx => mem_filter.mpr ⟨hASsub (mem_filter.mp hx).1, by
      have := (mem_filter.mp hx).2; omega⟩
  have hcount := two_pow_mul_card_filter_card_inter_le hKS (r - 1)
  rw [hKcard, show 3 * r - (r - 1) = 2 * r + 1 by omega] at hcount
  have key : 2 ^ (2 * r + 1) * #AS ≤ 4 * (3 ^ (3 * r) * 2 ^ (#S - 3 * r)) :=
    (Nat.mul_le_mul_left _ (show #AS ≤ 4 * #{x ∈ S.powerset | #(K ∩ x) ≤ r - 1} by omega)).trans
      (by rw [mul_left_comm]; exact Nat.mul_le_mul_left _ hcount)
  have h2S : 2 ^ (#S - 3 * r) * 2 ^ (3 * r) = 2 ^ #S := by
    rw [← pow_add, Nat.sub_add_cancel (hKcard ▸ card_le_card hKS)]
  have h32 : (32 : ℕ) ^ r = 2 ^ (2 * r) * 2 ^ (3 * r) := by
    rw [← pow_add, show 2 * r + 3 * r = 5 * r by ring, pow_mul]; norm_num
  have h27 : (27 : ℕ) ^ r = 3 ^ (3 * r) := by rw [pow_mul]; norm_num
  rw [h32, h27]; refine Nat.le_of_mul_le_mul_left ?_ (two_pos : 0 < 2)
  calc 2 * (#AS * (2 ^ (2 * r) * 2 ^ (3 * r))) = 2 ^ (2 * r + 1) * #AS * 2 ^ (3 * r) := by ring
    _ ≤ 4 * (3 ^ (3 * r) * 2 ^ (#S - 3 * r)) * 2 ^ (3 * r) := Nat.mul_le_mul_right _ key
    _ = 2 * (2 * 3 ^ (3 * r) * (2 ^ (#S - 3 * r) * 2 ^ (3 * r))) := by ring
    _ = 2 * (2 * 3 ^ (3 * r) * 2 ^ #S) := by rw [h2S]

/-- In `ℝ`, the subsets of `S` missing at most `j` points number at most
`2 ^ #S * (2 ^ j * (3 / 4) ^ #S)`. -/
private theorem card_filter_card_sdiff_le_real (S : Finset U) (j : ℕ) :
    (#{x ∈ S.powerset | #(S \ x) ≤ j} : ℝ) ≤ 2 ^ #S * (2 ^ j * (3 / 4) ^ #S) := by
  have hcount : 2 ^ #S * #{x ∈ S.powerset | #(S \ x) ≤ j} ≤ 2 ^ j * 3 ^ #S :=
    calc 2 ^ #S * #{x ∈ S.powerset | #(S \ x) ≤ j}
        ≤ 2 ^ j * 2 ^ (#S - j) * #{x ∈ S.powerset | #(S \ x) ≤ j} :=
          Nat.mul_le_mul_right _ (by
            rw [← pow_add]
            exact Nat.pow_le_pow_right two_pos (by omega))
      _ ≤ 2 ^ j * 3 ^ #S := by
          rw [mul_assoc]
          exact Nat.mul_le_mul_left _ (two_pow_mul_card_filter_card_sdiff_le S j)
  have hcountR : (2 : ℝ) ^ #S * #{x ∈ S.powerset | #(S \ x) ≤ j} ≤ 2 ^ j * 3 ^ #S := by
    exact_mod_cast hcount
  have h34 : (2 : ℝ) ^ #S * (2 ^ #S * (2 ^ j * (3 / 4) ^ #S)) = 2 ^ j * 3 ^ #S := by
    calc (2 : ℝ) ^ #S * (2 ^ #S * (2 ^ j * (3 / 4) ^ #S))
        = 2 ^ j * ((2 * (2 * (3 / 4))) ^ #S) := by rw [mul_pow, mul_pow]; ring
      _ = 2 ^ j * 3 ^ #S := by norm_num
  exact le_of_mul_le_mul_left (hcountR.trans_eq h34.symm) (by positivity)

/-- If `4 * #bad ≤ j + 1`, then `4` times the sum of avoidance counts over `bad` is at most the
sum over `S` plus `(j + 1) * #{x ∈ S.powerset | #(S \ x) ≤ j}`. -/
private theorem four_mul_sum_bad_le_sum_add (A : Finset (Finset U)) (S : Finset U) {j : ℕ}
    {bad : Finset U} (hbad : 4 * #bad ≤ j + 1) :
    4 * ∑ i ∈ bad, #{x ∈ A | x ⊆ S ∧ i ∉ x} ≤
      ∑ i ∈ S, #{x ∈ A | x ⊆ S ∧ i ∉ x} + (j + 1) * #{x ∈ S.powerset | #(S \ x) ≤ j} := by
  set AS := A.filter (· ⊆ S) with hAS
  have hASsub : AS ⊆ S.powerset := fun x hx => mem_powerset.mpr (mem_filter.mp hx).2
  have havoid (i : U) : #{x ∈ A | x ⊆ S ∧ i ∉ x} = #{x ∈ AS | i ∉ x} := by rw [hAS, filter_filter]
  have hsum_bad : ∑ i ∈ bad, #{x ∈ A | x ⊆ S ∧ i ∉ x} ≤ #bad * #AS :=
    (sum_le_sum fun i _ => (show #{x ∈ A | x ⊆ S ∧ i ∉ x} ≤ #AS by
      rw [havoid]; exact card_filter_le _ _)).trans_eq (by rw [sum_const, smul_eq_mul])
  have hS : ∑ i ∈ S, #{x ∈ A | x ⊆ S ∧ i ∉ x} = ∑ x ∈ AS, #(S \ x) := by
    simp only [havoid]
    rw [show ∑ i ∈ S, #{x ∈ AS | i ∉ x} = ∑ x ∈ AS, #{i ∈ S | i ∉ x} from
      sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow _]
    exact sum_congr rfl fun x _ => by rw [sdiff_eq_filter]
  have hH : (j + 1) * #{x ∈ AS | j < #(S \ x)} ≤ ∑ x ∈ AS, #(S \ x) :=
    mul_card_filter_le_sum _ _ _ fun _ _ => id
  have hHH : #{x ∈ AS | j < #(S \ x)} + #{x ∈ AS | ¬j < #(S \ x)} = #AS :=
    card_filter_add_card_filter_not _
  have hH' : #{x ∈ AS | ¬j < #(S \ x)} ≤ #{x ∈ S.powerset | #(S \ x) ≤ j} :=
    card_le_card fun x hx => mem_filter.mpr ⟨hASsub (mem_filter.mp hx).1, by
      have := (mem_filter.mp hx).2; omega⟩
  rw [hS]
  calc 4 * ∑ i ∈ bad, #{x ∈ A | x ⊆ S ∧ i ∉ x} ≤ 4 * (#bad * #AS) :=
        Nat.mul_le_mul_left _ hsum_bad
    _ ≤ (j + 1) * #AS := by rw [← mul_assoc]; exact Nat.mul_le_mul_right _ hbad
    _ = (j + 1) * #{x ∈ AS | j < #(S \ x)} + (j + 1) * #{x ∈ AS | ¬j < #(S \ x)} := by
        rw [← hHH, mul_add]
    _ ≤ ∑ x ∈ AS, #(S \ x) + (j + 1) * #{x ∈ S.powerset | #(S \ x) ≤ j} :=
        Nat.add_le_add hH (Nat.mul_le_mul_left _ hH')

/-- **A family of sets that avoid many points is small.** Let `A` be a family of sets and `S` a
finite set, and call a point `i ∈ S` *bad* if the members of `A` inside `S` containing `i` are
fewer than a third of those avoiding it. Then the pairs of a member of `A` inside `S` and a bad
point it avoids are at most a quarter of the pairs of a member inside `S` and a point of `S` it
avoids, up to `2 ^ #S (8 #S (27 / 32) ^ r + (j + 1) 2 ^ j (3 / 4) ^ #S)`, which is a small
fraction of `#S 2 ^ #S` when `#S ≥ 48 r` and `j = 12 r`. If at least `3 r` points are bad, at
least a quarter of the members of `A` inside `S` meet a set `K` of `3 r` bad points in fewer than
`r` points, by Markov's inequality, and few subsets of `S` do
(`two_pow_mul_card_filter_card_inter_le`). Otherwise, the bad points are fewer than `(j + 1) / 4`
and most members inside `S` avoid more than `j` points, unless few subsets of `S` miss at most `j`
points (`two_pow_mul_card_filter_card_sdiff_le`). This is the key counting step of the
corruption bound for disjointness (`Cslib.Communication.Disjointness.corrupted_hardDist`)
[Razborov1992]. -/
theorem four_mul_sum_card_filter_notMem_le (A : Finset (Finset U)) (S : Finset U) {r j : ℕ}
    (hrj : 12 * r ≤ j + 1) :
    4 * ∑ i ∈ S with 3 * #{x ∈ A | i ∈ x ∧ x ⊆ S} < #{x ∈ A | x ⊆ S ∧ i ∉ x},
        (#{x ∈ A | x ⊆ S ∧ i ∉ x} : ℝ) ≤
      ∑ i ∈ S, (#{x ∈ A | x ⊆ S ∧ i ∉ x} : ℝ) +
        2 ^ #S * (8 * #S * (27 / 32) ^ r + (j + 1) * 2 ^ j * (3 / 4) ^ #S) := by
  set AS := A.filter (· ⊆ S) with hAS; set N := #AS
  have havoid (i : U) : #{x ∈ A | x ⊆ S ∧ i ∉ x} = #{x ∈ AS | i ∉ x} := by rw [hAS, filter_filter]
  have hsplit (i : U) : #{x ∈ AS | i ∈ x} + #{x ∈ AS | i ∉ x} = N :=
    card_filter_add_card_filter_not _
  set bad := S.filter fun i => 3 * #{x ∈ A | i ∈ x ∧ x ⊆ S} < #{x ∈ A | x ⊆ S ∧ i ∉ x}
  have hpos : (0 : ℝ) ≤ ∑ i ∈ S, (#{x ∈ A | x ⊆ S ∧ i ∉ x} : ℝ) :=
    sum_nonneg fun _ _ => Nat.cast_nonneg _
  by_cases hbad : 3 * r ≤ #bad
  · -- Many bad points: the family is small.
    have hsum_bad : ∑ i ∈ bad, #{x ∈ A | x ⊆ S ∧ i ∉ x} ≤ #bad * N :=
      (sum_le_sum fun i _ => (show #{x ∈ A | x ⊆ S ∧ i ∉ x} ≤ N by
        rw [havoid]; exact card_filter_le _ _)).trans_eq (by rw [sum_const, smul_eq_mul])
    have hsmall : N * 32 ^ r ≤ 2 * 27 ^ r * 2 ^ #S := by
      refine card_filter_subset_mul_pow_le A S (hbad.trans (card_le_card fun i hi => ?_))
      obtain ⟨hiS, hlt⟩ := mem_filter.mp hi
      have hcontain : #{x ∈ A | i ∈ x ∧ x ⊆ S} = #{x ∈ AS | i ∈ x} := by
        rw [hAS, filter_filter]; exact congrArg card (filter_congr fun _ _ => and_comm)
      rw [hcontain, havoid] at hlt; have := hsplit i
      exact mem_filter.mpr ⟨hiS, by rw [← hAS]; omega⟩
    have hNr : (N : ℝ) ≤ 2 * (27 / 32) ^ r * 2 ^ #S := by
      have h : (N : ℝ) * 32 ^ r ≤ 2 * 27 ^ r * 2 ^ #S := by exact_mod_cast hsmall
      rw [div_pow, mul_div_assoc', div_mul_eq_mul_div, le_div_iff₀ (by positivity)]; linarith
    have h1 : (∑ i ∈ bad, (#{x ∈ A | x ⊆ S ∧ i ∉ x} : ℝ)) ≤ #S * N :=
      (by exact_mod_cast hsum_bad : (∑ i ∈ bad, (#{x ∈ A | x ⊆ S ∧ i ∉ x} : ℝ)) ≤ #bad * N).trans
        (mul_le_mul_of_nonneg_right (by exact_mod_cast card_le_card (filter_subset _ S))
          (by positivity))
    have h2 : (0 : ℝ) ≤ 2 ^ #S * ((j + 1) * 2 ^ j * (3 / 4) ^ #S) := by positivity
    have h3 : (#S : ℝ) * N ≤ #S * (2 * (27 / 32) ^ r * 2 ^ #S) := by gcongr
    nlinarith
  · -- Few bad points: most members of the family avoid many points.
    have hmainR : 4 * ∑ i ∈ bad, (#{x ∈ A | x ⊆ S ∧ i ∉ x} : ℝ) ≤
        ∑ i ∈ S, (#{x ∈ A | x ⊆ S ∧ i ∉ x} : ℝ) +
          (j + 1) * #{x ∈ S.powerset | #(S \ x) ≤ j} := by
      exact_mod_cast four_mul_sum_bad_le_sum_add A S (bad := bad) (by omega)
    have hQ := mul_le_mul_of_nonneg_left (card_filter_card_sdiff_le_real S j)
      (by positivity : (0 : ℝ) ≤ j + 1)
    have h8 : (0 : ℝ) ≤ 2 ^ #S * (8 * #S * (27 / 32) ^ r) := by positivity
    nlinarith

end Cslib
