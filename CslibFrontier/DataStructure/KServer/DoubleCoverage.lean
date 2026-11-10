/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.KServer.Basic
public import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Double Coverage is `k`-competitive on the line

This file proves the theorem of [Chrobak, Karloff, Payne and Vishwanathan, *New results on server
problems*][ChrobakKarloffPayneVishwanathan1991]: the Double Coverage algorithm for `k` servers on
the line is `k`-competitive. Together with the general lower bound
(`CslibFrontier.DataStructure.KServer.LowerBound`) this settles the deterministic competitive ratio
of the `k`-server problem on the line: from any start with distinct servers it is exactly `k`,
with an additive constant depending on the start. Double Coverage is not competitive with one
additive constant for all starts (`IsCompetitive`). The proof is the standard
potential-function argument for this algorithm (see also [Borodin and El-Yaniv, *Online
Computation and Competitive Analysis*, Chapter 10][BorodinElYaniv1998]). The line is usually taken
to be the real line; here the points are integers, which keeps distances natural numbers.

## The algorithm

Double Coverage (`dcStep`) serves a request `r` on the line `ℤ` with `k = n + 1` servers as
follows. If `r` lies left of all servers, the leftmost server moves to `r`; symmetrically on the
right. Otherwise let `a`, `b` be the nearest servers with `s a ≤ r < s b`. Both move toward `r` by
`min (r - s a) (s b - r)`, so one of them reaches `r`. A request on a server costs nothing. When
several servers share a position, only one of them moves. The implementation sorts the
configuration (`Tuple.sort`), applies the sorted rule `dcSorted` and undoes the sort, so labels
are preserved.

## Potential function

With `M_min` the minimum-cost matching between the Double Coverage and offline configurations
(`matchCost`) and `Σ_{i<j} |s_i - s_j|` the pairwise spread, the potential is
`Φ = k * M_min + Σ_{i<j} |s_i - s_j|`. We use the doubled potential
`2 * Φ = 2 * k * matchCost + pairSum`, since `pairSum` counts ordered pairs. Then each request
satisfies `2 * cost_DC + Δ(2 * Φ) ≤ 2 * k * cost_OPT` (`dcStep_amortized_offline`).

* **Outer request.** One server moves `d`. The matching distance drops by `d`, by uncrossing an
  optimal matching onto the moving server. The spread grows by `(k - 1) * d`.
* **Inner request.** Two servers move `d` toward each other. The matching distance does not grow,
  because one of the two is matched toward `r` after uncrossing. The spread drops by `2 * d`.
* **Offline move.** The matching distance grows by at most the offline movement.

## Main definitions

* `Cslib.DataStructure.KServer.dcSorted`: Double Coverage on a sorted configuration.
* `Cslib.DataStructure.KServer.dcStep`: Double Coverage on an arbitrary configuration.
* `Cslib.DataStructure.KServer.doubleCoverage`: the Double Coverage `Online.DetStrategy`.

## Main results

* `dcStep_amortized_offline`: the doubled amortized step inequality.
* `doubleCoverage_cost_le`: `cost_DC ≤ k * cost_OPT + k * matchCost s₀ s_off + pairSum s₀ / 2`,
  for any offline schedule from any start `s_off`.
* `doubleCoverage_isCompetitiveFrom`: Double Coverage is `k`-competitive from every initial
  configuration `s₀`, with additive constant `pairSum s₀ / 2 = Σ_{i<j} |s₀ i - s₀ j|`.

## References

* [M. Chrobak, H. J. Karloff, T. H. Payne and S. Vishwanathan, *New results on server
  problems*][ChrobakKarloffPayneVishwanathan1991]
* [A. Borodin and R. El-Yaniv, *Online Computation and Competitive Analysis*][BorodinElYaniv1998]
-/

public section

namespace Cslib.DataStructure.KServer

open Cslib.DataStructure.Online

variable {k : Nat}

/-! ### Double Coverage on a sorted configuration -/

/-- Number of servers at or left of `r`. -/
@[expose]
def countLe {n : Nat} (t : Fin n → Int) (r : Int) : Nat :=
  (Finset.univ.filter fun i => t i ≤ r).card

/-- On a sorted configuration, the servers at or left of `r` are exactly the first
`countLe t r`. -/
theorem lt_countLe_iff {n : Nat} {t : Fin n → Int} (ht : Monotone t) (r : Int) (i : Fin n) :
    i.val < countLe t r ↔ t i ≤ r := by
  constructor
  · intro hi
    by_contra hti
    have hsub : (Finset.univ.filter fun j => t j ≤ r) ⊆ Finset.Iio i := by
      intro j hj
      rw [Finset.mem_filter] at hj
      rw [Finset.mem_Iio]
      by_contra hji
      exact hti ((ht (not_lt.1 hji)).trans hj.2)
    have := Finset.card_le_card hsub
    rw [Fin.card_Iio] at this
    unfold countLe at hi
    omega
  · intro hti
    have hsub : Finset.Iic i ⊆ (Finset.univ.filter fun j => t j ≤ r) := fun j hj =>
      Finset.mem_filter.2 ⟨Finset.mem_univ j, (ht (Finset.mem_Iic.1 hj)).trans hti⟩
    have := Finset.card_le_card hsub
    rw [Fin.card_Iic] at this
    unfold countLe
    omega

theorem countLe_le {n : Nat} (t : Fin n → Int) (r : Int) : countLe t r ≤ n := by
  unfold countLe
  exact (Finset.card_filter_le _ _).trans (by rw [Finset.card_univ, Fintype.card_fin])

/-- Double Coverage on a sorted configuration of `n + 1` servers. With `c` servers at or left of
`r`: if `c = 0` the leftmost server moves to `r`, if `c = n + 1` the rightmost does, and otherwise
servers `c - 1` and `c` move toward `r` by `min (r - t (c - 1)) (t c - r)`. -/
@[expose]
def dcSorted {n : Nat} (t : Fin (n + 1) → Int) (r : Int) : Fin (n + 1) → Int :=
  let c := countLe t r
  if h0 : c = 0 then Function.update t 0 r
  else if h1 : c = n + 1 then Function.update t (Fin.last n) r
  else
    let a : Fin (n + 1) := ⟨c - 1, by have := countLe_le t r; omega⟩
    let b : Fin (n + 1) := ⟨c, by have := countLe_le t r; omega⟩
    let δ := min (r - t a) (t b - r)
    Function.update (Function.update t a (t a + δ)) b (t b - δ)

/-- Integer pairwise spread (each unordered pair counted twice); equal to `pairSum` on the
line. -/
private def spread {k : Nat} (t : Fin k → Int) : Int := ∑ i, ∑ j, |t i - t j|

private theorem spread_update {k : Nat} (t : Fin k → Int) (a : Fin k) (y : Int) :
    spread (Function.update t a y) =
      spread t + 2 * ∑ j, (|y - Function.update t a y j| - |t a - t j|) := by
  set t' := Function.update t a y
  set g : Fin k → Fin k → Int := fun i j => |t' i - t' j| - |t i - t j|
  have hg0 : ∀ i j, i ≠ a → j ≠ a → g i j = 0 := fun i j hi hj => by
    simp only [g, t', Function.update_of_ne hi, Function.update_of_ne hj, sub_self]
  have hgs : ∀ i j, g i j = g j i := fun i j => by
    simp only [g, abs_sub_comm]
  have hrow : ∀ i, i ≠ a → ∑ j, g i j = g a i := fun i hi => by
    rw [Fintype.sum_eq_single a fun j hj => hg0 i j hi hj, hgs]
  have hdiff : spread t' - spread t = ∑ i, ∑ j, g i j := by
    simp only [spread, g, Finset.sum_sub_distrib]
  have haa : g a a = 0 := by simp only [g, sub_self, abs_zero]
  have hsplit : ∑ i, ∑ j, g i j = 2 * ∑ j, g a j := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a)]
    rw [Finset.sum_congr rfl fun i hi => hrow i (Finset.ne_of_mem_erase hi)]
    rw [Finset.sum_erase _ haa]
    ring
  have hga : ∀ j, g a j = |y - t' j| - |t a - t j| := fun j => by
    simp only [g, t', Function.update_self]
  rw [Finset.sum_congr rfl fun j _ => hga j] at hsplit
  linarith

/-- Moving server `a` to `r` changes the spread by `2 * n * δ` when the distance from every other
server changes by the same `δ`. Shared by `spread_update_zero` and `spread_update_last`. -/
private theorem spread_update_of_forall_eq {n : Nat} (t : Fin (n + 1) → Int) (a : Fin (n + 1))
    {r δ : Int} (h : ∀ j ≠ a, |r - t j| - |t a - t j| = δ) :
    spread (Function.update t a r) = spread t + 2 * (n * δ) := by
  rw [spread_update]
  congr 2
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a)]
  have hrest : ∀ j ∈ Finset.univ.erase a, |r - Function.update t a r j| - |t a - t j| = δ :=
    fun j hj => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
      exact h j (Finset.ne_of_mem_erase hj)
  rw [Finset.sum_congr rfl hrest, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, Fintype.card_fin, Function.update_self]
  simp only [sub_self, abs_zero, add_tsub_cancel_right, nsmul_eq_mul, zero_add]

private theorem spread_update_zero {n : Nat} {t : Fin (n + 1) → Int} (ht : Monotone t) {r : Int}
    (hr : r ≤ t 0) : spread (Function.update t 0 r) = spread t + 2 * (n * (t 0 - r)) :=
  spread_update_of_forall_eq t 0 fun j _ => by
    have := ht (Fin.zero_le j)
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    ring

private theorem spread_update_last {n : Nat} {t : Fin (n + 1) → Int} (ht : Monotone t) {r : Int}
    (hr : t (Fin.last n) ≤ r) :
    spread (Function.update t (Fin.last n) r) = spread t + 2 * (n * (r - t (Fin.last n))) :=
  spread_update_of_forall_eq t (Fin.last n) fun j _ => by
    have := ht (Fin.le_last j)
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    ring

private theorem spread_update_mid {n : Nat} {t : Fin (n + 1) → Int} (ht : Monotone t)
    {a b : Fin (n + 1)}
    (hab : b.val = a.val + 1) {d : Int} (hd : 0 ≤ d) (hdab : 2 * d ≤ t b - t a) :
    spread (Function.update (Function.update t a (t a + d)) b (t b - d)) = spread t - 4 * d := by
  have hne : a ≠ b := fun h => by rw [h] at hab; omega
  set u := Function.update t a (t a + d)
  rw [spread_update, spread_update]
  have hub : u b = t b := Function.update_of_ne (Ne.symm hne) _ _
  have hua : u a = t a + d := Function.update_self _ _ _
  have hab' : t a ≤ t b := ht (Fin.le_iff_val_le_val.2 (by omega))
  have key : ∀ j, (|t a + d - u j| - |t a - t j|) +
      (|t b - d - Function.update u b (t b - d) j| - |u b - u j|) =
        if j = a then -d else if j = b then -d else 0 := by
    intro j
    by_cases hja : j = a
    · subst hja
      rw [ite_eq_left rfl, hua, Function.update_of_ne hne, hua, hub]
      rw [sub_self, abs_zero, sub_self, abs_zero]
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      ring
    by_cases hjb : j = b
    · subst hjb
      rw [ite_eq_right hja, ite_eq_left rfl, hub, Function.update_self]
      rw [sub_self, abs_zero, sub_self, abs_zero, abs_of_nonpos (by linarith),
        abs_of_nonpos (by linarith)]
      ring
    rw [ite_eq_right hja, ite_eq_right hjb]
    have huj : u j = t j := Function.update_of_ne hja _ _
    rw [Function.update_of_ne hjb, huj, hub]
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hja) with hlt | hgt
    · have hj : t j ≤ t a := ht (Fin.le_iff_val_le_val.2 hlt.le)
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith),
        abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      ring
    · have hj : t b ≤ t j := ht (Fin.le_iff_val_le_val.2 (by
        have := Fin.val_ne_of_ne hjb; omega))
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith),
        abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
      ring
  have hsum := Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => key j
  rw [Finset.sum_add_distrib] at hsum
  have hite : ∀ j, (if j = a then -d else if j = b then -d else (0 : Int)) =
      (if j = a then -d else 0) + (if j = b then -d else 0) := fun j => by
    by_cases hja : j = a
    · subst hja
      simp only [↓reduceIte, hne, add_zero]
    · simp only [hja, ↓reduceIte, zero_add]
  rw [Finset.sum_congr rfl fun j _ => hite j, Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ a, Finset.sum_ite_eq' Finset.univ b] at hsum
  simp only [Finset.mem_univ, ↓reduceIte] at hsum
  change spread t + 2 * ∑ j, (|t a + d - u j| - |t a - t j|) + _ = _
  linarith

/-- Uncross an optimal matching so that server `i` is matched to the request `r`. -/
private theorem exists_match_to_request (s o : Fin k → Int) {r : Int} (hr : ∃ j, o j = r)
    (i : Fin k) (hbtw : ∀ a, (r - s a).natAbs = (r - s i).natAbs + (s i - s a).natAbs) :
    ∃ σ, o (σ i) = r ∧ matchCostAlong NatMetric.line s o σ ≤ matchCost NatMetric.line s o := by
  obtain ⟨σ, hσ⟩ := exists_matchCost_eq NatMetric.line s o
  obtain ⟨j, hj⟩ := hr
  set a := σ.symm j
  have ha : o (σ a) = r := by simp only [a, Equiv.apply_symm_apply, hj]
  refine ⟨σ * Equiv.swap a i, ?_, ?_⟩
  · simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_right, ha]
  · rw [hσ]
    refine matchCostAlong_swap_le NatMetric.line s o σ ?_
    rw [ha]
    exact hbtw a

/-- Moving server `i` to `r` after uncrossing lowers the matching distance by the move. -/
private theorem matchCost_update_add_le (s o : Fin k → Int) {r : Int} (hr : ∃ j, o j = r)
    (i : Fin k) (hbtw : ∀ a, (r - s a).natAbs = (r - s i).natAbs + (s i - s a).natAbs) :
    matchCost NatMetric.line (Function.update s i r) o + (s i - r).natAbs ≤
      matchCost NatMetric.line s o := by
  obtain ⟨σ, hσi, hσ⟩ := exists_match_to_request s o hr i hbtw
  have h := matchCostAlong_update_toward NatMetric.line s o σ i r (by
    change (s i - o (σ i)).natAbs = (s i - r).natAbs + (r - o (σ i)).natAbs
    rw [hσi]; omega)
  have h2 := matchCost_le NatMetric.line (Function.update s i r) o σ
  change _ + (s i - r).natAbs = _ at h
  omega

/-- Uncross an optimal matching onto server `i`, given the betweenness only for the server that
the optimal matching sends to `r`. -/
private theorem matchCost_two_moves' (s o : Fin k → Int) {r : Int} (σ : Equiv.Perm (Fin k))
    (hσ : matchCost NatMetric.line s o = matchCostAlong NatMetric.line s o σ) (a₀ : Fin k)
    (ha₀ : o (σ a₀) = r) {i i' : Fin k} (hii : i ≠ i') {y y' : Int}
    (hbtw : (r - s a₀).natAbs = (r - s i).natAbs + (s i - s a₀).natAbs)
    (hy : (s i - r).natAbs = (s i - y).natAbs + (y - r).natAbs)
    (hd : (s i' - y').natAbs ≤ (s i - y).natAbs) :
    matchCost NatMetric.line (Function.update (Function.update s i y) i' y') o ≤
      matchCost NatMetric.line s o := by
  set τ := σ * Equiv.swap a₀ i
  have hτi : o (τ i) = r := by simp only [τ, Equiv.Perm.mul_apply, Equiv.swap_apply_right, ha₀]
  have hτ : matchCostAlong NatMetric.line s o τ ≤ matchCost NatMetric.line s o := by
    rw [hσ]
    refine matchCostAlong_swap_le NatMetric.line s o σ ?_
    rw [ha₀]
    exact hbtw
  have h1 := matchCostAlong_update_toward NatMetric.line s o τ i y (by
    change (s i - o (τ i)).natAbs = (s i - y).natAbs + (y - o (τ i)).natAbs
    rw [hτi]; exact hy)
  have h2 := matchCostAlong_update_le NatMetric.line (Function.update s i y) o τ i' y'
  have h3 := matchCost_le NatMetric.line (Function.update (Function.update s i y) i' y') o τ
  rw [Function.update_of_ne (Ne.symm hii)] at h2
  change _ + (s i - y).natAbs = _ at h1
  change _ ≤ _ + (s i' - y').natAbs at h2
  omega

/-- Middle case of Double Coverage: the two neighbours of `r` move toward it by `d`. -/
private theorem matchCost_mid_le {n : Nat} {t : Fin (n + 1) → Int} (ht : Monotone t)
    (o : Fin (n + 1) → Int) {r : Int} (hr : ∃ j, o j = r) {a b : Fin (n + 1)}
    (hab : b.val = a.val + 1) (hta : t a ≤ r) (htb : r ≤ t b) {d : Int} (hd0 : 0 ≤ d)
    (hda : d ≤ r - t a) (hdb : d ≤ t b - r) :
    matchCost NatMetric.line (Function.update (Function.update t a (t a + d)) b (t b - d)) o ≤
      matchCost NatMetric.line t o := by
  have hne : a ≠ b := fun h => by rw [h] at hab; omega
  obtain ⟨σ, hσ⟩ := exists_matchCost_eq NatMetric.line t o
  obtain ⟨j, hj⟩ := hr
  set a₀ := σ.symm j
  have ha₀ : o (σ a₀) = r := by simp only [a₀, Equiv.apply_symm_apply, hj]
  rcases le_or_gt a₀.val a.val with hle | hgt
  · have h := ht (Fin.le_iff_val_le_val.2 hle)
    exact matchCost_two_moves' t o σ hσ a₀ ha₀ hne (by omega) (by omega) (by omega)
  · have h := ht (Fin.le_iff_val_le_val.2 (show b.val ≤ a₀.val by omega))
    rw [Function.update_comm hne]
    exact matchCost_two_moves' t o σ hσ a₀ ha₀ (Ne.symm hne) (by omega) (by omega) (by omega)

/-- The Double Coverage step inequality on a sorted configuration (doubled, over `ℤ`). -/
private theorem dcSorted_step {n : Nat} {t : Fin (n + 1) → Int} (ht : Monotone t)
    (o : Fin (n + 1) → Int) {r : Int} (hr : ∃ j, o j = r) :
    2 * (moveCost NatMetric.line t (dcSorted t r) : Int) +
        2 * (n + 1) * (matchCost NatMetric.line (dcSorted t r) o : Int) + spread (dcSorted t r) ≤
      2 * (n + 1) * (matchCost NatMetric.line t o : Int) + spread t := by
  unfold dcSorted
  by_cases h0 : countLe t r = 0
  · simp only [h0, ↓reduceDIte]
    have hr0 : r < t 0 := by
      have := (lt_countLe_iff ht r 0).not.1 (by rw [h0]; omega)
      omega
    have hm := matchCost_update_add_le t o hr 0 fun a => by
      have := ht (Fin.zero_le a); omega
    rw [moveCost_update, NatMetric.line_dist, spread_update_zero ht hr0.le]
    have hδ : ((t 0 - r).natAbs : Int) = t 0 - r := by omega
    have hm' : (matchCost NatMetric.line (Function.update t 0 r) o : Int) + (t 0 - r) ≤
        matchCost NatMetric.line t o := by rw [← hδ]; exact_mod_cast hm
    rw [hδ]
    nlinarith
  by_cases h1 : countLe t r = n + 1
  · simp only [h1, Nat.add_one_ne_zero, ↓reduceDIte]
    have hrl : t (Fin.last n) ≤ r := (lt_countLe_iff ht r (Fin.last n)).1 (by
      rw [h1, Fin.val_last]; omega)
    have hm := matchCost_update_add_le t o hr (Fin.last n) fun a => by
      have := ht (Fin.le_last a); omega
    rw [moveCost_update, NatMetric.line_dist, spread_update_last ht hrl]
    have hδ : ((t (Fin.last n) - r).natAbs : Int) = r - t (Fin.last n) := by omega
    have hm' : (matchCost NatMetric.line (Function.update t (Fin.last n) r) o : Int) +
        (r - t (Fin.last n)) ≤ matchCost NatMetric.line t o := by rw [← hδ]; exact_mod_cast hm
    rw [hδ]
    nlinarith
  simp only [h0, h1, ↓reduceDIte]
  have hc := countLe_le t r
  set c := countLe t r
  set a : Fin (n + 1) := ⟨c - 1, by omega⟩
  set b : Fin (n + 1) := ⟨c, by omega⟩
  have hab : b.val = a.val + 1 := by simp only [a, b]; omega
  have hne : a ≠ b := fun h => by rw [h] at hab; omega
  have hta : t a ≤ r := (lt_countLe_iff ht r a).1 (by simp only [a]; omega)
  have htb : r < t b := by
    have := (lt_countLe_iff ht r b).not.1 (by simp only [b]; omega)
    omega
  set d := min (r - t a) (t b - r)
  have hd0 : 0 ≤ d := le_min (by omega) (by omega)
  have hda : d ≤ r - t a := min_le_left _ _
  have hdb : d ≤ t b - r := min_le_right _ _
  have hm := matchCost_mid_le ht o hr hab hta htb.le hd0 hda hdb
  rw [moveCost_update_update NatMetric.line t hne, NatMetric.line_dist, NatMetric.line_dist,
    spread_update_mid ht hab hd0 (by omega)]
  have h1' : |t a - (t a + d)| = d := by rw [abs_of_nonpos (by omega)]; ring
  have h2' : |t b - (t b - d)| = d := by rw [abs_of_nonneg (by omega)]; ring
  simp only [Nat.cast_add, Int.natCast_natAbs]
  rw [h1', h2']
  have hm' : (matchCost NatMetric.line
      (Function.update (Function.update t a (t a + d)) b (t b - d)) o : Int) ≤
        matchCost NatMetric.line t o := by
    exact_mod_cast hm
  nlinarith

/-- Double Coverage on a sorted configuration serves the request. -/
theorem exists_dcSorted_eq {n : Nat} (t : Fin (n + 1) → Int) (r : Int) :
    ∃ i, dcSorted t r i = r := by
  unfold dcSorted
  by_cases h0 : countLe t r = 0
  · simp only [h0, ↓reduceDIte]
    exact ⟨0, Function.update_self _ _ _⟩
  by_cases h1 : countLe t r = n + 1
  · simp only [h1, Nat.add_one_ne_zero, ↓reduceDIte]
    exact ⟨Fin.last n, Function.update_self _ _ _⟩
  simp only [h0, h1, ↓reduceDIte]
  have hc := countLe_le t r
  have hne : (⟨countLe t r - 1, by omega⟩ : Fin (n + 1)) ≠ ⟨countLe t r, by omega⟩ := by
    intro h; rw [Fin.mk.injEq] at h; omega
  rcases min_choice (r - t ⟨countLe t r - 1, by omega⟩) (t ⟨countLe t r, by omega⟩ - r) with h | h
  · refine ⟨⟨countLe t r - 1, by omega⟩, ?_⟩
    rw [Function.update_of_ne hne, Function.update_self, h]
    ring
  · refine ⟨⟨countLe t r, by omega⟩, ?_⟩
    rw [Function.update_self, h]
    ring

private theorem spread_eq_pairSum {k : Nat} (s : Fin k → Int) :
    spread s = (pairSum NatMetric.line s : Int) := by
  unfold spread pairSum
  simp only [Nat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  change |s i - s j| = ((s i - s j).natAbs : Int)
  rw [Int.natCast_natAbs]

/-- Double Coverage on an arbitrary configuration: sort, apply `dcSorted`, unsort. -/
@[expose]
def dcStep {n : Nat} (s : Fin (n + 1) → Int) (r : Int) : Fin (n + 1) → Int :=
  dcSorted (s ∘ Tuple.sort s) r ∘ (Tuple.sort s).symm

/-- Relabeling `dcStep s r` by the sorting permutation of `s` gives the sorted step. -/
theorem dcStep_comp_sort {n : Nat} (s : Fin (n + 1) → Int) (r : Int) :
    dcStep s r ∘ Tuple.sort s = dcSorted (s ∘ Tuple.sort s) r := by
  funext i
  simp only [dcStep, Function.comp_apply, Equiv.symm_apply_apply]

/-- Double Coverage serves the request. -/
theorem exists_dcStep_eq {n : Nat} (s : Fin (n + 1) → Int) (r : Int) :
    ∃ i, dcStep s r i = r := by
  obtain ⟨i, hi⟩ := exists_dcSorted_eq (s ∘ Tuple.sort s) r
  rw [← dcStep_comp_sort] at hi
  exact ⟨Tuple.sort s i, hi⟩

/-- On an already sorted configuration, `dcStep` is `dcSorted`. -/
theorem dcStep_of_monotone {n : Nat} {s : Fin (n + 1) → Int} (hs : Monotone s) (r : Int) :
    dcStep s r = dcSorted s r := by
  rw [dcStep, Tuple.sort_eq_refl_iff_monotone.2 hs]
  rfl

/-! ### The amortized step inequality -/

/-- The doubled amortized step inequality when the offline configuration `o` already covers the
request: `2 * cost_DC + Δ(2 * k * matchCost + pairSum) ≤ 0`. -/
theorem dcStep_amortized {n : Nat} (s o : Fin (n + 1) → Int) {r : Int} (hr : ∃ j, o j = r) :
    2 * moveCost NatMetric.line s (dcStep s r) +
        2 * (n + 1) * matchCost NatMetric.line (dcStep s r) o +
          pairSum NatMetric.line (dcStep s r) ≤
      2 * (n + 1) * matchCost NatMetric.line s o + pairSum NatMetric.line s := by
  have h := dcSorted_step (Tuple.monotone_sort s) o hr
  rw [← dcStep_comp_sort] at h
  simp only [spread_eq_pairSum, pairSum_comp_perm, matchCost_comp_perm, moveCost_comp_perm] at h
  exact_mod_cast h

/-- The doubled amortized step inequality: if the offline schedule moves from `o` to `o'` to serve
`r`, then `2 * cost_DC + Δ(2 * Φ) ≤ 2 * k * cost_OPT` for `2 * Φ = 2 * k * matchCost + pairSum`.
-/
theorem dcStep_amortized_offline {n : Nat} (s o o' : Fin (n + 1) → Int) {r : Int}
    (hr : ∃ j, o' j = r) :
    2 * moveCost NatMetric.line s (dcStep s r) +
        (2 * (n + 1) * matchCost NatMetric.line (dcStep s r) o' +
          pairSum NatMetric.line (dcStep s r)) ≤
      2 * (n + 1) * moveCost NatMetric.line o o' +
        (2 * (n + 1) * matchCost NatMetric.line s o + pairSum NatMetric.line s) := by
  have h1 := dcStep_amortized s o' hr
  have h2 := matchCost_le_add_moveCost NatMetric.line s o o'
  generalize 2 * (n + 1) = K at h1 ⊢
  have h3 := Nat.mul_le_mul_left K h2
  rw [Nat.mul_add] at h3
  omega

/-! ### The strategy and its competitive ratio -/

/-- The Double Coverage strategy for `n + 1` servers on the integer line. -/
@[expose]
def doubleCoverage (n : Nat) : DetStrategy (problem NatMetric.line (n + 1)) where
  Mem := Fin (n + 1) → Int
  ValidMem _ := True
  project s := s
  init s := s
  step s r := dcStep s r
  valid_init _ := ⟨trivial, rfl⟩
  valid_step r _ := ⟨trivial, exists_dcStep_eq _ r⟩

/-- Telescoped doubled potential bound for Double Coverage from configuration `s`, against any
valid offline schedule from `s_off`. -/
theorem doubleCoverage_costFrom_le {n : Nat} (s s_off : Fin (n + 1) → Int) (reqs : List Int)
    (offStates : List (Fin (n + 1) → Int))
    (hv : (problem NatMetric.line (n + 1)).ValidSchedule s_off reqs offStates) :
    2 * (doubleCoverage n).costFrom s reqs ≤
      2 * (n + 1) * (problem NatMetric.line (n + 1)).scheduleCost s_off reqs offStates +
        (2 * (n + 1) * matchCost NatMetric.line s s_off + pairSum NatMetric.line s) := by
  induction hv using Problem.ValidSchedule.induction (P := problem NatMetric.line (n + 1))
    generalizing s with
  | nil => exact (Nat.mul_zero 2).symm ▸ Nat.zero_le _
  | cons s_off r rs o' os hstep _ ih =>
    have hih := ih (dcStep s r)
    have hamort := dcStep_amortized_offline s s_off o' hstep
    change 2 * (moveCost NatMetric.line s (dcStep s r) +
        (doubleCoverage n).costFrom (dcStep s r) rs) ≤
      2 * (n + 1) * (moveCost NatMetric.line s_off o' +
        (problem NatMetric.line (n + 1)).scheduleCost o' rs os) + _
    generalize 2 * (n + 1) = K at hih hamort ⊢
    rw [Nat.mul_add, Nat.mul_add]
    omega

/-- **Chrobak–Karloff–Payne–Vishwanathan.** With `k = n + 1` servers on the line, Double
Coverage from `s₀` costs at most `k` times any valid offline schedule from any `s_off`, plus
`k * matchCost s₀ s_off + Σ_{i<j} |s₀ i - s₀ j|`. -/
theorem doubleCoverage_cost_le {n : Nat} (s₀ s_off : Fin (n + 1) → Int) (reqs : List Int)
    (offStates : List (Fin (n + 1) → Int))
    (hv : (problem NatMetric.line (n + 1)).ValidSchedule s_off reqs offStates) :
    (doubleCoverage n).cost s₀ reqs ≤
      (n + 1) * (problem NatMetric.line (n + 1)).scheduleCost s_off reqs offStates +
        ((n + 1) * matchCost NatMetric.line s₀ s_off + pairSum NatMetric.line s₀ / 2) := by
  have h := doubleCoverage_costFrom_le s₀ s_off reqs offStates hv
  have hc : (doubleCoverage n).cost s₀ reqs = (doubleCoverage n).costFrom s₀ reqs :=
    (doubleCoverage n).cost_eq_costFrom trivial reqs
  rw [hc]
  rw [Nat.mul_assoc 2 (n + 1), Nat.mul_assoc 2 (n + 1)] at h
  generalize (n + 1) * (problem NatMetric.line (n + 1)).scheduleCost s_off reqs offStates = X
    at h ⊢
  generalize (n + 1) * matchCost NatMetric.line s₀ s_off = Y at h ⊢
  omega

/-- **Chrobak–Karloff–Payne–Vishwanathan.** Double Coverage with `k = n + 1` servers on the line
is `k`-competitive from every initial configuration `s₀`, with additive constant
`pairSum s₀ / 2 = Σ_{i<j} |s₀ i - s₀ j|`. -/
theorem doubleCoverage_isCompetitiveFrom {n : Nat} (s₀ : Fin (n + 1) → Int) :
    (doubleCoverage n).IsCompetitiveFrom s₀ (n + 1) (pairSum NatMetric.line s₀ / 2) := by
  intro reqs offStates hv
  have h := doubleCoverage_cost_le s₀ s₀ reqs offStates hv
  rw [matchCost_self, Nat.mul_zero, Nat.zero_add] at h
  exact h

/-- Double Coverage's cost on a nonempty request sequence: the first step plus the rest. -/
theorem doubleCoverage_cost_cons {n : Nat} (s₀ : Fin (n + 1) → Int) (r : Int)
    (rs : List Int) :
    (doubleCoverage n).cost s₀ (r :: rs) =
      moveCost NatMetric.line s₀ (dcStep s₀ r) + (doubleCoverage n).cost (dcStep s₀ r) rs :=
  rfl

@[simp]
theorem doubleCoverage_cost_nil {n : Nat} (s₀ : Fin (n + 1) → Int) :
    (doubleCoverage n).cost s₀ [] = 0 :=
  rfl

end Cslib.DataStructure.KServer
