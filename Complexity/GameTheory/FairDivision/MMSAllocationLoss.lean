/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.GameTheory.FairDivision.MMSAsymptotic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity

/-!
# Allocation structure in the asymptotic MMS construction

The structural steps of [EzraGarbuz2027], Proposition 8 (PDF pp. 9–12).
All bundles below are fibers of complete allocations of the actual item type.

## Main results

- `allocation_label_distance`: equal-weight allocations with corrections at least -l
  force the P/Q recipients' one-sided label distance to be at most 5l.
- `universal_goods_loss`: every goods allocation loses more than l below exact MMS
  when the actual label sets have distance greater than 5l.
- `universal_chores_loss`: the reversed-correction chores construction forces cost
  more than l above exact MMS under the same label-distance condition.
-/

public section

open scoped BigOperators

namespace Cslib.FairDivision.MMSAsymptotic

private abbrev P (k d : ℕ) : HighGood k d := .inr (.inl 0)
private abbrev Q (k d : ℕ) : HighGood k d := .inr (.inl 1)

private def lows {k d : ℕ} (a : Allocation k d) (i : HighGood k d) : Finset (LowGood k) :=
  Finset.univ.filter fun g => a (.inl g) = i

private theorem fiber_sum {k d : ℕ} (a : Allocation k d) (i : HighGood k d)
    (f : Good k d → ℤ) :
    (∑ g ∈ bundle k d a i, f g) =
      (∑ g ∈ lows a i, f (.inl g)) +
      ∑ h : HighGood k d, if a (.inr h) = i then f (.inr h) else 0 := by
  simp only [bundle, lows, Finset.sum_filter, Fintype.sum_sum_type]

private theorem fixed_fiber {k d : ℕ} (a : Allocation k d)
    (ha : ∀ h, a (.inr h) = h) (i : HighGood k d) (f : Good k d → ℤ) :
    (∑ g ∈ bundle k d a i, f g) = (∑ g ∈ lows a i, f (.inl g)) + f (.inr i) := by
  rw [fiber_sum]
  simp [ha]

private theorem low_weight_fixed {k d : ℕ} (a : Allocation k d)
    (ha : ∀ h, a (.inr h) = h)
    (hw : ∀ i, (∑ g ∈ bundle k d a i, (weight k d g : ℤ)) = 68 * (k : ℤ) ^ 3)
    (i : HighGood k d) :
    (∑ g ∈ lows a i, (lowWeight k g : ℤ)) = 68 * (k : ℤ) ^ 3 - weight k d (.inr i) := by
  have h := hw i
  rw [fixed_fiber a ha] at h
  exact eq_sub_of_add_eq h

private theorem z_lows {k d : ℕ} (hk : 0 < k) (a : Allocation k d)
    (ha : ∀ h, a (.inr h) = h)
    (hw : ∀ i, (∑ g ∈ bundle k d a i, (weight k d g : ℤ)) = 68 * (k : ℤ) ^ 3)
    (j : Fin (2 * k)) :
    (∃ h : Fin k, lows a (.inl j) = {Sum.inr (Sum.inr h)}) ∨
      ∃ t : Fin (2 * k), lows a (.inl j) = {Sum.inl t, Sum.inr (Sum.inl t)} := by
  apply (low_bundle_rigidity k hk _).mp
  have h := low_weight_fixed a ha hw (.inl j)
  have hs : 17 * k * k ≤ 68 * k * k * k := by nlinarith [Nat.mul_le_mul_left (k * k) hk]
  simp only [weight, Nat.cast_sub hs] at h
  push_cast at h
  have he : (∑ g ∈ lows a (.inl j), (lowWeight k g : ℤ)) = 17 * k * k := by
    nlinarith [h]
  exact_mod_cast he

private theorem d_lows {k d : ℕ} (hk : 0 < k) (a : Allocation k d)
    (ha : ∀ h, a (.inr h) = h)
    (hw : ∀ i, (∑ g ∈ bundle k d a i, (weight k d g : ℤ)) = 68 * (k : ℤ) ^ 3)
    (j : Fin d) : lows a (.inr (.inr j)) = ∅ := by
  have h := low_weight_fixed a ha hw (.inr (.inr j))
  simp only [weight] at h
  push_cast at h
  have hz : (∑ g ∈ lows a (.inr (.inr j)), (lowWeight k g : ℤ)) = 0 := by nlinarith
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro g hg
  have hp : ∀ t ∈ lows a (.inr (.inr j)), (0 : ℤ) ≤ lowWeight k t := by intros; positivity
  have hl := Finset.single_le_sum hp hg
  have hr := (lowWeight_range k g).1
  have hr' : 6 * (k : ℤ) * k ≤ lowWeight k g := by exact_mod_cast hr
  have hk' : (0 : ℤ) < k := by exact_mod_cast hk
  nlinarith

/-- Outside the two distinguished bundles, X and Y of the same label must be
allocated together. This follows from low-bundle rigidity, not an allocation premise. -/
private theorem matched_outside_distinguished {k d : ℕ} (hk : 0 < k) (a : Allocation k d)
    (ha : ∀ h, a (.inr h) = h)
    (hw : ∀ i, (∑ g ∈ bundle k d a i, (weight k d g : ℤ)) = 68 * (k : ℤ) ^ 3)
    (j : Fin (2 * k)) :
    (a (.inl (.inl j)) = P k d ∨ a (.inl (.inl j)) = Q k d) ↔
      (a (.inl (.inr (.inl j))) = P k d ∨ a (.inl (.inr (.inl j))) = Q k d) := by
  have hz (t : Fin (2 * k)) :
      a (.inl (.inl j)) = .inl t ↔ a (.inl (.inr (.inl j))) = .inl t := by
    have h := z_lows hk a ha hw t
    have hx : a (.inl (.inl j)) = .inl t ↔ Sum.inl j ∈ lows a (.inl t) := by simp [lows]
    have hy : a (.inl (.inr (.inl j))) = .inl t ↔ Sum.inr (Sum.inl j) ∈ lows a (.inl t) := by
      simp [lows]
    rw [hx, hy]
    rcases h with ⟨s, hs⟩ | ⟨s, hs⟩ <;> simp [hs, eq_comm]
  have hd (t : Fin d) : a (.inl (.inl j)) ≠ .inr (.inr t) ∧
      a (.inl (.inr (.inl j))) ≠ .inr (.inr t) := by
    have h := d_lows hk a ha hw t
    have hx : Sum.inl j ∉ lows a (.inr (.inr t)) := by simp [h]
    have hy : Sum.inr (Sum.inl j) ∉ lows a (.inr (.inr t)) := by simp [h]
    simpa [lows] using And.intro hx hy
  rcases hx : a (.inl (.inl j)) with x | x | x
  · have hy := (hz x).mp hx
    simp [hy, P, Q]
  · fin_cases x <;> simp only [P, Q] <;>
      rcases hy : a (.inl (.inr (.inl j))) with y | y | y
    all_goals first
      | exact False.elim (by have := (hz y).mpr hy; simp [hx] at this)
      | exact False.elim ((hd y).2 hy)
      | fin_cases y <;> simp
  · exact False.elim ((hd x).1 hx)

private def xs {k d : ℕ} (a : Allocation k d) (i : HighGood k d) : Finset (Fin (2 * k)) :=
  Finset.univ.filter fun j => a (.inl (.inl j)) = i

private def ys {k d : ℕ} (a : Allocation k d) (i : HighGood k d) : Finset (Fin (2 * k)) :=
  Finset.univ.filter fun j => a (.inl (.inr (.inl j))) = i

private def gs {k d : ℕ} (a : Allocation k d) (i : HighGood k d) : Finset (Fin k) :=
  Finset.univ.filter fun j => a (.inl (.inr (.inr j))) = i

private theorem low_sum {k d : ℕ} (a : Allocation k d) (i : HighGood k d)
    (f : LowGood k → ℤ) :
    (∑ g ∈ lows a i, f g) = (∑ j ∈ xs a i, f (.inl j)) +
      (∑ j ∈ ys a i, f (.inr (.inl j))) + (∑ j ∈ gs a i, f (.inr (.inr j))) := by
  simp only [lows, xs, ys, gs, Finset.sum_filter, Fintype.sum_sum_type]
  omega

private theorem correction_fixed {k d : ℕ} (a : Allocation k d)
    (ha : ∀ h, a (.inr h) = h) (S : Finset (Fin (2 * k))) (i : HighGood k d) :
    (∑ g ∈ bundle k d a i, correction k d S g) =
      ((ys a i ∩ S).card : ℤ) - (xs a i \ S).card - (gs a i).card + correction k d S (.inr i) := by
  rw [fixed_fiber a ha, low_sum]
  simp only [correction, Finset.sum_ite, Finset.sum_const_zero, zero_add,
    Finset.sum_const, nsmul_eq_mul, mul_neg, mul_one, add_zero]
  have hx : (xs a i).filter (fun j => j ∉ S) = xs a i \ S := by ext; simp
  have hy : (ys a i).filter (fun j => j ∈ S) = ys a i ∩ S := by ext; simp
  rw [hx, hy]
  ring

private theorem y_range (k : ℕ) (j : Fin (2 * k)) :
    0 ≤ (17 * k * k - k * (6 * k + j.val) : ℕ) ∧
      (17 * k * k - k * (6 * k + j.val) : ℕ) ≤ 11 * k * k := by
  have hj := j.isLt
  constructor
  · omega
  · have hx : 6 * k * k ≤ k * (6 * k + j.val) := by nlinarith
    have he : 17 * k * k = 6 * k * k + 11 * k * k := by ring
    omega

private theorem sum_y {k : ℕ} (S : Finset (Fin (2 * k))) (hS : S.card = k)
    (hU : (∑ j ∈ S, k * (6 * k + j.val)) = 7 * k * k * k - k * k / 2) :
    (∑ j ∈ S, ((17 * k * k - k * (6 * k + j.val) : ℕ) : ℤ)) =
      17 * (k : ℤ) ^ 3 - ((7 * k * k * k - k * k / 2 : ℕ) : ℤ) := by
  have he (j : Fin (2 * k)) : k * (6 * k + j.val) ≤ 17 * k * k := by nlinarith [j.isLt]
  simp only [Nat.cast_sub (he _), Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add,
    Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  have hu : (∑ j ∈ S, (k : ℤ) * (6 * k + j.val)) = ((7 * k * k * k - k * k / 2 : ℕ) : ℤ) := by
    exact_mod_cast hU
  rw [hS, hu]
  ring

private theorem q_x_count {k d : ℕ} (a : Allocation k d)
    (ha : ∀ h, a (.inr h) = h)
    (hw : ∀ i, (∑ g ∈ bundle k d a i, (weight k d g : ℤ)) = 68 * (k : ℤ) ^ 3)
    (hk : 0 < k) (S : Finset (Fin (2 * k))) (hS : S.card = k)
    (hU : (∑ j ∈ S, k * (6 * k + j.val)) = 7 * k * k * k - k * k / 2) :
    (xs a (Q k d)).card ≤ 2 * (S \ ys a (Q k d)).card := by
  let Y : Fin (2 * k) → ℤ := fun j => (17 * k * k - k * (6 * k + j.val) : ℕ)
  have hq := low_weight_fixed a ha hw (Q k d)
  rw [low_sum] at hq
  have hy := sum_y S hS hU
  have hsel : (∑ j ∈ S ∩ ys a (Q k d), Y j) ≤ ∑ j ∈ ys a (Q k d), Y j :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
      (by intros; dsimp only [Y]; positivity)
  have hsplit : (∑ j ∈ S ∩ ys a (Q k d), Y j) +
      (∑ j ∈ S \ ys a (Q k d), Y j) = ∑ j ∈ S, Y j := by
    exact Finset.sum_inter_add_sum_sdiff S (ys a (Q k d)) Y
  have hmissing : (∑ j ∈ S \ ys a (Q k d), Y j) ≤
      (S \ ys a (Q k d)).card * (11 * (k : ℤ) * k) := by
    calc
      _ ≤ ∑ _j ∈ S \ ys a (Q k d), 11 * (k : ℤ) * k :=
        Finset.sum_le_sum fun j _ => by dsimp only [Y]; exact_mod_cast (y_range k j).2
      _ = _ := by simp
  have hx : (xs a (Q k d)).card * (6 * (k : ℤ) * k) ≤
      ∑ j ∈ xs a (Q k d), (k : ℤ) * (6 * k + j.val) := by
    calc
      _ = ∑ _j ∈ xs a (Q k d), 6 * (k : ℤ) * k := by simp
      _ ≤ _ := Finset.sum_le_sum fun j _ => by nlinarith [Nat.cast_nonneg (α := ℤ) j.val]
  have hg : (0 : ℤ) ≤ ∑ _j ∈ gs a (Q k d), (17 * k * k : ℕ) := by positivity
  simp only [Q, weight, lowWeight, Fin.val_one, Nat.one_ne_zero, ite_false] at hq
  push_cast at hq hg
  change (∑ j ∈ S, Y j) = _ at hy
  have hk' : (0 : ℤ) < k := by exact_mod_cast hk
  have hh : (xs a (Q k d)).card * (6 * (k : ℤ) * k) ≤
      (S \ ys a (Q k d)).card * (11 * (k : ℤ) * k) := by
    change (∑ j ∈ S ∩ ys a (Q k d), Y j) ≤ _ at hsel
    dsimp only [Y] at hsel hsplit
    nlinarith [hq, hy]
  have he : ((xs a (Q k d)).card : ℤ) ≤ 2 * (S \ ys a (Q k d)).card := by
    nlinarith [sq_pos_of_pos hk']
  exact_mod_cast he

private theorem distinguished_y_count {k d : ℕ} (hk : 0 < k) (a : Allocation k d)
    (ha : ∀ h, a (.inr h) = h)
    (hw : ∀ i, (∑ g ∈ bundle k d a i, (weight k d g : ℤ)) = 68 * (k : ℤ) ^ 3) :
    (ys a (P k d)).card + (ys a (Q k d)).card ≤ k := by
  have hpair (j : Fin (2 * k)) := matched_outside_distinguished hk a ha hw j
  have he (j : Fin (2 * k)) :
      (if a (.inl (.inl j)) = P k d then (k * (6 * k + j.val) : ℤ) else 0) +
      (if a (.inl (.inl j)) = Q k d then (k * (6 * k + j.val) : ℤ) else 0) +
      (if a (.inl (.inr (.inl j))) = P k d then
        ((17 * k * k - k * (6 * k + j.val) : ℕ) : ℤ) else 0) +
      (if a (.inl (.inr (.inl j))) = Q k d then
        ((17 * k * k - k * (6 * k + j.val) : ℕ) : ℤ) else 0) =
      17 * (k : ℤ) * k * ((if a (.inl (.inr (.inl j))) = P k d then 1 else 0) +
        (if a (.inl (.inr (.inl j))) = Q k d then 1 else 0)) := by
    have hx : k * (6 * k + j.val) ≤ 17 * k * k := by nlinarith [j.isLt]
    have hh := hpair j
    have hpq : P k d ≠ Q k d := by simp [P, Q]
    rw [Nat.cast_sub hx]
    push_cast
    by_cases hxp : a (.inl (.inl j)) = P k d <;>
      by_cases hxq : a (.inl (.inl j)) = Q k d <;>
      by_cases hyp : a (.inl (.inr (.inl j))) = P k d <;>
      by_cases hyq : a (.inl (.inr (.inl j))) = Q k d <;>
      simp_all
  have hes := congrArg (fun f : Fin (2 * k) → ℤ => ∑ j, f j) (funext he)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hes
  have hy (i : HighGood k d) :
      (∑ j : Fin (2 * k), if a (.inl (.inr (.inl j))) = i then (1 : ℤ) else 0) = (ys a i).card := by
    simp [ys]
  rw [hy, hy] at hes
  have hP := low_weight_fixed a ha hw (P k d)
  have hQ := low_weight_fixed a ha hw (Q k d)
  rw [low_sum] at hP hQ
  have hu : 7 * k * k * k - k * k / 2 ≤ 68 * k * k * k := by
    have := Nat.sub_le (7 * k * k * k) (k * k / 2)
    nlinarith
  simp only [P, Q, weight, Fin.val_zero, Fin.val_one, ite_true, ite_false,
    Nat.one_ne_zero, Nat.cast_sub hu] at hP hQ
  push_cast at hP hQ
  simp only [lowWeight, xs, ys, Finset.sum_filter] at hP hQ
  push_cast at hP hQ
  have hg (i : HighGood k d) : (0 : ℤ) ≤ ∑ _j ∈ gs a i, (17 * k * k : ℕ) := by positivity
  have hgp := hg (P k d)
  have hgq := hg (Q k d)
  push_cast at hgp hgq
  have hk' : (0 : ℤ) < k := by exact_mod_cast hk
  have hb : ((ys a (P k d)).card : ℤ) + (ys a (Q k d)).card ≤ k := by
    nlinarith [sq_pos_of_pos hk']
  exact_mod_cast hb

private theorem sdiff_bound {α : Type*} [DecidableEq α] (S X Y : Finset α) :
    (S \ X).card ≤ (S \ (X ∪ Y)).card + Y.card := by
  calc
    _ ≤ ((S \ (X ∪ Y)) ∪ Y).card := Finset.card_le_card (by intro j hj; simp_all; tauto)
    _ ≤ _ := Finset.card_union_le _ _

/-- Proposition 8's distance estimate on the forced, equal-weight allocation
structure. The premises describe actual item fibers, without assuming any loss. -/
theorem allocation_label_distance {k d : ℕ} (hk : 0 < k) (a : Allocation k d)
    (ha : ∀ h, a (.inr h) = h)
    (hw : ∀ i, (∑ g ∈ bundle k d a i, (weight k d g : ℤ)) = 68 * (k : ℤ) ^ 3)
    (S : HighGood k d → Finset (Fin (2 * k)))
    (hS : ∀ i, (S i).card = k)
    (hU : ∀ i, (∑ j ∈ S i, k * (6 * k + j.val)) = 7 * k * k * k - k * k / 2)
    (l : ℤ)
    (hc : ∀ i, -l ≤ ∑ g ∈ bundle k d a i, correction k d (S i) g) :
    (((S (.inr (.inl 1))) \ S (.inr (.inl 0))).card : ℤ) ≤ 5 * l := by
  let p := P k d
  let q := Q k d
  let missing := S q \ ys a q
  have hpart : (ys a q ∩ S q).card + missing.card = k := by
    simpa only [missing, Finset.inter_comm, hS] using
      Finset.card_inter_add_card_sdiff (S q) (ys a q)
  have hcq := hc q
  rw [correction_fixed a ha] at hcq
  change - l ≤ ((ys a q ∩ S q).card : ℤ) - (xs a q \ S q).card - (gs a q).card - k at hcq
  have hd : (missing.card : ℤ) ≤ l := by omega
  have hx := q_x_count a ha hw hk (S q) (hS q) (hU q)
  change (xs a q).card ≤ 2 * missing.card at hx
  have hxy := distinguished_y_count hk a ha hw
  have hY : ((ys a p).card : ℤ) ≤ missing.card := by
    have hi := Finset.card_le_card (Finset.inter_subset_left : ys a q ∩ S q ⊆ ys a q)
    change (ys a p).card + (ys a q).card ≤ k at hxy
    omega
  have hcp := hc p
  rw [correction_fixed a ha] at hcp
  change - l ≤ ((ys a p ∩ S p).card : ℤ) - (xs a p \ S p).card - (gs a p).card + 0 at hcp
  have hi := Finset.card_le_card (Finset.inter_subset_left : ys a p ∩ S p ⊆ ys a p)
  have hbad : ((xs a p \ S p).card : ℤ) ≤ missing.card + l := by omega
  have hmiss : (S q \ (xs a p ∪ xs a q)).card ≤ missing.card := by
    apply Finset.card_le_card
    intro j hj
    dsimp only [missing]
    have hm := matched_outside_distinguished hk a ha hw j
    simp only [Finset.mem_sdiff, Finset.mem_union, xs, ys, Finset.mem_filter,
      Finset.mem_univ, true_and, not_or] at hj ⊢
    exact ⟨hj.1, fun hy => (hm.mpr (Or.inr hy)).elim hj.2.1 hj.2.2⟩
  have hs := sdiff_bound (S q) (xs a p) (xs a q)
  have hdist : (S q \ S p).card ≤ (S q \ xs a p).card + (xs a p \ S p).card := by
    calc
      _ ≤ ((S q \ xs a p) ∪ (xs a p \ S p)).card :=
        Finset.card_le_card (by
          intro j hj
          simp_all only [Finset.mem_sdiff, Finset.mem_union]
          tauto)
      _ ≤ _ := Finset.card_union_le _ _
  change (((S q) \ S p).card : ℤ) ≤ _
  omega

private theorem low_correction_le {k d : ℕ} (a : Allocation k d)
    (i : HighGood k d) (S : Finset (Fin (2 * k))) (hS : S.card = k) :
    (∑ g ∈ lows a i, correction k d S (.inl g)) ≤ k := by
  rw [low_sum]
  simp only [correction, Finset.sum_ite, Finset.sum_const_zero, zero_add,
    Finset.sum_const, nsmul_eq_mul, mul_neg, mul_one, add_zero]
  have hy : ((ys a i).filter (fun j => j ∈ S)).card ≤ k := by
    exact (Finset.card_le_card (by intro j hj; exact (Finset.mem_filter.mp hj).2)).trans_eq hS
  omega

private theorem high_weight_lower (k d : ℕ) (hk : 0 < k) (h : HighGood k d) :
    51 * (k : ℤ) ^ 3 ≤ weight k d (.inr h) := by
  have hk' : (1 : ℤ) ≤ k := by exact_mod_cast hk
  have hk2 : (k : ℤ) ^ 2 ≤ (k : ℤ) ^ 3 := by nlinarith [sq_nonneg (k : ℤ)]
  rcases h with j | j | j
  · have hs : 17 * k * k ≤ 68 * k * k * k := by nlinarith [Nat.mul_le_mul_left (k * k) hk]
    simp only [weight, Nat.cast_sub hs]
    push_cast
    nlinarith
  · have hu : 7 * k * k * k - k * k / 2 ≤ 68 * k * k * k := by
      have := Nat.sub_le (7 * k * k * k) (k * k / 2)
      nlinarith
    have hb : ((7 * k * k * k - k * k / 2 : ℕ) : ℤ) ≤ 7 * (k : ℤ) ^ 3 := by
      have := Nat.sub_le (7 * k * k * k) (k * k / 2)
      exact_mod_cast (show 7 * k * k * k - k * k / 2 ≤ 7 * k ^ 3 by nlinarith)
    simp only [weight]
    split_ifs
    · rw [Nat.cast_sub hu]
      push_cast
      nlinarith
    · push_cast
      nlinarith [Nat.cast_nonneg (α := ℤ) (7 * k * k * k - k * k / 2)]
  · simp only [weight]
    push_cast
    nlinarith

private theorem goods_high_surjective {k d : ℕ} (hk : 0 < k) (a : Allocation k d)
    (S : HighGood k d → Finset (Fin (2 * k))) (hS : ∀ i, (S i).card = k)
    (l : ℤ) (hl : l < k)
    (hv : ∀ i, 204 * (k : ℤ) ^ 3 - l ≤ ∑ g ∈ bundle k d a i, goodsValue k d (S i) g) :
    Function.Surjective (fun h : HighGood k d => a (.inr h)) := by
  intro i
  by_contra hn
  have hnone : ∀ h, a (.inr h) ≠ i := by simpa only [not_exists] using hn
  have hc := low_correction_le a i (S i) (hS i)
  have hw : (∑ g ∈ lows a i, (lowWeight k g : ℤ)) ≤ 51 * (k : ℤ) ^ 3 := by
    have h := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ (lows a i)) (f := fun g => (lowWeight k g : ℤ)) (by intros; positivity)
    have ht : (∑ g : LowGood k, (lowWeight k g : ℤ)) = 51 * (k : ℤ) ^ 3 := by
      rw [← Nat.cast_sum, lowWeight_total]
      push_cast
      ring
    exact h.trans ht.le
  have h := hv i
  rw [fiber_sum] at h
  simp only [hnone, ite_false, Finset.sum_const_zero, add_zero, goodsValue,
    Finset.sum_add_distrib, ← Finset.mul_sum] at h
  change 204 * (k : ℤ) ^ 3 - l ≤ 3 * (∑ g ∈ lows a i, (lowWeight k g : ℤ)) + _ at h
  have hk' : (1 : ℤ) ≤ k := by exact_mod_cast hk
  have hcub : (k : ℤ) ≤ (k : ℤ) ^ 3 := by nlinarith [sq_nonneg ((k : ℤ) - 1)]
  nlinarith

private theorem chores_high_injective {k d : ℕ} (hk : 0 < k) (a : Allocation k d)
    (S : HighGood k d → Finset (Fin (2 * k))) (l : ℤ) (hl : l < k)
    (hv : ∀ i, (∑ g ∈ bundle k d a i, choreCost k d (S i) g) ≤ 204 * (k : ℤ) ^ 3 + l) :
    Function.Injective (fun h : HighGood k d => a (.inr h)) := by
  intro h j he
  by_contra hn
  let i := a (.inr h)
  have hsub : {Sum.inr h, Sum.inr j} ⊆ bundle k d a i := by
    intro g hg
    simp only [Finset.mem_insert, Finset.mem_singleton] at hg
    rcases hg with rfl | rfl <;> simp [bundle, i, he]
  have hb := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (f := choreCost k d (S i)) (by intro g _ _; exact (choreCost_pos k d hk (S i) g).le)
  rw [Finset.sum_pair (by simpa using hn)] at hb
  have hh := high_weight_lower k d hk h
  have hj := high_weight_lower k d hk j
  have ch := (correction_bounds k d hk (S i) (.inr h)).2
  have cj := (correction_bounds k d hk (S i) (.inr j)).2
  have hi := hv i
  have hk' : (1 : ℤ) ≤ k := by exact_mod_cast hk
  have hcub : (k : ℤ) ≤ (k : ℤ) ^ 3 := by nlinarith [sq_nonneg ((k : ℤ) - 1)]
  change _ ≤ ∑ g ∈ bundle k d a i, choreCost k d (S i) g at hb
  simp only [choreCost] at hb hi
  nlinarith

private theorem weight_dvd {k d : ℕ} (S : Finset (Fin (2 * k)))
    (hU : (∑ j ∈ S, k * (6 * k + j.val)) = 7 * k * k * k - k * k / 2) (g : Good k d) :
    k ∣ weight k d g := by
  have hu : k ∣ 7 * k * k * k - k * k / 2 := by
    rw [← hU]
    exact Finset.dvd_sum fun j _ => dvd_mul_right k _
  have h17 : k ∣ 17 * k * k := by exact dvd_mul_of_dvd_left (dvd_mul_left k 17) k
  have h68 : k ∣ 68 * k * k * k := by
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_left k 68) k) k
  rcases g with (j | j | j) | j | j | j
  · exact dvd_mul_right k _
  · exact Nat.dvd_sub h17 (dvd_mul_right k _)
  · exact h17
  · exact Nat.dvd_sub h68 h17
  · simp only [weight]
    split_ifs
    · exact Nat.dvd_sub h68 hu
    · exact dvd_add (by exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_left k 51) k) k) hu
  · exact h68

private theorem fixed_correction_le {k d : ℕ} (a : Allocation k d)
    (ha : ∀ h, a (.inr h) = h) (S : Finset (Fin (2 * k))) (hS : S.card = k)
    (hk : 0 < k) (i : HighGood k d) :
    (∑ g ∈ bundle k d a i, correction k d S g) ≤ k + 1 := by
  rw [fixed_fiber a ha]
  have := low_correction_le a i S hS
  have := (correction_bounds k d hk S (.inr i)).2
  omega

private theorem fixed_weights {k d : ℕ} (hk : 0 < k) (a : Allocation k d)
    (ha : ∀ h, a (.inr h) = h)
    (S : HighGood k d → Finset (Fin (2 * k))) (hS : ∀ i, (S i).card = k)
    (hU : ∀ i, (∑ j ∈ S i, k * (6 * k + j.val)) = 7 * k * k * k - k * k / 2)
    (l : ℤ) (hl : l < k)
    (hv : (∀ i, 204 * (k : ℤ) ^ 3 - l ≤ ∑ g ∈ bundle k d a i, goodsValue k d (S i) g) ∨
      (∀ i, (∑ g ∈ bundle k d a i, choreCost k d (S i) g) ≤ 204 * (k : ℤ) ^ 3 + l)) :
    ∀ i, (∑ g ∈ bundle k d a i, (weight k d g : ℤ)) = 68 * (k : ℤ) ^ 3 := by
  let W := fun i => ∑ g ∈ bundle k d a i, (weight k d g : ℤ)
  have hd (i) : (k : ℤ) ∣ W i := by
    apply Finset.dvd_sum
    intro g _
    exact_mod_cast weight_dvd (S (P k d)) (hU _) g
  have ht : (∑ i, W i) = (Fintype.card (HighGood k d) : ℤ) * (68 * (k : ℤ) ^ 3) := by
    rw [allocation_total k d, ← Nat.cast_sum, weight_total]
    simp only [HighGood, Fintype.card_sum, Fintype.card_fin]
    push_cast
    ring
  have hstep (i) := fixed_correction_le a ha (S i) (hS i) hk i
  have hk' : (0 : ℤ) < k := by exact_mod_cast hk
  have htar : (k : ℤ) ∣ 68 * (k : ℤ) ^ 3 :=
    dvd_mul_of_dvd_right (dvd_pow_self (k : ℤ) (by decide : 3 ≠ 0)) 68
  have heq (hb : ∀ i, 68 * (k : ℤ) ^ 3 ≤ W i) : ∀ i, W i = 68 * (k : ℤ) ^ 3 := by
    intro i
    have hh := Finset.sum_eq_sum_iff_of_le (s := Finset.univ) (fun j _ => hb j)
    have hs : (∑ _i : HighGood k d, 68 * (k : ℤ) ^ 3) = ∑ i, W i := by simpa using ht.symm
    exact ((hh.mp hs) i (Finset.mem_univ i)).symm
  rcases hv with hv | hv
  · apply heq
    intro i
    by_contra hn
    have hv := hv i
    simp only [goodsValue, Finset.sum_add_distrib, ← Finset.mul_sum] at hv
    have hh : k ≤ 68 * (k : ℤ) ^ 3 - W i :=
      Int.le_of_dvd (by omega) (dvd_sub htar (hd i))
    change 204 * (k : ℤ) ^ 3 - l ≤ 3 * W i + _ at hv
    have hc := hstep i
    nlinarith
  · have hb (i) : W i ≤ 68 * (k : ℤ) ^ 3 := by
      by_contra hn
      have hv := hv i
      simp only [choreCost, Finset.sum_sub_distrib, ← Finset.mul_sum] at hv
      have hh : k ≤ W i - 68 * (k : ℤ) ^ 3 :=
        Int.le_of_dvd (by omega) (dvd_sub (hd i) htar)
      change 3 * W i - _ ≤ 204 * (k : ℤ) ^ 3 + l at hv
      have hc := hstep i
      nlinarith
    intro i
    have hh := Finset.sum_eq_sum_iff_of_le (s := Finset.univ) (fun j _ => hb j)
    have hs : (∑ i, W i) = ∑ _i : HighGood k d, 68 * (k : ℤ) ^ 3 := by simpa using ht
    exact (hh.mp hs) i (Finset.mem_univ i)

private theorem reindex_bundle {k d : ℕ} (a : Allocation k d) (e : HighGood k d ≃ HighGood k d)
    (i : HighGood k d) : bundle k d (e.symm ∘ a) i = bundle k d a (e i) := by
  ext g
  simp [bundle, Equiv.symm_apply_eq]

/-- Proposition 8, with its distance/loss tradeoff explicit: every allocation of
these actual goods loses more than l for some agent whenever distinct label sets
are more than 5l apart. No universal allocation-loss premise is used. -/
theorem universal_goods_loss {k d : ℕ} (hk : 0 < k)
    (S : HighGood k d → Finset (Fin (2 * k))) (hS : ∀ i, (S i).card = k)
    (hU : ∀ i, (∑ j ∈ S i, k * (6 * k + j.val)) = 7 * k * k * k - k * k / 2)
    (l : ℤ) (hl : l < k)
    (hdist : ∀ i j, i ≠ j → 5 * l < ((S i \ S j).card : ℤ))
    (a : Allocation k d) :
    ∃ i, (∑ g ∈ bundle k d a i, goodsValue k d (S i) g) < 204 * (k : ℤ) ^ 3 - l := by
  classical
  by_contra hn
  have hv : ∀ i, 204 * (k : ℤ) ^ 3 - l ≤ ∑ g ∈ bundle k d a i, goodsValue k d (S i) g := by
    simpa only [not_exists, not_lt] using hn
  have hsurj := goods_high_surjective hk a S hS l hl hv
  let e := Equiv.ofBijective (fun h : HighGood k d => a (.inr h))
    ⟨Finite.injective_iff_surjective.mpr hsurj, hsurj⟩
  let b : Allocation k d := e.symm ∘ a
  have hb : ∀ h, b (.inr h) = h := fun h => e.symm_apply_apply h
  have hv' : ∀ i, 204 * (k : ℤ) ^ 3 - l ≤ ∑ g ∈ bundle k d b i, goodsValue k d (S (e i)) g := by
    intro i
    rw [reindex_bundle]
    exact hv (e i)
  have hw := fixed_weights hk b hb (S ∘ e) (fun i => hS (e i)) (fun i => hU (e i)) l hl (Or.inl hv')
  have hc : ∀ i, -l ≤ ∑ g ∈ bundle k d b i, correction k d (S (e i)) g := by
    intro i
    have h := hv' i
    simp only [goodsValue, Finset.sum_add_distrib, ← Finset.mul_sum] at h
    rw [hw i] at h
    nlinarith
  have hbound := allocation_label_distance hk b hb hw (S ∘ e)
    (fun i => hS (e i)) (fun i => hU (e i)) l hc
  have hne : e (Q k d) ≠ e (P k d) := e.injective.ne (by simp [P, Q])
  have hstrict := hdist (e (Q k d)) (e (P k d)) hne
  exact (not_le_of_gt hstrict) hbound

/-- The chores reduction of Section 4, with the same explicit distance/loss
tradeoff. Every allocation incurs more than MMS+l for some agent. -/
theorem universal_chores_loss {k d : ℕ} (hk : 0 < k)
    (S : HighGood k d → Finset (Fin (2 * k))) (hS : ∀ i, (S i).card = k)
    (hU : ∀ i, (∑ j ∈ S i, k * (6 * k + j.val)) = 7 * k * k * k - k * k / 2)
    (l : ℤ) (hl : l < k)
    (hdist : ∀ i j, i ≠ j → 5 * l < ((S i \ S j).card : ℤ))
    (a : Allocation k d) :
    ∃ i, 204 * (k : ℤ) ^ 3 + l < ∑ g ∈ bundle k d a i, choreCost k d (S i) g := by
  classical
  by_contra hn
  have hv : ∀ i, (∑ g ∈ bundle k d a i, choreCost k d (S i) g) ≤ 204 * (k : ℤ) ^ 3 + l := by
    simpa only [not_exists, not_lt] using hn
  have hinj := chores_high_injective hk a S l hl hv
  let e := Equiv.ofBijective (fun h : HighGood k d => a (.inr h))
    ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩
  let b : Allocation k d := e.symm ∘ a
  have hb : ∀ h, b (.inr h) = h := fun h => e.symm_apply_apply h
  have hv' : ∀ i, (∑ g ∈ bundle k d b i, choreCost k d (S (e i)) g) ≤ 204 * (k : ℤ) ^ 3 + l := by
    intro i
    rw [reindex_bundle]
    exact hv (e i)
  have hw := fixed_weights hk b hb (S ∘ e) (fun i => hS (e i)) (fun i => hU (e i)) l hl (Or.inr hv')
  have hc : ∀ i, -l ≤ ∑ g ∈ bundle k d b i, correction k d (S (e i)) g := by
    intro i
    have h := hv' i
    simp only [choreCost, Finset.sum_sub_distrib, ← Finset.mul_sum] at h
    rw [hw i] at h
    nlinarith
  have hbound := allocation_label_distance hk b hb hw (S ∘ e)
    (fun i => hS (e i)) (fun i => hU (e i)) l hc
  have hne : e (Q k d) ≠ e (P k d) := e.injective.ne (by simp [P, Q])
  have hstrict := hdist (e (Q k d)) (e (P k d)) hne
  exact (not_le_of_gt hstrict) hbound

end Cslib.FairDivision.MMSAsymptotic
