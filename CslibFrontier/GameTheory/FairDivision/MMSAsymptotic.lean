/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The asymptotic MMS construction: items and low-bundle rigidity

[EzraGarbuz2027], Section 2.1 and Lemma 7 (PDF pp. 8–9). These are the actual
parameterized item weights and type-dependent goods/chores values, with d dummy
items and n=2k+2+d agents. The total item count is exactly n+5k.

`low_bundle_rigidity` proves the structural lemma for every positive k and every
subset of the actual low goods: weight 17k^2 occurs exactly for a singleton
G-good or a matched pair X_j,Y_j. It uses weight ranges, not finite enumeration
at a selected parameter. `guarantees_iff` and `caps_iff` prove the exact goods and chores MMS under
the two explicit source label invariants (cardinality and X-weight sum), by
constructing the actual equal-bundle partitions of Lemma 6. Total valuations
equal n times that MMS target. The allocation-loss argument is in `MMSAllocationLoss`;
uniform population bounds and inverse-polynomial exclusion are in `MMSPopulation`.
The exact-existence
threshold consequences in `MMSExistence`. The latter explicitly separates the
external positive-existence dependency from the proved negative direction.
-/

public section

open scoped BigOperators

namespace Cslib.FairDivision.MMSAsymptotic

/-- X goods, Y goods and G goods, respectively. -/
abbrev LowGood (k : ℕ) := Fin (2 * k) ⊕ Fin (2 * k) ⊕ Fin k

/-- Z goods, the distinguished P/Q goods, and dummy goods, respectively. -/
abbrev HighGood (k d : ℕ) := Fin (2 * k) ⊕ Fin 2 ⊕ Fin d

/-- All items in the source construction. -/
abbrev Good (k d : ℕ) := LowGood k ⊕ HighGood k d

/-- The exact source auxiliary weights on low goods. -/
@[expose] def lowWeight (k : ℕ) : LowGood k → ℕ
  | .inl j => k * (6 * k + j.val)
  | .inr (.inl j) => 17 * k * k - k * (6 * k + j.val)
  | .inr (.inr _) => 17 * k * k

/-- Common auxiliary weights. For the paper's k divisible by 8, the integer
division in U=7k^3-k^2/2 is exact. -/
@[expose] def weight (k d : ℕ) : Good k d → ℕ
  | .inl g => lowWeight k g
  | .inr (.inl _) => 68 * k * k * k - 17 * k * k
  | .inr (.inr (.inl j)) =>
    if j.val = 0 then 68 * k * k * k - (7 * k * k * k - k * k / 2)
    else 51 * k * k * k + (7 * k * k * k - k * k / 2)
  | .inr (.inr (.inr _)) => 68 * k * k * k

/-- The type-dependent corrections, with a type represented by its label set S. -/
@[expose] def correction (k d : ℕ) (S : Finset (Fin (2 * k))) : Good k d → ℤ
  | .inl (.inl j) => if j ∈ S then 0 else -1
  | .inl (.inr (.inl j)) => if j ∈ S then 1 else 0
  | .inl (.inr (.inr _)) => -1
  | .inr (.inl _) => 1
  | .inr (.inr (.inl j)) => if j.val = 0 then 0 else -(k : ℤ)
  | .inr (.inr (.inr _)) => 0

/-- Source goods valuations, extended additively when summing a bundle. -/
@[expose] def goodsValue (k d : ℕ) (S : Finset (Fin (2 * k))) (g : Good k d) : ℤ :=
  3 * weight k d g + correction k d S g

/-- Source chores costs: the sign of the correction is reversed. -/
@[expose] def choreCost (k d : ℕ) (S : Finset (Fin (2 * k))) (g : Good k d) : ℤ :=
  3 * weight k d g - correction k d S g

/-- Exactly n+5k items for n=2k+2+d agents. -/
theorem card_goods (k d : ℕ) : Fintype.card (Good k d) = (2 * k + 2 + d) + 5 * k := by
  simp [Good, LowGood, HighGood]
  omega

/-- The exact reflection relating goods values and chores costs on every bundle. -/
theorem goodsValue_add_choreCost (k d : ℕ) (S : Finset (Fin (2 * k)))
    (B : Finset (Good k d)) :
    (∑ g ∈ B, goodsValue k d S g) + (∑ g ∈ B, choreCost k d S g) =
      6 * ∑ g ∈ B, (weight k d g : ℤ) := by
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro g _
  simp only [goodsValue, choreCost]
  omega

/-- Balanced label sets have zero total correction, for goods and chores alike. -/
theorem correction_total (k d : ℕ) (S : Finset (Fin (2 * k))) (hS : S.card = k) :
    (∑ g : Good k d, correction k d S g) = 0 := by
  have hx : (∑ j : Fin (2 * k), if j ∈ S then (0 : ℤ) else -1) =
      (S.card : ℤ) - 2 * k := by
    have he (j : Fin (2 * k)) : (if j ∈ S then (0 : ℤ) else -1) =
        (if j ∈ S then (1 : ℤ) else 0) - 1 := by split_ifs <;> omega
    simp only [he, Finset.sum_sub_distrib]
    simp
  have hy : (∑ j : Fin (2 * k), if j ∈ S then (1 : ℤ) else 0) = S.card := by
    simp
  simp only [Good, LowGood, HighGood, Fintype.sum_sum_type, correction]
  rw [hx, hy]
  simp [hS, Fin.sum_univ_two]
  omega

private theorem x_range (k : ℕ) (j : Fin (2 * k)) :
    6 * k * k ≤ k * (6 * k + j.val) ∧ k * (6 * k + j.val) < 8 * k * k := by
  have hj := j.isLt
  constructor <;> nlinarith [Nat.zero_le j.val]

/-- Total low weight is three k copies of H. -/
theorem lowWeight_total (k : ℕ) : (∑ g : LowGood k, lowWeight k g) = 51 * k * k * k := by
  have he (j : Fin (2 * k)) :
      k * (6 * k + j.val) + (17 * k * k - k * (6 * k + j.val)) = 17 * k * k := by
    have hr := x_range k j
    have hx : k * (6 * k + j.val) ≤ 17 * k * k := by nlinarith [hr.2]
    omega
  simp only [LowGood, Fintype.sum_sum_type, lowWeight]
  rw [← add_assoc, ← Finset.sum_add_distrib]
  simp only [he, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  ring

/-- The common total weight is exactly nT, including all dummy goods. -/
theorem weight_total (k d : ℕ) :
    (∑ g : Good k d, weight k d g) = (2 * k + 2 + d) * (68 * k * k * k) := by
  have hu : 7 * k * k * k - k * k / 2 ≤ 68 * k * k * k := by
    have hh := Nat.sub_le (7 * k * k * k) (k * k / 2)
    nlinarith
  have hp := Nat.sub_add_cancel hu
  have hz : 17 * k * k ≤ 68 * k * k * k := by
    by_cases hk : k = 0
    · simp [hk]
    · have hk1 : 1 ≤ k := by omega
      nlinarith [Nat.mul_le_mul_left (k * k) hk1]
  have hzc := Nat.sub_add_cancel hz
  rw [Fintype.sum_sum_type (weight k d)]
  change (∑ g : LowGood k, lowWeight k g) +
    (∑ g : HighGood k d, weight k d (.inr g)) = _
  rw [lowWeight_total]
  simp only [HighGood, Fintype.sum_sum_type, weight]
  simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, ite_true, Nat.one_ne_zero,
    ite_false, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  nlinarith

/-- Each balanced type's total goods value is n times the source MMS target. -/
theorem goodsValue_total (k d : ℕ) (S : Finset (Fin (2 * k))) (hS : S.card = k) :
    (∑ g : Good k d, goodsValue k d S g) =
      (2 * (k : ℤ) + 2 + d) * (204 * k * k * k) := by
  simp only [goodsValue, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [correction_total k d S hS, ← Nat.cast_sum, weight_total]
  push_cast
  ring

/-- Each balanced type's total chore cost equals the same n times MMS target. -/
theorem choreCost_total (k d : ℕ) (S : Finset (Fin (2 * k))) (hS : S.card = k) :
    (∑ g : Good k d, choreCost k d S g) =
      (2 * (k : ℤ) + 2 + d) * (204 * k * k * k) := by
  simp only [choreCost, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [correction_total k d S hS, ← Nat.cast_sum, weight_total]
  push_cast
  ring

/-- All low weights lie between 6k^2 and 17k^2. -/
theorem lowWeight_range (k : ℕ) (g : LowGood k) :
    6 * k * k ≤ lowWeight k g ∧ lowWeight k g ≤ 17 * k * k := by
  rcases g with j | j | j
  · have hr := x_range k j
    simp only [lowWeight]
    constructor <;> nlinarith
  · have hr := x_range k j
    have hx : k * (6 * k + j.val) ≤ 17 * k * k := by nlinarith [hr.2]
    have hh := Nat.sub_add_cancel hx
    simp only [lowWeight]
    constructor <;> nlinarith
  · simp only [lowWeight]
    constructor <;> nlinarith

/-- The concrete weights are positive uniformly in the number of dummy items. -/
theorem weight_lower (k d : ℕ) (hk : 0 < k) (g : Good k d) :
    6 * k * k ≤ weight k d g := by
  have hk1 : 1 ≤ k := hk
  have hcube : k * k ≤ k * k * k := by nlinarith
  rcases g with g | j | j | j
  · exact (lowWeight_range k g).1
  · simp only [weight]
    have hz : 17 * k * k ≤ 68 * k * k * k := by nlinarith
    have hh := Nat.sub_add_cancel hz
    nlinarith
  · simp only [weight]
    split_ifs
    · have hu : 7 * k * k * k - k * k / 2 ≤ 68 * k * k * k := by
        have hh : 7 * k * k * k ≤ 68 * k * k * k := by nlinarith
        omega
      have hs := Nat.sub_add_cancel hu
      have hh := Nat.sub_le (7 * k * k * k) (k * k / 2)
      nlinarith
    · nlinarith
  · simp only [weight]
    nlinarith

/-- Item corrections lie between -k and 1, including Q's correction -k. -/
theorem correction_bounds (k d : ℕ) (hk : 0 < k) (S : Finset (Fin (2 * k)))
    (g : Good k d) : -(k : ℤ) ≤ correction k d S g ∧ correction k d S g ≤ 1 := by
  rcases g with (j | j | j) | j | j | j <;>
    simp [correction] <;> omega

/-- The actual goods construction has strictly positive integer item values. -/
theorem goodsValue_pos (k d : ℕ) (hk : 0 < k) (S : Finset (Fin (2 * k)))
    (g : Good k d) : 0 < goodsValue k d S g := by
  have hw : 6 * (k : ℤ) * k ≤ weight k d g := by exact_mod_cast weight_lower k d hk g
  have hc := correction_bounds k d hk S g
  have hp : (0 : ℤ) < k := by exact_mod_cast hk
  simp only [goodsValue]
  nlinarith

/-- Reversing corrections also gives strictly positive integer chore costs. -/
theorem choreCost_pos (k d : ℕ) (hk : 0 < k) (S : Finset (Fin (2 * k)))
    (g : Good k d) : 0 < choreCost k d S g := by
  have hw : 6 * (k : ℤ) * k ≤ weight k d g := by exact_mod_cast weight_lower k d hk g
  have hc := correction_bounds k d hk S g
  have hp : (0 : ℤ) < k := by exact_mod_cast hk
  simp only [choreCost]
  nlinarith
private theorem singleton_weight (k : ℕ) (hk : 0 < k) (g : LowGood k) :
    lowWeight k g = 17 * k * k ↔ ∃ h : Fin k, g = Sum.inr (Sum.inr h) := by
  have hkk : 0 < k * k := Nat.mul_pos hk hk
  rcases g with j | j | j
  · have hr := x_range k j
    simp [lowWeight]
    nlinarith
  · have hr := x_range k j
    have hx : k * (6 * k + j.val) ≤ 17 * k * k := by nlinarith [hr.2]
    have hh := Nat.sub_add_cancel hx
    simp [lowWeight]
    nlinarith
  · simp [lowWeight]

private theorem pair_weight (k : ℕ) (hk : 0 < k) (a b : LowGood k) :
    lowWeight k a + lowWeight k b = 17 * k * k ↔
      ∃ j : Fin (2 * k),
        (a = Sum.inl j ∧ b = Sum.inr (Sum.inl j)) ∨
        (b = Sum.inl j ∧ a = Sum.inr (Sum.inl j)) := by
  have hkk : 0 < k * k := Nat.mul_pos hk hk
  have xy (a b : Fin (2 * k)) :
      k * (6 * k + a.val) + (17 * k * k - k * (6 * k + b.val)) = 17 * k * k ↔ a = b := by
    have hb := x_range k b
    have hh := Nat.sub_add_cancel (show k * (6 * k + b.val) ≤ 17 * k * k by nlinarith [hb.2])
    constructor
    · intro he
      apply Fin.ext
      nlinarith
    · rintro rfl
      omega
  rcases a with a | a | a <;> rcases b with b | b | b
  · have ha := x_range k a
    have hb := x_range k b
    simp [lowWeight]
    nlinarith
  · simpa [lowWeight, eq_comm] using xy a b
  · simp [lowWeight, Nat.ne_of_gt hk]
  · simpa [lowWeight, Nat.add_comm, eq_comm] using xy b a
  · have ha := x_range k a
    have hb := x_range k b
    have hsa := Nat.sub_add_cancel (show k * (6 * k + a.val) ≤ 17 * k * k by nlinarith [ha.2])
    have hsb := Nat.sub_add_cancel (show k * (6 * k + b.val) ≤ 17 * k * k by nlinarith [hb.2])
    simp [lowWeight]
    nlinarith
  · have ha := x_range k a
    have hsa := Nat.sub_add_cancel (show k * (6 * k + a.val) ≤ 17 * k * k by nlinarith [ha.2])
    simp [lowWeight]
    nlinarith
  · simp [lowWeight, Nat.ne_of_gt hk]
  · have hb := x_range k b
    have hsb := Nat.sub_add_cancel (show k * (6 * k + b.val) ≤ 17 * k * k by nlinarith [hb.2])
    simp [lowWeight]
    nlinarith
  · simp [lowWeight]
    nlinarith

/-- Lemma 7: every weight-H subset of low goods is a singleton G or matched X/Y.
The converse is included, so there are no missing low-bundle configurations. -/
theorem low_bundle_rigidity (k : ℕ) (hk : 0 < k) (B : Finset (LowGood k)) :
    (∑ g ∈ B, lowWeight k g) = 17 * k * k ↔
      (∃ h : Fin k, B = {Sum.inr (Sum.inr h)}) ∨
      (∃ j : Fin (2 * k), B = {Sum.inl j, Sum.inr (Sum.inl j)}) := by
  constructor
  · intro he
    have hc : B.card ≤ 2 := by
      have hb : B.card * (6 * k * k) ≤ ∑ g ∈ B, lowWeight k g := by
        calc
          B.card * (6 * k * k) = ∑ _g ∈ B, 6 * k * k := by simp
          _ ≤ _ := Finset.sum_le_sum fun g _ => (lowWeight_range k g).1
      rw [he] at hb
      by_contra h
      have hh : 3 ≤ B.card := by omega
      nlinarith [Nat.mul_le_mul_right (6 * k * k) hh]
    have hn : B.Nonempty := by
      by_contra h
      have hem : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
      simp only [hem, Finset.sum_empty] at he
      nlinarith
    have cases : B.card = 1 ∨ B.card = 2 := by
      have := Finset.card_pos.mpr hn
      omega
    rcases cases with hc | hc
    · obtain ⟨g, rfl⟩ := Finset.card_eq_one.mp hc
      simp only [Finset.sum_singleton] at he
      obtain ⟨h, rfl⟩ := (singleton_weight k hk g).mp he
      exact Or.inl ⟨h, rfl⟩
    · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hc
      rw [Finset.sum_pair hab] at he
      obtain ⟨j, hj | hj⟩ := (pair_weight k hk a b).mp he
      · exact Or.inr ⟨j, by rw [hj.1, hj.2]⟩
      · exact Or.inr ⟨j, by rw [hj.1, hj.2, Finset.pair_comm]⟩
  · rintro (⟨h, rfl⟩ | ⟨j, rfl⟩)
    · simp [lowWeight]
    · have hr := x_range k j
      rw [Finset.sum_pair (by simp)]
      simp only [lowWeight]
      have hh := Nat.sub_add_cancel (show k * (6 * k + j.val) ≤ 17 * k * k by nlinarith [hr.2])
      omega


/-- The source's label 2h+a_h for a bit at coordinate h. -/
@[expose] def labelIndex {k : ℕ} (a : Fin k → Bool) (h : Fin k) : Fin (2 * k) :=
  ⟨2 * h.val + if a h then 1 else 0, by split_ifs <;> omega⟩

/-- Every bit string selects exactly one label from each consecutive pair. -/
@[expose] def labelSet {k : ℕ} (a : Fin k → Bool) : Finset (Fin (2 * k)) :=
  Finset.univ.image (labelIndex a)

/-- Labels of distinct coordinates are distinct, independently of the bits. -/
theorem labelIndex_injective {k : ℕ} (a : Fin k → Bool) :
    Function.Injective (labelIndex a) := by
  intro h j he
  apply Fin.ext
  have hv := congrArg Fin.val he
  simp only [labelIndex] at hv
  split_ifs at hv <;> omega

/-- The source label set has exactly k elements. -/
theorem card_labelSet {k : ℕ} (a : Fin k → Bool) : (labelSet a).card = k := by
  simp [labelSet, Finset.card_image_of_injective, labelIndex_injective]

/-- Two labels agree precisely when both their coordinate and bit agree. -/
theorem labelIndex_eq_iff {k : ℕ} (a b : Fin k → Bool) (h j : Fin k) :
    labelIndex a h = labelIndex b j ↔ h = j ∧ a h = b j := by
  cases ha : a h <;> cases hb : b j <;>
    simp [labelIndex, ha, hb, Fin.ext_iff] <;> omega

/-- Membership in another word's label set compares the bit at the same coordinate. -/
theorem labelIndex_mem_iff {k : ℕ} (a b : Fin k → Bool) (h : Fin k) :
    labelIndex a h ∈ labelSet b ↔ a h = b h := by
  simp only [labelSet, Finset.mem_image, Finset.mem_univ, true_and, labelIndex_eq_iff]
  constructor
  · rintro ⟨j, rfl, he⟩
    exact he.symm
  · intro he
    exact ⟨h, rfl, he.symm⟩

/-- Equation (2)'s combinatorial identity: one-sided label distance equals the
number of differing bits, independently of whether either word is balanced. -/
theorem labelSet_sdiff_card {k : ℕ} (a b : Fin k → Bool) :
    ((labelSet a) \ labelSet b).card =
      (Finset.univ.filter fun h => a h ≠ b h).card := by
  have he : labelSet a \ labelSet b =
      (Finset.univ.filter fun h => a h ≠ b h).image (labelIndex a) := by
    ext j
    constructor
    · intro hj
      obtain ⟨hj, hb⟩ := Finset.mem_sdiff.mp hj
      obtain ⟨h, _, rfl⟩ := Finset.mem_image.mp hj
      exact Finset.mem_image.mpr ⟨h, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, fun heq => hb ((labelIndex_mem_iff a b h).mpr heq)⟩, rfl⟩
    · intro hj
      obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hj
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr ⟨h, Finset.mem_univ _, rfl⟩,
        fun hb => (Finset.mem_filter.mp hh).2 ((labelIndex_mem_iff a b h).mp hb)⟩
  rw [he, Finset.card_image_of_injective _ (labelIndex_injective a)]

/-- Equation (1): the label sum for a balanced binary word. -/
theorem sum_labelSet {k : ℕ} (a : Fin k → Bool)
    (ha : (Finset.univ.filter fun h => a h).card = k / 2) :
    (∑ j ∈ labelSet a, j.val) = k * (k - 1) + k / 2 := by
  have hs : (∑ h : Fin k, h.val) * 2 = k * (k - 1) := by
    rw [Fin.sum_univ_eq_sum_range (fun x : ℕ => x) k]
    exact Finset.sum_range_id_mul_two k
  rw [labelSet, Finset.sum_image (fun h _ j _ he => labelIndex_injective a he)]
  simp only [labelIndex, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hb : (∑ h : Fin k, if a h then 1 else 0) = k / 2 := by simpa using ha
  rw [hb]
  omega

/-- Balanced even-length source words satisfy the explicit X-weight invariant U. -/
theorem labelSet_x_weight {k : ℕ} (a : Fin k → Bool) (hk : 2 ∣ k)
    (ha : (Finset.univ.filter fun h => a h).card = k / 2) :
    (∑ j ∈ labelSet a, k * (6 * k + j.val)) = 7 * k * k * k - k * k / 2 := by
  have hs := sum_labelSet a ha
  have hc := card_labelSet a
  have hd : k / 2 * 2 = k := Nat.div_mul_cancel hk
  have hdd : k * k / 2 * 2 = k * k := Nat.div_mul_cancel (dvd_mul_of_dvd_left hk k)
  have hhalf : k * (k / 2) = k * k / 2 := (Nat.mul_div_assoc k hk).symm
  have he (j : Fin (2 * k)) : k * (6 * k + j.val) = 6 * k * k + k * j.val := by ring
  simp only [he, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, hc,
    ← Finset.mul_sum, hs]
  by_cases hz : k = 0
  · simp [hz]
  · have hm : k - 1 + 1 = k := by omega
    have hm2 : k * (k - 1) + k = k * k := by nlinarith
    have hm3 := congrArg (fun x => k * x) hm2
    simp only [Nat.mul_add] at hm3
    have heq : k * (6 * k * k) + k * (k * (k - 1) + k / 2) + k * k / 2 =
        7 * k * k * k := by nlinarith
    omega

/-- Source partition slots: one for every high item. -/
abbrev Allocation (k d : ℕ) := Good k d → HighGood k d

/-- The complete bundle received by a partition slot. -/
@[expose] def bundle (k d : ℕ) (a : Allocation k d) (i : HighGood k d) : Finset (Good k d) :=
  Finset.univ.filter fun g => a g = i

/-- A type's witness partition from Lemma 6. The bijection assigns a distinct G
item to every selected Z label; it supplies no assumption about bundle values. -/
@[expose] def witness (k d : ℕ) (S : Finset (Fin (2 * k)))
    (e : Fin k ≃ S) : Allocation k d
  | .inl (.inl j) => if j ∈ S then .inr (.inl 0) else .inl j
  | .inl (.inr (.inl j)) => if j ∈ S then .inr (.inl 1) else .inl j
  | .inl (.inr (.inr h)) => .inl (e h).val
  | .inr h => h

private theorem witness_high (k d : ℕ) (S : Finset (Fin (2 * k))) (e : Fin k ≃ S)
    (f : Good k d → ℤ) (i : HighGood k d) :
    (∑ g ∈ bundle k d (witness k d S e) i, f g) =
      (∑ j : Fin (2 * k), if (if j ∈ S then Sum.inr (Sum.inl (0 : Fin 2))
        else Sum.inl j) = i then f (.inl (.inl j)) else 0) +
      (∑ j : Fin (2 * k), if (if j ∈ S then Sum.inr (Sum.inl (1 : Fin 2))
        else Sum.inl j) = i then f (.inl (.inr (.inl j))) else 0) +
      (∑ h : Fin k, if Sum.inl (e h).val = i then f (.inl (.inr (.inr h))) else 0) +
      f (.inr i) := by
  classical
  unfold bundle
  rw [Finset.sum_filter]
  simp only [Good, LowGood, HighGood, Fintype.sum_sum_type]
  dsimp +instances only [witness]
  rcases i with i | i | i <;>
    simp only [Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl,
      ite_false, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
      zero_add, add_zero]; ring

private theorem g_fiber (k : ℕ) (S : Finset (Fin (2 * k))) (e : Fin k ≃ S)
    (j : Fin (2 * k)) (c : ℤ) :
    (∑ h : Fin k, if (e h).val = j then c else 0) = if j ∈ S then c else 0 := by
  classical
  rw [← e.symm.sum_comp]
  by_cases hj : j ∈ S
  · have he (x : S) : (x.val = j) ↔ x = ⟨j, hj⟩ := by
      constructor <;> intro h <;> simpa only [Subtype.ext_iff] using h
    simp [he, hj]
  · have he (x : S) : x.val ≠ j := by
      intro h
      exact hj (h ▸ x.property)
    simp [he, hj]

/-- Each source witness bundle has exactly common auxiliary weight T. -/
theorem witness_weight (k d : ℕ) (S : Finset (Fin (2 * k))) (e : Fin k ≃ S)
    (hS : S.card = k) (hU : (∑ j ∈ S, (k * (6 * k + j.val) : ℕ)) =
      7 * k * k * k - k * k / 2) (i : HighGood k d) :
    (∑ g ∈ bundle k d (witness k d S e) i, (weight k d g : ℤ)) =
      68 * (k : ℤ) * k * k := by
  have hcast : (∑ j ∈ S, (k : ℤ) * (6 * k + j.val)) =
      ((7 * k * k * k - k * k / 2 : ℕ) : ℤ) := by exact_mod_cast hU
  have hx (j : Fin (2 * k)) : k * (6 * k + j.val) ≤ 17 * k * k := by
    have hr := x_range k j
    nlinarith [hr.2]
  have hu : 7 * k * k * k - k * k / 2 ≤ 68 * k * k * k := by
    have hh := Nat.sub_le (7 * k * k * k) (k * k / 2)
    nlinarith
  have hz : 17 * k * k ≤ 68 * k * k * k := by
    by_cases hk : k = 0
    · simp [hk]
    · have hk1 : 1 ≤ k := by omega
      nlinarith [Nat.mul_le_mul_left (k * k) hk1]
  rw [witness_high]
  rcases i with j | j | j
  · simp only [weight, lowWeight]
    simp only [ite_eq_iff, Sum.inr_ne_inl, Sum.inl.injEq, false_or, and_false]
    have hf (f : Fin (2 * k) → ℤ) :
        (∑ x, if x ∉ S ∧ x = j then f x else 0) = if j ∈ S then 0 else f j := by
      have he (x : Fin (2 * k)) : (x ∉ S ∧ x = j) ↔ (x = j ∧ j ∉ S) := by
        aesop
      by_cases hj : j ∈ S <;> simp [he, hj]
    rw [hf, hf, g_fiber]
    split_ifs <;> push_cast [Nat.cast_sub hz, Nat.cast_sub (hx j)] <;> ring
  · fin_cases j
    · simp only [weight, lowWeight, ite_eq_iff]
      norm_num only [Sum.inr.injEq, Sum.inl.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl,
        Fin.ext_iff, Fin.val_zero, Fin.val_one]
      simp only [and_true, and_false, or_false, ite_false, ite_true,
        Finset.sum_const_zero, add_zero, Finset.sum_ite_mem, Finset.univ_inter]
      rw [Nat.cast_sub hu]
      push_cast
      rw [hcast]
      ring
    · simp only [weight, lowWeight]
      simp [ite_eq_iff, Nat.cast_sub (hx _), Finset.sum_sub_distrib,
        Finset.sum_const, hS, hcast]
      ring
  · simp [weight, ite_eq_iff]

/-- Every bundle of the source's type-specific partition has correction zero. -/
theorem witness_correction (k d : ℕ) (S : Finset (Fin (2 * k))) (e : Fin k ≃ S)
    (hS : S.card = k) (i : HighGood k d) :
    (∑ g ∈ bundle k d (witness k d S e) i, correction k d S g) = 0 := by
  rw [witness_high]
  rcases i with j | j | j
  · simp only [correction, ite_eq_iff, Sum.inr_ne_inl, Sum.inl.injEq, and_false,
      false_or]
    have hf (f : Fin (2 * k) → ℤ) :
        (∑ x, if x ∉ S ∧ x = j then f x else 0) = if j ∈ S then 0 else f j := by
      have he (x : Fin (2 * k)) : (x ∉ S ∧ x = j) ↔ (x = j ∧ j ∉ S) := by aesop
      by_cases hj : j ∈ S <;> simp [he, hj]
    rw [hf, hf]
    rw [g_fiber]
    split_ifs <;> norm_num
  · fin_cases j <;>
      simp [correction, ite_eq_iff, Fin.ext_iff, Finset.sum_ite, hS]
  · simp [correction, ite_eq_iff]

/-- Actual equal-valued goods partitions, obtained without assuming MMS. -/
theorem witness_goodsValue (k d : ℕ) (S : Finset (Fin (2 * k))) (e : Fin k ≃ S)
    (hS : S.card = k) (hU : (∑ j ∈ S, (k * (6 * k + j.val) : ℕ)) =
      7 * k * k * k - k * k / 2) (i : HighGood k d) :
    (∑ g ∈ bundle k d (witness k d S e) i, goodsValue k d S g) =
      204 * (k : ℤ) * k * k := by
  simp only [goodsValue, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [witness_weight k d S e hS hU, witness_correction k d S e hS]
  ring

/-- Actual equal-cost chores partitions on the same items. -/
theorem witness_choreCost (k d : ℕ) (S : Finset (Fin (2 * k))) (e : Fin k ≃ S)
    (hS : S.card = k) (hU : (∑ j ∈ S, (k * (6 * k + j.val) : ℕ)) =
      7 * k * k * k - k * k / 2) (i : HighGood k d) :
    (∑ g ∈ bundle k d (witness k d S e) i, choreCost k d S g) =
      204 * (k : ℤ) * k * k := by
  simp only [choreCost, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [witness_weight k d S e hS hU, witness_correction k d S e hS]
  ring

/-- Goods MMS convention: a lower bound achievable by some complete partition. -/
@[expose] def Guarantees (k d : ℕ) (S : Finset (Fin (2 * k))) (t : ℤ) : Prop :=
  ∃ a : Allocation k d, ∀ i, t ≤ ∑ g ∈ bundle k d a i, goodsValue k d S g

/-- Chores MMS convention: an upper cost cap achievable by some complete partition. -/
@[expose] def Caps (k d : ℕ) (S : Finset (Fin (2 * k))) (t : ℤ) : Prop :=
  ∃ a : Allocation k d, ∀ i, (∑ g ∈ bundle k d a i, choreCost k d S g) ≤ t

/-- Every complete allocation partitions the total additive value among its fibers. -/
theorem allocation_total (k d : ℕ) (a : Allocation k d) (f : Good k d → ℤ) :
    (∑ i : HighGood k d, ∑ g ∈ bundle k d a i, f g) = ∑ g, f g := by
  classical
  simp only [bundle, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g _
  simp

/-- Lemma 6: exact goods MMS, with no assumed equal-bundle or rigidity premise.
The two label invariants are cardinality k and the explicit sum of X weights U. -/
theorem guarantees_iff (k d : ℕ) (S : Finset (Fin (2 * k))) (hS : S.card = k)
    (hU : (∑ j ∈ S, (k * (6 * k + j.val) : ℕ)) =
      7 * k * k * k - k * k / 2) (t : ℤ) :
    Guarantees k d S t ↔ t ≤ 204 * (k : ℤ) * k * k := by
  constructor
  · rintro ⟨a, ha⟩
    have hb := Finset.sum_le_sum (s := Finset.univ) (fun i _ => ha i)
    rw [allocation_total, goodsValue_total k d S hS] at hb
    simp only [HighGood, Finset.sum_const, Finset.card_univ, Fintype.card_sum,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hb
    have hk : (0 : ℤ) ≤ k := by positivity
    have hd : (0 : ℤ) ≤ d := by positivity
    nlinarith
  · intro ht
    let e : Fin k ≃ S := (Finset.equivFinOfCardEq hS).symm
    exact ⟨witness k d S e, fun i => (witness_goodsValue k d S e hS hU i).symm ▸ ht⟩

/-- The same type-specific partitions give the exact chores MMS target. -/
theorem caps_iff (k d : ℕ) (S : Finset (Fin (2 * k))) (hS : S.card = k)
    (hU : (∑ j ∈ S, (k * (6 * k + j.val) : ℕ)) =
      7 * k * k * k - k * k / 2) (t : ℤ) :
    Caps k d S t ↔ 204 * (k : ℤ) * k * k ≤ t := by
  constructor
  · rintro ⟨a, ha⟩
    have hb := Finset.sum_le_sum (s := Finset.univ) (fun i _ => ha i)
    rw [allocation_total, choreCost_total k d S hS] at hb
    simp only [HighGood, Finset.sum_const, Finset.card_univ, Fintype.card_sum,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hb
    have hk : (0 : ℤ) ≤ k := by positivity
    have hd : (0 : ℤ) ≤ d := by positivity
    nlinarith
  · intro ht
    let e : Fin k ≃ S := (Finset.equivFinOfCardEq hS).symm
    exact ⟨witness k d S e, fun i => (witness_choreCost k d S e hS hU i).symm ▸ ht⟩

/-- Lemma 6 for every actual balanced even-length word, deriving both source
label invariants rather than requiring their weight sum as an input. -/
theorem balanced_guarantees_iff {k : ℕ} (d : ℕ) (a : Fin k → Bool) (hk : 2 ∣ k)
    (ha : (Finset.univ.filter fun h => a h).card = k / 2) (t : ℤ) :
    Guarantees k d (labelSet a) t ↔ t ≤ 204 * (k : ℤ) * k * k :=
  guarantees_iff k d (labelSet a) (card_labelSet a) (labelSet_x_weight a hk ha) t

/-- The chores MMS for each actual balanced even-length source word. -/
theorem balanced_caps_iff {k : ℕ} (d : ℕ) (a : Fin k → Bool) (hk : 2 ∣ k)
    (ha : (Finset.univ.filter fun h => a h).card = k / 2) (t : ℤ) :
    Caps k d (labelSet a) t ↔ 204 * (k : ℤ) * k * k ≤ t :=
  caps_iff k d (labelSet a) (card_labelSet a) (labelSet_x_weight a hk ha) t

end Cslib.FairDivision.MMSAsymptotic
