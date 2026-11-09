/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Distributions with one linear constraint

A finite distribution can be replaced by one supported on at most two indices,
preserving the expectation of one observable and decreasing the expectation of
another. The proof works over any linear ordered field, including the rationals:
it removes an index along a mass- and moment-preserving direction. In particular,
no existence of an optimizer is an input to the reduction.

This is the support-reduction argument used in [Wang2027], Theorem 1(3), PDF p. 7.

## Main results

* `exists_two_support`: preserve one moment and decrease cost on at most two atoms.
* `exists_optimal_two`: construct an attained optimum by finite vertex enumeration.
-/

public section
namespace Cslib.Optimization.OneConstraint
open Finset
variable {ι K : Type*} [Fintype ι]
  [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- A nonnegative normalized finite probability table. -/
@[ext] structure Distribution (ι K : Type*) [Fintype ι] [Field K] [LinearOrder K] where
  /-- Probability of each index. -/
  weight : ι → K
  /-- Nonnegative weights. -/
  nonneg : ∀ i, 0 ≤ weight i
  /-- Total probability one. -/
  total : ∑ i, weight i = 1

/-- Expectation of an observable under a finite probability table. -/
@[expose] def Distribution.mean (w : Distribution ι K) (f : ι → K) : K :=
  ∑ i, w.weight i * f i

/-- The indices with strictly positive mass. -/
@[expose] def Distribution.support (w : Distribution ι K) : Finset ι :=
  univ.filter fun i => 0 < w.weight i

open scoped Classical in
/-- A deterministic finite law. -/
@[expose] noncomputable def Distribution.pure (i : ι) : Distribution ι K :=
  ⟨fun j => if j = i then 1 else 0, fun j => by split_ifs <;> norm_num, by simp⟩

variable {κ : Type*} [Fintype κ]

open scoped Classical in
/-- Push a finite table through a deterministic map. -/
@[expose] noncomputable def Distribution.map (w : Distribution ι K) (f : ι → κ) :
    Distribution κ K :=
  ⟨fun j => ∑ i, if f i = j then w.weight i else 0,
    fun j => sum_nonneg fun i _ => by split_ifs; exacts [w.nonneg i, le_rfl],
    by rw [sum_comm]; simp [w.total]⟩

/-- Compose finite conditional probability tables. -/
@[expose] def Distribution.bind (w : Distribution ι K) (f : ι → Distribution κ K) :
    Distribution κ K :=
  ⟨fun j => ∑ i, w.weight i * (f i).weight j,
    fun j => sum_nonneg fun i _ => mul_nonneg (w.nonneg i) ((f i).nonneg j),
    by rw [sum_comm]; simp only [← mul_sum, Distribution.total, mul_one, Distribution.total]⟩

/-- Evaluation under a deterministic finite law. -/
theorem Distribution.mean_pure (i : ι) (f : ι → K) : (Distribution.pure i).mean f = f i := by
  classical
  simp [Distribution.mean, Distribution.pure, ite_mul]

/-- Deterministic change of variables for finite tables. -/
theorem Distribution.mean_map (w : Distribution ι K) (f : ι → κ) (g : κ → K) :
    (w.map f).mean g = w.mean (g ∘ f) := by
  classical
  simp only [Distribution.mean, Distribution.map, sum_mul]
  rw [sum_comm]
  simp [ite_mul]

/-- The tower identity for finite tables. -/
theorem Distribution.mean_bind (w : Distribution ι K) (f : ι → Distribution κ K)
    (g : κ → K) : (w.bind f).mean g = w.mean (fun i => (f i).mean g) := by
  simp only [Distribution.mean, Distribution.bind, sum_mul]
  rw [sum_comm]
  simp only [mul_assoc, mul_sum]

omit [IsStrictOrderedRing K] in
/-- The expectation of a constant is that constant. -/
theorem Distribution.mean_const {α : Type} [Fintype α] (w : Distribution α K) (a : K) :
    w.mean (fun _ => a) = a := by
  simp [Distribution.mean, ← sum_mul, w.total]

omit [IsStrictOrderedRing K] in
/-- Finite expectation preserves addition. -/
theorem Distribution.mean_add {α : Type} [Fintype α] (w : Distribution α K) (f g : α → K) :
    w.mean (fun i => f i + g i) = w.mean f + w.mean g := by
  simp [Distribution.mean, mul_add, sum_add_distrib]

omit [IsStrictOrderedRing K] in
/-- Finite expectation commutes with constant scalar multiplication. -/
theorem Distribution.mean_mul {α : Type} [Fintype α] (w : Distribution α K) (a : K) (f : α → K) :
    w.mean (fun i => a * f i) = a * w.mean f := by
  simp [Distribution.mean, mul_left_comm, mul_sum]

/-- Restrict a law to a finite set containing all its nonzero weights. -/
@[expose] def Distribution.restrict (w : Distribution ι K) (s : Finset ι)
    (hw : ∀ i ∉ s, w.weight i = 0) : Distribution s K :=
  ⟨fun i => w.weight i, fun i => w.nonneg i, by
    rw [sum_coe_sort, sum_subset (subset_univ s) (fun i _ hi => hw i hi)]
    exact w.total⟩

omit [IsStrictOrderedRing K] in
/-- Restricting to a set of full probability preserves every expectation. -/
theorem Distribution.mean_restrict (w : Distribution ι K) (s : Finset ι)
    (hw : ∀ i ∉ s, w.weight i = 0) (f : ι → K) :
    (w.restrict s hw).mean (fun i => f i) = w.mean f := by
  change (∑ i : s, (fun j => w.weight j * f j) i) = _
  calc
    _ = ∑ i ∈ s, w.weight i * f i := sum_coe_sort s _
    _ = _ := sum_subset (subset_univ s) (fun i _ hi => by rw [hw i hi, zero_mul])

/-- Pushforward cannot introduce more positive atoms than its source law. -/
theorem Distribution.support_map_card (w : Distribution ι K) (f : ι → κ) :
    (w.map f).support.card ≤ w.support.card := by
  classical
  have hsub : (w.map f).support ⊆ w.support.image f := by
    intro j hj
    have hjpos : 0 < ∑ i, if f i = j then w.weight i else 0 := (mem_filter.mp hj).2
    obtain ⟨i, _, hi⟩ := (sum_pos_iff_of_nonneg
      (fun i _ => by split_ifs; exacts [w.nonneg i, le_rfl])).mp hjpos
    split_ifs at hi with hij
    · exact mem_image.mpr ⟨i, mem_filter.mpr ⟨mem_univ i, hi⟩, hij⟩
    · exact (lt_irrefl _ hi).elim
  exact (card_le_card hsub).trans (card_image_le)

/-- Positive support of a deterministic finite law. -/
theorem Distribution.mem_support_pure (a i : ι) :
    i ∈ (Distribution.pure a : Distribution ι K).support ↔ i = a := by
  classical
  simp only [Distribution.support, mem_filter, mem_univ, true_and]
  change (0 < (if i = a then 1 else 0 : K)) ↔ i = a
  by_cases h : i = a <;> simp [h]

/-- Positive support of a conditional mixture. -/
theorem Distribution.mem_support_bind (w : Distribution ι K) (k : ι → Distribution κ K) (j : κ) :
    j ∈ (w.bind k).support ↔ ∃ i ∈ w.support, j ∈ (k i).support := by
  simp only [Distribution.support, mem_filter, mem_univ, true_and]
  change (0 < ∑ i, w.weight i * (k i).weight j) ↔
    ∃ i, 0 < w.weight i ∧ 0 < (k i).weight j
  rw [sum_pos_iff_of_nonneg (fun i _ => mul_nonneg (w.nonneg i) ((k i).nonneg j))]
  constructor
  · rintro ⟨i,_,hi⟩
    rcases mul_pos_iff.mp hi with h | h
    · exact ⟨i,h⟩
    · linarith [w.nonneg i]
  · rintro ⟨i,hi,hj⟩
    exact ⟨i,mem_univ i,mul_pos hi hj⟩

/-- Positive support of deterministic postprocessing. -/
theorem Distribution.mem_support_map (w : Distribution ι K) (f : ι → κ) (j : κ) :
    j ∈ (w.map f).support ↔ ∃ i ∈ w.support, f i = j := by
  classical
  simp only [Distribution.support, mem_filter, mem_univ, true_and]
  change (0 < ∑ i, if f i = j then w.weight i else 0) ↔
    ∃ i, 0 < w.weight i ∧ f i = j
  rw [sum_pos_iff_of_nonneg (fun i _ => by split_ifs; exacts [w.nonneg i, le_rfl])]
  constructor
  · rintro ⟨i,_,hi⟩
    split_ifs at hi with hij
    · exact ⟨i,hi,hij⟩
    · exact (lt_irrefl _ hi).elim
  · rintro ⟨i,hi,hij⟩
    exact ⟨i,mem_univ i,by simpa only [hij, ↓reduceIte] using hi⟩

/-- A normalized table has a nonempty positive support. -/
theorem Distribution.support_nonempty (w : Distribution ι K) : w.support.Nonempty := by
  by_contra h
  have hz : ∀ i, w.weight i = 0 := by
    intro i
    have : ¬ 0 < w.weight i := fun hi => h ⟨i, mem_filter.mpr ⟨mem_univ i, hi⟩⟩
    exact le_antisymm (le_of_not_gt this) (w.nonneg i)
  have := w.total
  simp [hz] at this

omit [IsStrictOrderedRing K] in
/-- Weights outside positive support vanish. -/
theorem Distribution.weight_zero_of_not_mem (w : Distribution ι K) (i : ι)
    (hi : i ∉ w.support) : w.weight i = 0 := by
  have hn : ¬ 0 < w.weight i := fun h => hi (mem_filter.mpr ⟨mem_univ i,h⟩)
  exact le_antisymm (le_of_not_gt hn) (w.nonneg i)

/-- Equality with a common upper bound forces equality at every positive atom. -/
theorem Distribution.mean_eq_iff_of_le (w : Distribution ι K) (f : ι → K) (M : K)
    (hf : ∀ i ∈ w.support, f i ≤ M) :
    w.mean f = M ↔ ∀ i ∈ w.support, f i = M := by
  classical
  have hn : ∀ i, 0 ≤ w.weight i * (M-f i) := by
    intro i
    by_cases hi : i ∈ w.support
    · exact mul_nonneg (w.nonneg i) (sub_nonneg.mpr (hf i hi))
    · rw [w.weight_zero_of_not_mem i hi, zero_mul]
  constructor
  · intro he i hi
    have he' : (∑ i, w.weight i * f i) = M := he
    have hz : (∑ i, w.weight i * (M-f i)) = 0 := by
      simp only [mul_sub, sum_sub_distrib, ← sum_mul, w.total, one_mul,
        he', sub_self]
    have hz' := (sum_eq_zero_iff_of_nonneg (fun i _ => hn i)).mp hz i (mem_univ i)
    have hpos := (mem_filter.mp hi).2
    nlinarith
  · intro he
    calc
      w.mean f = ∑ i, w.weight i * M := by
        apply sum_congr rfl
        intro i _
        by_cases hi : i ∈ w.support
        · rw [he i hi]
        · rw [w.weight_zero_of_not_mem i hi, zero_mul, zero_mul]
      _ = M := by rw [← sum_mul, w.total, one_mul]

/-- Some positive atom costs no more than the average. -/
theorem Distribution.exists_support_le_mean (w : Distribution ι K) (f : ι → K) :
    ∃ i ∈ w.support, f i ≤ w.mean f := by
  classical
  obtain ⟨i,hi,hmin⟩ := w.support.exists_min_image f w.support_nonempty
  refine ⟨i,hi,?_⟩
  have hn : ∀ j, 0 ≤ w.weight j * (f j-f i) := by
    intro j
    by_cases hj : j ∈ w.support
    · exact mul_nonneg (w.nonneg j) (sub_nonneg.mpr (hmin j hj))
    · rw [w.weight_zero_of_not_mem j hj, zero_mul]
  have hs := sum_nonneg (fun j (_ : j ∈ univ) => hn j)
  simpa only [mul_sub, sum_sub_distrib, ← sum_mul, w.total, one_mul,
    sub_nonneg, Distribution.mean] using hs

private theorem direction (p : ι → K) {s : Finset ι} (hs : 2 < s.card) :
    ∃ d : ι → K, (∀ i ∉ s, d i = 0) ∧ (∑ i, d i = 0) ∧
      (∑ i, d i * p i = 0) ∧ ∃ i, d i ≠ 0 := by
  classical
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := two_lt_card.mp hs
  by_cases hp : p a = p b ∧ p b = p c
  · refine ⟨fun i => (if i = a then 1 else 0) + (if i = b then -1 else 0), ?_, ?_, ?_,
      a, by simp [hab]⟩
    · intro i hi
      have : i ≠ a ∧ i ≠ b := ⟨fun h => hi (h ▸ ha), fun h => hi (h ▸ hb)⟩
      simp [this.1, this.2]
    · simp [sum_add_distrib]
    · simp [add_mul, ite_mul, sum_add_distrib, hp.1]
  · refine ⟨fun i => (if i = a then p b - p c else 0) +
        (if i = b then p c - p a else 0) + (if i = c then p a - p b else 0),
      ?_, ?_, ?_, ?_⟩
    · intro i hi
      have : i ≠ a ∧ i ≠ b ∧ i ≠ c :=
        ⟨fun h => hi (h ▸ ha), fun h => hi (h ▸ hb), fun h => hi (h ▸ hc)⟩
      simp [this.1, this.2.1, this.2.2]
    · simp only [sum_add_distrib, sum_ite_eq', mem_univ, ↓reduceIte]
      ; ring
    · simp only [add_mul, ite_mul, zero_mul, sum_add_distrib, sum_ite_eq', mem_univ, ↓reduceIte]
      ; ring
    · by_cases h : p b = p c
      · refine ⟨c, ?_⟩
        simp only [Ne, hac.symm, hbc.symm, ↓reduceIte, zero_add, sub_eq_zero]
        exact fun h' => hp ⟨h', h⟩
      · exact ⟨a, by simpa [hab, hac] using sub_ne_zero.mpr h⟩

/-- Preserve one expected observable and decrease another, using at most two atoms.
This is valid over both rational and real probability tables. -/
theorem exists_two_support (w : Distribution ι K) (p c : ι → K) :
    ∃ v : Distribution ι K, v.support.card ≤ 2 ∧ v.mean p = w.mean p ∧
      v.mean c ≤ w.mean c := by
  classical
  suffices ∀ s : Finset ι, ∀ w : Distribution ι K, w.support ⊆ s →
      ∃ v : Distribution ι K, v.support.card ≤ 2 ∧ v.mean p = w.mean p ∧
        v.mean c ≤ w.mean c from this w.support w Subset.rfl
  intro s
  induction s using Finset.strongInduction with | H s ih =>
  intro w hws
  by_cases hs : s.card ≤ 2
  · exact ⟨w, (card_le_card hws).trans hs, rfl, le_rfl⟩
  obtain ⟨d, hds, hsum, hp, i, hi⟩ := direction p (lt_of_not_ge hs)
  have hd : ∃ d : ι → K, (∀ i ∉ s, d i = 0) ∧ (∑ i, d i = 0) ∧
      (∑ i, d i * p i = 0) ∧ 0 ≤ ∑ i, d i * c i ∧ ∃ i, 0 < d i := by
    have hpos : ∀ d : ι → K, (∑ i, d i = 0) → (∃ i, d i ≠ 0) → ∃ i, 0 < d i := by
      intro d hz hn
      by_contra h
      have hle : ∀ i, d i ≤ 0 := by simpa using h
      obtain ⟨i, hi⟩ := hn
      have hlt := (hle i).lt_of_ne hi
      have : (∑ j, d j) < 0 := sum_neg' (fun j _ => hle j) ⟨i, mem_univ i, hlt⟩
      linarith
    by_cases hc : 0 ≤ ∑ i, d i * c i
    · exact ⟨d, hds, hsum, hp, hc, hpos d hsum ⟨i, hi⟩⟩
    · refine ⟨fun i => -d i, ?_, ?_, ?_, ?_, ?_⟩
      · intro i hi; simp [hds i hi]
      · simp only [sum_neg_distrib, hsum, neg_zero]
      · simp only [neg_mul, sum_neg_distrib, hp, neg_zero]
      · simp only [neg_mul, sum_neg_distrib]; linarith
      · exact hpos _ (by simp [hsum]) ⟨i, neg_ne_zero.mpr hi⟩
  obtain ⟨d, hds, hsum, hp, hc, hpos⟩ := hd
  let t := univ.filter fun i => 0 < d i
  have ht : t.Nonempty := by
    obtain ⟨i, hi⟩ := hpos
    exact ⟨i, mem_filter.mpr ⟨mem_univ i, hi⟩⟩
  obtain ⟨a, hat, hmin⟩ := t.exists_min_image (fun i => w.weight i / d i) ht
  have hda : 0 < d a := (mem_filter.mp hat).2
  let r := w.weight a / d a
  have hr : 0 ≤ r := div_nonneg (w.nonneg a) hda.le
  have hnew : ∀ i, 0 ≤ w.weight i - r * d i := by
    intro i
    by_cases hdi : 0 < d i
    · have := hmin i (mem_filter.mpr ⟨mem_univ i, hdi⟩)
      exact sub_nonneg.mpr ((le_div_iff₀ hdi).mp this)
    · exact sub_nonneg.mpr ((mul_nonpos_of_nonneg_of_nonpos hr (le_of_not_gt hdi)).trans
        (w.nonneg i))
  let v : Distribution ι K := ⟨fun i => w.weight i - r * d i, hnew, by
    simp only [sum_sub_distrib, ← mul_sum, hsum, w.total, mul_zero, sub_zero]⟩
  have hva : v.weight a = 0 := by
    dsimp only [v, r]
    rw [div_mul_cancel₀ _ hda.ne', sub_self]
  have ha : a ∈ s := by
    by_contra h
    exact hda.ne' (hds a h)
  have hvs : v.support ⊆ s.erase a := by
    intro i hi
    have hiv : 0 < v.weight i := (mem_filter.mp hi).2
    refine mem_erase.mpr ⟨?_, ?_⟩
    · intro h; subst i; rw [hva] at hiv; exact lt_irrefl _ hiv
    · by_contra his
      have hw : w.weight i = 0 := by
        have : ¬ 0 < w.weight i := fun h => his (hws (mem_filter.mpr ⟨mem_univ i, h⟩))
        exact le_antisymm (le_of_not_gt this) (w.nonneg i)
      change 0 < w.weight i - r * d i at hiv
      simp [hw, hds i his] at hiv
  obtain ⟨v', hv', hvp, hvc⟩ := ih (s.erase a) (erase_ssubset ha) v hvs
  refine ⟨v', hv', hvp.trans ?_, hvc.trans ?_⟩
  · change (∑ i, (w.weight i - r * d i) * p i) = _
    simp only [sub_mul, mul_assoc, sum_sub_distrib, ← mul_sum, hp, mul_zero, sub_zero,
      Distribution.mean]
  · change (∑ i, (w.weight i - r * d i) * c i) ≤ _
    simp only [sub_mul, mul_assoc, sum_sub_distrib, ← mul_sum, Distribution.mean]
    exact sub_le_self _ (mul_nonneg hr hc)

/-- A distribution concentrated on two specified indices; they may coincide. -/
@[expose] noncomputable def pair (a b : ι) (t : K) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    Distribution ι K := by
  classical
  exact ⟨fun i => (if i = a then t else 0) + (if i = b then 1 - t else 0),
    fun i => add_nonneg (by split_ifs <;> positivity)
      (by split_ifs <;> linarith), by simp [sum_add_distrib]⟩

/-- Expectation under a two-index mixture, including coincident indices. -/
theorem pair_mean (a b : ι) (t : K) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (f : ι → K) :
    (pair a b t ht₀ ht₁).mean f = t * f a + (1 - t) * f b := by
  classical
  simp [Distribution.mean, pair, add_mul, ite_mul, sum_add_distrib]

/-- A two-index mixture has at most two positive weights. -/
theorem pair_support_card (a b : ι) (t : K) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    (pair a b t ht₀ ht₁).support.card ≤ 2 := by
  classical
  apply le_trans (card_le_card (t := {a, b}) ?_) card_le_two
  intro i hi
  by_contra h
  have hab : i ≠ a ∧ i ≠ b := by simpa using h
  have : 0 < (pair a b t ht₀ ht₁).weight i := (mem_filter.mp hi).2
  simp [pair, hab.1, hab.2] at this

/-- Every table supported on at most two indices has a two-index mixture representation. -/
theorem two_support_representation (w : Distribution ι K) (hw : w.support.card ≤ 2) :
    ∃ a b t, ∃ _ht₀ : 0 ≤ t, ∃ _ht₁ : t ≤ 1,
      ∀ f : ι → K, w.mean f = t * f a + (1 - t) * f b := by
  classical
  have hne := w.support_nonempty
  obtain ⟨a, ha⟩ := hne
  have hwa : 0 < w.weight a := (mem_filter.mp ha).2
  have hsmall : (w.support.erase a).card ≤ 1 := by
    rw [card_erase_of_mem ha]; omega
  have zero_outside : ∀ i ∉ w.support, w.weight i = 0 := by
    intro i hi
    have : ¬ 0 < w.weight i := fun h => hi (mem_filter.mpr ⟨mem_univ i, h⟩)
    exact le_antisymm (le_of_not_gt this) (w.nonneg i)
  by_cases he : (w.support.erase a).Nonempty
  · obtain ⟨b, hb⟩ := he
    have hba : b ≠ a := (mem_erase.mp hb).1
    have hsub : w.support ⊆ {a, b} := by
      intro i hi
      by_cases hia : i = a
      · simp [hia]
      · have hib := card_le_one.mp hsmall i (mem_erase.mpr ⟨hia, hi⟩) b hb
        simp [hib]
    have hsum : ∀ f : ι → K, w.mean f = w.weight a * f a + w.weight b * f b := by
      intro f
      rw [Distribution.mean, ← sum_subset (subset_univ {a, b})]
      · simp [hba.symm]
      · intro i _ hi
        rw [zero_outside i (fun h => hi (hsub h)), zero_mul]
    have htot : w.weight a + w.weight b = 1 := by
      have := hsum (fun _ => 1)
      simpa [Distribution.mean, w.total] using this.symm
    refine ⟨a, b, w.weight a, w.nonneg a, ?_, ?_⟩
    · linarith [w.nonneg b]
    · intro f
      rw [hsum f, show 1 - w.weight a = w.weight b by linarith]
  · have hsub : w.support ⊆ {a} := by
      intro i hi
      by_contra hn
      exact he ⟨i, mem_erase.mpr ⟨by simpa using hn, hi⟩⟩
    have hsum : ∀ f : ι → K, w.mean f = w.weight a * f a := by
      intro f
      rw [Distribution.mean, sum_eq_single a]
      · intro i _ hi
        rw [zero_outside i (fun h => hi (mem_singleton.mp (hsub h))), zero_mul]
      · simp
    have htot : w.weight a = 1 := by
      have := hsum (fun _ => 1)
      simpa [Distribution.mean, w.total] using this.symm
    refine ⟨a, a, 1, zero_le_one, le_rfl, ?_⟩
    intro f
    simp [hsum, htot]

/-- A table with support at most two is exactly a two-index mixture. -/
theorem exists_eq_pair (w : Distribution ι K) (hw : w.support.card ≤ 2) :
    ∃ a b t, ∃ h₀ : 0 ≤ t, ∃ h₁ : t ≤ 1, w = pair a b t h₀ h₁ := by
  classical
  obtain ⟨a,b,t,h₀,h₁,hm⟩ := two_support_representation w hw
  refine ⟨a,b,t,h₀,h₁,?_⟩
  ext i
  have h := hm (fun j => if j = i then 1 else 0)
  simpa [Distribution.mean, pair, mul_ite, eq_comm] using h

private theorem interval_vertex_left (pa pb ca cb η t : K)
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hf : η ≤ t * pa + (1 - t) * pb)
    (hc : ca ≤ cb) :
    ∃ z ∈ ({0, 1, (η - pb) / (pa - pb)} : Finset K),
      0 ≤ z ∧ z ≤ 1 ∧ η ≤ z * pa + (1 - z) * pb ∧
        z * ca + (1 - z) * cb ≤ t * ca + (1 - t) * cb := by
  by_cases hpa : η ≤ pa
  · refine ⟨1, by simp, zero_le_one, le_rfl, by simpa using hpa, ?_⟩
    nlinarith
  · have hab : pa < pb := by
      by_contra h
      have : pb ≤ pa := le_of_not_gt h
      nlinarith [mul_nonneg (sub_nonneg.mpr ht₁) (sub_nonneg.mpr this)]
    have hpb : η ≤ pb := by nlinarith [mul_nonneg ht₀ (sub_nonneg.mpr hab.le)]
    let z := (pb - η) / (pb - pa)
    have hd : 0 < pb - pa := sub_pos.mpr hab
    have hz₀ : 0 ≤ z := div_nonneg (sub_nonneg.mpr hpb) hd.le
    have hz₁ : z ≤ 1 := (div_le_one hd).mpr (by linarith)
    have htz : t ≤ z := (le_div_iff₀ hd).mpr (by nlinarith)
    have hz : z * (pb - pa) = pb - η := div_mul_cancel₀ _ hd.ne'
    have hze : z = (η - pb) / (pa - pb) := by
      dsimp only [z]
      rw [show η - pb = -(pb - η) by ring, show pa - pb = -(pb - pa) by ring,
        neg_div_neg_eq]
    refine ⟨z, by simp [hze], hz₀, hz₁, by nlinarith, ?_⟩
    nlinarith [mul_nonneg (sub_nonneg.mpr htz) (sub_nonneg.mpr hc)]

private theorem interval_vertex (pa pb ca cb η t : K)
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hf : η ≤ t * pa + (1 - t) * pb) :
    ∃ z ∈ ({0, 1, (η - pb) / (pa - pb)} : Finset K),
      0 ≤ z ∧ z ≤ 1 ∧ η ≤ z * pa + (1 - z) * pb ∧
        z * ca + (1 - z) * cb ≤ t * ca + (1 - t) * cb := by
  classical
  by_cases hc : ca ≤ cb
  · exact interval_vertex_left pa pb ca cb η t ht₀ ht₁ hf hc
  · obtain ⟨z, hz, hz₀, hz₁, hzf, hzc⟩ :=
      interval_vertex_left pb pa cb ca η (1-t) (by linarith) (by linarith)
        (by nlinarith) (le_of_not_ge hc)
    by_cases heq : pa = pb
    · refine ⟨0, by simp, le_rfl, zero_le_one, ?_, ?_⟩
      · nlinarith [mul_nonneg ht₀ (sub_nonneg.mpr (le_of_eq heq))]
      · nlinarith [mul_nonneg ht₀ (sub_nonneg.mpr (le_of_not_ge hc))]
    · refine ⟨1-z, ?_, by linarith, by linarith, by nlinarith, by nlinarith⟩
      simp only [mem_insert, mem_singleton] at hz ⊢
      rcases hz with rfl | rfl | rfl
      · exact Or.inr (Or.inl (by ring))
      · exact Or.inl (by ring)
      · right; right
        field_simp
        ; ring

open scoped Classical in
/-- The finitely many endpoint/intersection candidates for a one-constraint LP. -/
@[expose] noncomputable def vertices (p : ι → K) (η : K) : Finset (ι × ι × K) :=
  univ.biUnion fun a => univ.biUnion fun b =>
    ({0, 1, (η - p b) / (p a - p b)} : Finset K).image fun t => (a, b, t)

omit [IsStrictOrderedRing K] in
/-- Membership in the finite endpoint/intersection candidate set. -/
theorem mem_vertices (p : ι → K) (η t : K) (a b : ι) :
    (a,b,t) ∈ vertices p η ↔ t ∈ ({0,1,(η-p b)/(p a-p b)} : Finset K) := by
  classical
  simp [vertices]
  grind

/-- Every feasible table is dominated by a feasible endpoint/intersection candidate. -/
theorem exists_vertex_le (w : Distribution ι K) (p c : ι → K) (η : K)
    (hw : η ≤ w.mean p) :
    ∃ a b t, (a, b, t) ∈ vertices p η ∧ 0 ≤ t ∧ t ≤ 1 ∧
      η ≤ t * p a + (1-t) * p b ∧ t * c a + (1-t) * c b ≤ w.mean c := by
  classical
  obtain ⟨v, hv, hvp, hvc⟩ := exists_two_support w p c
  obtain ⟨a, b, t, ht₀, ht₁, hm⟩ := two_support_representation v hv
  obtain ⟨z, hz, hz₀, hz₁, hzp, hzc⟩ := interval_vertex (p a) (p b) (c a) (c b) η t
    ht₀ ht₁ (by rw [← hm, hvp]; exact hw)
  refine ⟨a, b, z, ?_, hz₀, hz₁, hzp, hzc.trans ?_⟩
  · simp only [vertices, mem_biUnion, mem_univ, true_and, mem_image]
    exact ⟨a, b, z, hz, rfl⟩
  · rw [← hm]; exact hvc

/-- A feasible one-constraint finite LP has an attained optimum supported on at most two
indices. This includes rational coefficients and rational probabilities, without compactness
or a hypothesized optimizer. -/
theorem exists_optimal_two (p c : ι → K) (η : K)
    (hfeas : ∃ w : Distribution ι K, η ≤ w.mean p) :
    ∃ w : Distribution ι K, w.support.card ≤ 2 ∧ η ≤ w.mean p ∧
      ∀ v : Distribution ι K, η ≤ v.mean p → w.mean c ≤ v.mean c := by
  classical
  let s := (vertices p η).filter fun (a,b,t) =>
    0 ≤ t ∧ t ≤ 1 ∧ η ≤ t * p a + (1-t) * p b
  let cost : ι × ι × K → K := fun (a,b,t) => t * c a + (1-t) * c b
  have hs : s.Nonempty := by
    obtain ⟨v, hv⟩ := hfeas
    obtain ⟨a,b,t,hmem,h₀,h₁,hp,_⟩ := exists_vertex_le v p c η hv
    exact ⟨(a,b,t), mem_filter.mpr ⟨hmem,h₀,h₁,hp⟩⟩
  obtain ⟨⟨a,b,t⟩, hmem, hmin⟩ := s.exists_min_image cost hs
  obtain ⟨_, ht₀, ht₁, htp⟩ := mem_filter.mp hmem
  refine ⟨pair a b t ht₀ ht₁, pair_support_card a b t ht₀ ht₁,
    by rwa [pair_mean], ?_⟩
  intro v hv
  obtain ⟨a',b',t',hmem',h₀,h₁,hp,hc⟩ := exists_vertex_le v p c η hv
  rw [pair_mean]
  exact (hmin (a',b',t') (mem_filter.mpr ⟨hmem',h₀,h₁,hp⟩)).trans hc

end Cslib.Optimization.OneConstraint
