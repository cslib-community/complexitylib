/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.MatrixMultiplication.Schonhage.Boxes
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Finite box counts and value recurrence

The canonical-box bijection counts boxes by a completed leaf and a number of stars.
`card_boxes_le` bounds their total by `(m + 1)` times the sum of the existing `beta`
counts. It needs only `m ≤ L` and `t ≤ m`; the source's stronger `10 * m ≤ L` is unnecessary.

`boxValue` recursively replaces the highest star by each of the ten existing terms.
`boxValue_eq_val` proves that it computes the signed cube value when the supplied star
count is exact. This recurrence may recompute subproblems: it is neither a memoized table
nor a native program and carries no preprocessing-time or space theorem.

Adapted from [AlmanWilliams2026, Lemma 29] and
[Lemma29.lean](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Sec4/Lemma29.lean) at
`anthropics/formal-math@16a5ce41304fcdaea4e0be7c132e1c361dc26da5`.
The encodings, terms, leaf order and `beta` counts are the existing local notions.
-/

public section

open Finset

namespace Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- All cubes satisfying the box conditions at the selected parameters. -/
@[expose] def boxes (L m t : ℕ) : Finset (Cube L) := univ.filter (IsBox m t)

/-- Boxes whose star count is exactly `e`. -/
@[expose] def boxesWithStars (L m t e : ℕ) : Finset (Cube L) :=
  (boxes L m t).filter fun π => π.starLevels.card = e

/-- Finite recursive value evaluation, indexed by the exact number of stars. -/
@[expose] def boxValue {L : ℕ} (encA encB : Leaf L → ℤ) : ℕ → Cube L → ℤ
  | 0, π => encA π.starsToP0 * encB π.starsToP0
  | e + 1, π =>
    if h : π.starLevels.Nonempty then
      ∑ lam : Term, boxValue encA encB e (π.replace (π.starLevels.max' h) lam)
    else 0

/-- Membership is exactly the two box conditions. -/
@[simp] theorem mem_boxes {L m t : ℕ} {π : Cube L} : π ∈ boxes L m t ↔ IsBox m t π := by
  simp [boxes]

/-- Membership combines the box conditions with an exact star count. -/
@[simp] theorem mem_boxesWithStars {L m t e : ℕ} {π : Cube L} :
    π ∈ boxesWithStars L m t e ↔ IsBox m t π ∧ (Cube.starLevels π).card = e := by
  simp [boxesWithStars, boxes]



private lemma card_leaves_P0 {L m f : ℕ} (hmL : m ≤ L) (hf : f ≤ m) :
    (univ.filter fun τ : Leaf L => (P0Levels τ).card = f).card = beta L m (m - f) := by
  rw [← card_filter_order_eq hmL (m - f) (Nat.sub_le _ _)]
  congr 1
  ext τ
  rw [mem_filter, mem_filter, order]
  simp only [mem_univ, true_and]
  omega

/-- Boxes with a fixed combined star/P0 count correspond to completed leaves and star counts. -/
theorem card_boxes_with_P0_count (L m t f : ℕ) (hmL : m ≤ L) (hf : f ≤ m - t) :
    ((boxes L m t).filter fun π => (Cube.starLevels π).card + (Cube.P0Levels π).card = f).card
      = (f + 1) * beta L m (m - f) := by
  have hpairs : ((univ.filter fun τ : Leaf L => (P0Levels τ).card = f) ×ˢ range (f + 1)).card
      = (f + 1) * beta L m (m - f) := by
    rw [card_product, card_leaves_P0 hmL (by omega), card_range, mul_comm]
  have hpair : ∀ p ∈ (univ.filter fun τ : Leaf L => (P0Levels τ).card = f) ×ˢ range (f + 1),
      (P0Levels p.1).card = f ∧ p.2 < f + 1 := fun p hp =>
    ⟨(mem_filter.1 (mem_product.1 hp).1).2, mem_range.1 (mem_product.1 hp).2⟩
  rw [← hpairs]
  refine card_bij' (fun π _ => (Cube.starsToP0 π, (Cube.starLevels π).card))
    (fun p _ => starLowest p.2 p.1) (fun π hπ => ?_) (fun p hp => ?_) (fun π hπ => ?_)
    fun p hp => ?_
  · -- the pair of such a box is such a pair
    have hf := (mem_filter.1 hπ).2
    simp only [mem_product, mem_filter, mem_univ, true_and, mem_range,
      card_P0Levels_starsToP0]
    omega
  · -- the cube of such a pair is such a box: its leaf is the leaf of the pair
    obtain ⟨hτ, -⟩ := hpair p hp
    rw [mem_filter, mem_boxes, ← card_P0Levels_starsToP0, starsToP0_starLowest]
    exact ⟨isBox_starLowest m t p.2 p.1 (by omega), hτ⟩
  · -- from a box to its pair and back
    exact (eq_starLowest_starsToP0 π (mem_boxes.1 (mem_filter.1 hπ).1).2).symm
  · -- from a pair `(τ, e)` to its cube and back: the cube has `min e f = e` stars
    obtain ⟨hτ, he⟩ := hpair p hp
    rw [starsToP0_starLowest, starLevels_starLowest, card_lowest, hτ,
      min_eq_left (by omega)]

/-- The total count is bounded by completed-leaf counts and at most `m + 1` star counts. -/
theorem card_boxes_le (L m t : ℕ) (hmL : m ≤ L) (ht : t ≤ m) :
    (boxes L m t).card ≤ (m + 1) * ∑ d ∈ Finset.Icc t m, beta L m d := by
  have hsort : (boxes L m t).card = ∑ f ∈ range (m - t + 1),
      ((boxes L m t).filter
        fun π => (Cube.starLevels π).card + (Cube.P0Levels π).card = f).card := by
    refine card_eq_sum_card_fiberwise fun π hπ => ?_
    have hi := (mem_boxes.1 (mem_coe.1 hπ)).1
    simp only [coe_range, Set.mem_Iio]
    omega
  have hreflect : ∑ f ∈ range (m - t + 1), beta L m (m - f) = ∑ d ∈ Finset.Icc t m, beta L m d := by
    rw [range_eq_Ico, sum_Ico_reflect _ _ (by omega)]
    congr 1
    ext d
    simp only [mem_Ico, mem_Icc]
    omega
  rw [hsort, ← hreflect, mul_sum]
  refine sum_le_sum fun f hf => ?_
  have hfm : f < m - t + 1 := mem_range.1 hf
  rw [card_boxes_with_P0_count L m t f (by omega) (by omega)]
  exact Nat.mul_le_mul_right _ (by omega)



/-- Boxes without stars are exactly the eligible fully fixed leaves. -/
theorem boxesWithStars_zero_iff {L : ℕ} (m t : ℕ) (π : Cube L) :
    π ∈ boxesWithStars L m t 0 ↔ ∃ τ : Leaf L, (P0Levels τ).card ≤ m - t ∧ π = Cube.ofLeaf τ := by
  rw [mem_boxesWithStars]
  constructor
  · rintro ⟨hbox, hstar⟩
    refine ⟨Cube.starsToP0 π, ?_,
      Cube.eq_ofLeaf_of_starLevels_eq_empty π (card_eq_zero.1 hstar)⟩
    rw [card_P0Levels_starsToP0]
    exact hbox.1
  · rintro ⟨τ, hτ, rfl⟩
    rw [IsBox, Cube.starLevels_ofLeaf, Cube.P0Levels_ofLeaf]
    simpa using hτ

/-- Replacing the highest star gives a box with one fewer star. -/
theorem replace_highest_mem_boxesWithStars {L m t e : ℕ} {π : Cube L}
    (hπ : π ∈ boxesWithStars L m t (e + 1))
    (hne : (Cube.starLevels π).Nonempty) (lam : Term) :
    Cube.replace π ((Cube.starLevels π).max' hne) lam ∈ boxesWithStars L m t e := by
  obtain ⟨⟨hcount, hbelow⟩, hcard⟩ := mem_boxesWithStars.1 hπ
  have hstar :
      (Cube.starLevels (Cube.replace π ((Cube.starLevels π).max' hne) lam)).card = e := by
    rw [Cube.starLevels_replace, card_erase_of_mem (max'_mem _ hne), hcard,
      Nat.add_sub_cancel]
  have hP0 := Cube.P0Levels_replace_subset π ((Cube.starLevels π).max' hne) lam
  refine mem_boxesWithStars.2 ⟨⟨?_, fun k hk k' hk' => ?_⟩, hstar⟩
  · -- One star fewer (`hstar`, `hcard`) and at most one symbol `P₀` more (`hmore`), so (i) stays.
    have hmore := (card_le_card hP0).trans (card_insert_le _ _)
    omega
  · -- The new symbol is above the remaining stars, and so are the old symbols `P₀`, by (ii).
    rw [Cube.starLevels_replace, mem_erase] at hk
    rcases mem_insert.1 (hP0 hk') with hnew | hold
    · exact hnew ▸ lt_of_le_of_ne (le_max' _ k hk.2) hk.1
    · exact hbelow k hk.2 k' hold

/-- The finite recurrence agrees with the signed encoding-product sum of a box. -/
theorem boxValue_eq_val (L m t e : ℕ) (a : LeftStr L → ℤ) (b : RightStr L → ℤ) (π : Cube L)
    (hπ : π ∈ boxesWithStars L m t e) :
    boxValue (encodingL a) (encodingR b) e π = Cube.val a b π := by
  induction e generalizing π with
  | zero =>
    obtain ⟨τ, -, rfl⟩ := (boxesWithStars_zero_iff m t π).1 hπ
    rw [Cube.val_ofLeaf]
    rfl
  | succ e ih =>
    have hne : (Cube.starLevels π).Nonempty :=
      card_pos.1 ((mem_boxesWithStars.1 hπ).2 ▸ Nat.succ_pos e)
    rw [boxValue, dite_eq_left hne,
      Cube.val_eq_sum_replace a b π _ (Cube.mem_starLevels.1 (max'_mem _ hne))]
    exact sum_congr rfl fun lam _ => ih _ (replace_highest_mem_boxesWithStars hπ hne lam)

end Cslib.Algorithms.MatrixMultiplication.Schonhage
