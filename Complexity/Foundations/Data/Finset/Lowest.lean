/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.Finset.Card

/-!
# Initial segments of finite linearly ordered sets

`Finset.lowest k s` retains the elements with fewer than `k` predecessors in `s`.
Its members precede every omitted member, and its cardinality is `min k s.card`.
This finite rank specification avoids choosing an enumeration in the clients.

The proofs generalize the ordered-level argument in
[AlmanWilliams2026, Section 4.2], primary formal source
[Boxes.lean](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Sec4/Boxes.lean) at `anthropics/formal-math@16a5ce41304fcdaea4e0be7c132e1c361dc26da5`.
The concrete consumer is the canonical tensor-box construction. No execution bound is asserted.
-/

public section

namespace Finset

variable {α : Type*} [LinearOrder α]

/-- The elements having fewer than `k` predecessors in the finite set. -/
@[expose] def lowest (k : ℕ) (s : Finset α) : Finset α :=
  s.filter fun x => (s.filter fun y => y < x).card < k

/-- The selected elements belong to the original set. -/
theorem lowest_subset (k : ℕ) (S : Finset α) : lowest k S ⊆ S :=
  filter_subset _ _

/-- Membership is determined by the number of strictly smaller elements in the set. -/
@[simp] theorem mem_lowest {k : ℕ} {S : Finset α} {ℓ : α} :
    ℓ ∈ lowest k S ↔ ℓ ∈ S ∧ (S.filter fun ℓ' => ℓ' < ℓ).card < k := by
  simp [lowest]

private lemma card_below_strictMonoOn (S : Finset α) :
    StrictMonoOn (fun ℓ => (S.filter fun x => x < ℓ).card) S := by
  intro ℓ hℓ ℓ' _ hlt
  refine card_lt_card ⟨fun x hx => ?_, fun hsub => ?_⟩
  · exact mem_filter.2 ⟨(mem_filter.1 hx).1, (mem_filter.1 hx).2.trans hlt⟩
  · exact lt_irrefl ℓ (mem_filter.1 (hsub (mem_filter.2 ⟨hℓ, hlt⟩))).2

/-- Every selected element precedes every unselected element of the set. -/
theorem lowest_lt {k : ℕ} {S : Finset α} {ℓ ℓ' : α} (hℓ : ℓ ∈ lowest k S)
    (hℓ' : ℓ' ∈ S \ lowest k S) : ℓ < ℓ' := by
  obtain ⟨hS, hbelow⟩ := mem_lowest.1 hℓ
  obtain ⟨hS', hnot⟩ := mem_sdiff.1 hℓ'
  by_contra hlt
  exact hnot (mem_lowest.2
    ⟨hS', ((card_below_strictMonoOn S).monotoneOn hS' hS (not_lt.1 hlt)).trans_lt hbelow⟩)

/-- An initial subset is determined by its cardinality. -/
theorem eq_lowest_of_lt {S T : Finset α} (hT : T ⊆ S)
    (h : ∀ ℓ ∈ T, ∀ ℓ' ∈ S \ T, ℓ < ℓ') : T = lowest T.card S := by
  ext ℓ
  rw [mem_lowest]
  constructor
  · -- Predecessors of a selected element belong to the initial subset.
    refine fun hℓ => ⟨hT hℓ, card_lt_card ⟨fun x hx => ?_, fun hsub => ?_⟩⟩
    · by_contra hxT
      exact lt_asymm (mem_filter.1 hx).2 (h ℓ hℓ x (mem_sdiff.2 ⟨(mem_filter.1 hx).1, hxT⟩))
    · exact lt_irrefl ℓ (mem_filter.1 (hsub hℓ)).2
  · -- All selected elements precede an omitted element.
    rintro ⟨hℓS, hcard⟩
    by_contra hℓT
    refine absurd (card_le_card fun x hx => ?_) (not_le.2 hcard)
    exact mem_filter.2 ⟨hT hx, h x hx ℓ (mem_sdiff.2 ⟨hℓS, hℓT⟩)⟩

private lemma image_card_below (S : Finset α) :
    (S.image fun ℓ => (S.filter fun x => x < ℓ).card) = range S.card := by
  refine eq_of_subset_of_card_le (fun n hn => ?_) ?_
  · obtain ⟨ℓ, hℓ, rfl⟩ := mem_image.1 hn
    exact mem_range.2
      (card_lt_card ⟨filter_subset _ _, fun hsub => lt_irrefl ℓ (mem_filter.1 (hsub hℓ)).2⟩)
  · rw [card_image_of_injOn (card_below_strictMonoOn S).injOn, card_range]

/-- Selection saturates at the size of the original set. -/
theorem card_lowest (k : ℕ) (S : Finset α) : (lowest k S).card = min k S.card := by
  have hinj := (card_below_strictMonoOn S).injOn.mono (coe_subset.2 (lowest_subset k S))
  have hrange : ((range S.card).filter fun n => n < k) = range (min k S.card) := by
    ext n
    simp only [mem_filter, mem_range, lt_min_iff, and_comm]
  rw [← card_image_of_injOn hinj, ← card_range (min k S.card), ← hrange, ← image_card_below,
    filter_image]
  rfl

end Finset
