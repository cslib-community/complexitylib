/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Foundations.Geometry.Orthogonal.Subdivision
import Mathlib.Analysis.Convex.Basic
import Mathlib.Tactic.Linarith

/-!
# Integer-grid isolation for local drawing replacements

An orthogonal segment with integer endpoints that enters the open unit box about an integer
point must contain that integer point. In a simple route, only the initial segment can contain
its initial vertex. These facts supply uniform local isolation without searching for a
drawing-dependent real radius.

## Main definitions

* `nearGridPoint`: the open unit square centered on an integer point.

## Main results

* `gridPoint_mem_segment_of_near`, `gridPoint_mem_support_of_near`.
* `segment_eq_first_of_head_mem`, `mem_first_segment_of_near_head`.

## References

These integer-grid separation observations and proofs are original.
-/

@[expose] public section

namespace Cslib.Orthogonal


/-- The open unit square centered on an integer grid point. -/
def nearGridPoint (c : Point) (p : ℝ × ℝ) : Prop :=
  (c.1 : ℝ) - 1 < p.1 ∧ p.1 < (c.1 : ℝ) + 1 ∧
    (c.2 : ℝ) - 1 < p.2 ∧ p.2 < (c.2 : ℝ) + 1

private theorem int_between_of_near {a b c : ℤ} {x : ℝ}
    (ha : (a : ℝ) ≤ x) (hb : x ≤ (b : ℝ))
    (hc : (c : ℝ) - 1 < x ∧ x < (c : ℝ) + 1) : a ≤ c ∧ c ≤ b := by
  constructor
  · by_contra h
    have h' : c + 1 ≤ a := by omega
    have h'' : (c : ℝ) + 1 ≤ (a : ℝ) := by exact_mod_cast h'
    linarith [hc.2]
  · by_contra h
    have h' : b ≤ c - 1 := by omega
    have h'' : (b : ℝ) ≤ (c : ℝ) - 1 := by exact_mod_cast h'
    linarith [hc.1]

/-- Distinct grid points are not within the open unit box about one another. -/
theorem eq_of_nearGridPoint {a c : Point} (h : nearGridPoint c (realPoint a)) : a = c := by
  have hx := int_between_of_near (a := a.1) (b := a.1) le_rfl le_rfl ⟨h.1, h.2.1⟩
  have hy := int_between_of_near (a := a.2) (b := a.2) le_rfl le_rfl ⟨h.2.2.1, h.2.2.2⟩
  exact Prod.ext (le_antisymm hx.1 hx.2) (le_antisymm hy.1 hy.2)

/-- Entering the open unit box about a grid point forces an integer orthogonal segment
to contain that grid point. The statement concerns all real points of the segment. -/
theorem gridPoint_mem_segment_of_near {a b c : Point} (hab : a.1 = b.1 ∨ a.2 = b.2)
    {p : ℝ × ℝ} (hp : p ∈ segment a b) (hc : nearGridPoint c p) :
    realPoint c ∈ segment a b := by
  have hb := mem_segment_bounds hp
  change (min (a.1 : ℝ) (b.1 : ℝ) ≤ p.1 ∧ p.1 ≤ max (a.1 : ℝ) (b.1 : ℝ)) ∧
    (min (a.2 : ℝ) (b.2 : ℝ) ≤ p.2 ∧ p.2 ≤ max (a.2 : ℝ) (b.2 : ℝ)) at hb
  have hx : ((min a.1 b.1 : ℤ) : ℝ) ≤ p.1 ∧
      p.1 ≤ ((max a.1 b.1 : ℤ) : ℝ) := by
    simpa only [Int.cast_min, Int.cast_max] using hb.1
  have hy : ((min a.2 b.2 : ℤ) : ℝ) ≤ p.2 ∧
      p.2 ≤ ((max a.2 b.2 : ℤ) : ℝ) := by
    simpa only [Int.cast_min, Int.cast_max] using hb.2
  have hx' := int_between_of_near hx.1 hx.2 ⟨hc.1, hc.2.1⟩
  have hy' := int_between_of_near hy.1 hy.2 ⟨hc.2.2.1, hc.2.2.2⟩
  exact (realPoint_mem_segment_iff hab).2 ⟨hx'.1, hx'.2, hy'.1, hy'.2⟩

/-- A nonincident integer vertex has a whole open unit box disjoint from a route. -/
theorem gridPoint_mem_support_of_near {r : Route} (hr : IsOrthogonal r)
    {c : Point} {p : ℝ × ℝ} (hp : p ∈ support r) (hc : nearGridPoint c p) :
    realPoint c ∈ support r := by
  rcases hp with ⟨a, ha, rfl⟩ | ⟨e, he, hp⟩
  · exact Or.inl ⟨a, ha, congrArg realPoint (eq_of_nearGridPoint hc).symm⟩
  · exact Or.inr ⟨e, he, gridPoint_mem_segment_of_near (hr e he).1 hp hc⟩

/-- In a simple route, the initial grid vertex lies on no segment other than the first. -/
theorem segment_eq_first_of_head_mem {a b : Point} {r : Route}
    (hr : IsSimple (a :: b :: r)) {e : Point × Point}
    (he : e ∈ (a :: b :: r).consecutivePairs) (ha : realPoint a ∈ segment e.1 e.2) :
    e = (a, b) := by
  by_contra hne
  have he' : e ∈ (b :: r).consecutivePairs := by
    simpa only [List.consecutivePairs, List.tail_cons, List.zip_cons_cons, List.mem_cons,
      hne, false_or] using he
  have hfirst : (a, b) ∈ (a :: b :: r).consecutivePairs := by
    simp [List.consecutivePairs]
  have ha' : realPoint a ∈ segment a b := _root_.left_mem_segment ℝ _ _
  have hh := (hr.2 e he (a, b) hfirst hne (realPoint a) ha ha').1
  have hnot : a ∉ b :: r := (List.nodup_cons.mp hr.1).1
  have hepoints := List.of_mem_zip he'
  rcases hh with hh | hh
  · exact hnot (realPoint_injective hh ▸ hepoints.1)
  · exact hnot (realPoint_injective hh ▸ List.mem_of_mem_tail hepoints.2)

/-- The open unit box about a route's initial vertex meets only its first segment. -/
theorem mem_first_segment_of_near_head {a b : Point} {r : Route}
    (ho : IsOrthogonal (a :: b :: r)) (hs : IsSimple (a :: b :: r))
    {p : ℝ × ℝ} (hp : p ∈ support (a :: b :: r)) (ha : nearGridPoint a p) :
    p ∈ segment a b := by
  rcases hp with ⟨q, hq, rfl⟩ | ⟨e, he, hp⟩
  · obtain rfl := eq_of_nearGridPoint ha
    exact _root_.left_mem_segment ℝ _ _
  · have hea := gridPoint_mem_segment_of_near (ho e he).1 hp ha
    obtain rfl := segment_eq_first_of_head_mem hs he hea
    exact hp

/-- The tail of a simple proper orthogonal route avoids the entire open unit box about
the route's initial grid vertex. -/
theorem not_near_head_tail {a b : Point} {r : Route}
    (ho : IsOrthogonal (a :: b :: r)) (hs : IsSimple (a :: b :: r))
    {p : ℝ × ℝ} (hp : p ∈ support (b :: r)) : ¬ nearGridPoint a p := by
  intro hn
  have ha := gridPoint_mem_support_of_near ho.of_cons hp hn
  have hab : a = b := realPoint_injective
    (first_segment_tail_contact hs (_root_.left_mem_segment ℝ _ _) ha)
  exact (ho (a, b) (by simp [List.consecutivePairs])).2 hab

/-- Cutting the first segment at one of its grid points preserves proper axis alignment
provided the new segment has not collapsed. -/
theorem axisAligned_cut_first {a b c : Point} (hab : a.1 = b.1 ∨ a.2 = b.2)
    (hc : realPoint c ∈ segment a b) (hcb : c ≠ b) : AxisAligned c b := by
  have hb := (realPoint_mem_segment_iff hab).1 hc
  refine ⟨?_, hcb⟩
  rcases hab with hab | hab
  · left
    omega
  · right
    omega

/-- Removing an initial portion of the first segment only shrinks a route's real support. -/
theorem support_cut_first_subset {a b c : Point} {r : Route}
    (hc : realPoint c ∈ segment a b) : support (c :: b :: r) ⊆ support (a :: b :: r) := by
  have hsub : segment c b ⊆ segment a b :=
    (convex_segment (𝕜 := ℝ) (realPoint a) (realPoint b)).segment_subset hc
      (_root_.right_mem_segment ℝ _ _)
  rw [support_cons_cons, support_cons_cons]
  exact Set.union_subset_union_left _ hsub

/-- Endpoint cutting preserves a route's orthogonality. -/
theorem isOrthogonal_cut_first {a b c : Point} {r : Route}
    (hr : IsOrthogonal (a :: b :: r)) (hc : realPoint c ∈ segment a b) (hcb : c ≠ b) :
    IsOrthogonal (c :: b :: r) := by
  intro e he
  simp only [List.consecutivePairs, List.tail_cons, List.zip_cons_cons, List.mem_cons] at he
  rcases he with rfl | he
  · exact axisAligned_cut_first (hr (a, b) (by simp [List.consecutivePairs])).1 hc hcb
  · exact hr.of_cons e he

/-- Moving the initial endpoint forward within its first segment preserves continuous
simplicity. No repeated point or contact with a later segment is introduced. -/
theorem isSimple_cut_first {a b c : Point} {r : Route}
    (hr : IsSimple (a :: b :: r)) (hc : realPoint c ∈ segment a b) (hcb : c ≠ b) :
    IsSimple (c :: b :: r) := by
  have hsub : segment c b ⊆ segment a b :=
    (convex_segment (𝕜 := ℝ) (realPoint a) (realPoint b)).segment_subset hc
      (_root_.right_mem_segment ℝ _ _)
  have hnot : c ∉ b :: r := by
    intro hm
    have hp : realPoint c ∈ support (b :: r) := Or.inl ⟨c, hm, rfl⟩
    exact hcb (realPoint_injective (first_segment_tail_contact hr hc hp))
  have hne (e : Point × Point) (he : e ∈ (b :: r).consecutivePairs) : (a, b) ≠ e := by
    intro h
    have hp := (List.of_mem_zip he).1
    have hnot' := (List.nodup_cons.mp hr.1).1
    exact hnot' (by simpa only [← h] using hp)
  have hmem (e : Point × Point) (he : e ∈ (b :: r).consecutivePairs) :
      e ∈ (a :: b :: r).consecutivePairs := by
    simpa only [List.consecutivePairs, List.tail_cons, List.zip_cons_cons, List.mem_cons]
      using Or.inr he
  have hcontact (e : Point × Point) (he : e ∈ (b :: r).consecutivePairs) :
      EndpointContacts c b e.1 e.2 := by
    intro p hp hq
    have hp' := hsub hp
    have htail : p ∈ support (b :: r) := Or.inr ⟨e, he, hq⟩
    have hpb := first_segment_tail_contact hr hp' htail
    exact ⟨Or.inr hpb,
      (hr.2 (a, b) (by simp [List.consecutivePairs]) e (hmem e he) (hne e he) p hp' hq).2⟩
  refine ⟨List.nodup_cons.mpr ⟨hnot, hr.1.tail⟩, ?_⟩
  intro e he f hf hneq
  simp only [List.consecutivePairs, List.tail_cons, List.zip_cons_cons, List.mem_cons] at he hf
  rcases he with rfl | he <;> rcases hf with rfl | hf
  · exact False.elim (hneq rfl)
  · exact hcontact f hf
  · exact (hcontact e he).symm
  · exact hr.of_cons.2 e he f hf hneq

/-- Manhattan length is additive when a grid point lies on an orthogonal segment. -/
theorem length_add_cut_first {a b c : Point} (hab : a.1 = b.1 ∨ a.2 = b.2)
    (hc : realPoint c ∈ segment a b) : length a c + length c b = length a b := by
  have h := (realPoint_mem_segment_iff hab).1 hc
  simp only [length]
  omega

/-- Endpoint cutting subtracts exactly the removed Manhattan length. -/
theorem wireLength_cut_first {a b c : Point} {r : Route}
    (hab : a.1 = b.1 ∨ a.2 = b.2) (hc : realPoint c ∈ segment a b) :
    wireLength (c :: b :: r) + length a c = wireLength (a :: b :: r) := by
  have h := length_add_cut_first hab hc
  simp only [wireLength, List.consecutivePairs, List.tail_cons, List.zip_cons_cons,
    List.map_cons, List.sum_cons]
  omega

end Cslib.Orthogonal
