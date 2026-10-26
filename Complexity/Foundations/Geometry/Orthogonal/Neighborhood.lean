/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Foundations.Geometry.Orthogonal.Subdivision
import Mathlib.Tactic.Abel
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs

/-!
# Integer points and local neighborhoods of orthogonal unit paths

## Main definitions

* `Cslib.Orthogonal.StraightThrough`: a consecutive three-point neighborhood in either direction.

## Main results

* `Cslib.Orthogonal.mem_iff_realPoint_mem_support`: for unit paths, integer support membership
  is exactly membership in the finite listed-point data.
* `Cslib.Orthogonal.StraightThrough.getD_neighbors`: exact indexed predecessor/successor lookups.
* `Cslib.Orthogonal.subdivide_horizontal`, `.subdivide_vertical`: strict interior grid points
  retain consecutive straight neighborhoods after subdivision.
* `Cslib.Orthogonal.point_bounds_of_mem_support`: listed-point bounds hold on all integer support.

## References

These are original finite-list proofs of elementary lattice-segment facts.
-/

@[expose] public section

namespace Cslib.Orthogonal

/-- A unit path passes straight through `p`, with its two immediate neighbors `p-d` and `p+d`.
The three points occur consecutively, in either orientation. -/
def StraightThrough (r : Route) (p d : Point) : Prop :=
  [p - d, p, p + d] <:+: r ∨ [p + d, p, p - d] <:+: r

/-- An integer point on a unit segment is one of its endpoints. -/
theorem eq_endpoint_of_mem_unit_segment {a b p : Point} (hab : length a b = 1)
    (hp : realPoint p ∈ segment a b) : p = a ∨ p = b := by
  have hb := (realPoint_mem_segment_iff (axisAligned_of_length_eq_one hab).1).1 hp
  rcases a with ⟨ax, ay⟩
  rcases b with ⟨bx, by'⟩
  rcases p with ⟨px, py⟩
  simp only [length] at hab
  simp only [Prod.mk.injEq]
  omega

/-- A finite unit path lists every integer point in its continuous real support. -/
theorem mem_iff_realPoint_mem_support {r : Route}
    (hr : ∀ e ∈ r.consecutivePairs, length e.1 e.2 = 1) (p : Point) :
    p ∈ r ↔ realPoint p ∈ support r := by
  constructor
  · exact fun hp => Or.inl ⟨p, hp, rfl⟩
  · rintro (⟨a, ha, heq⟩ | ⟨e, he, hp⟩)
    · exact realPoint_injective heq ▸ ha
    · have hm := List.of_mem_zip he
      rcases eq_endpoint_of_mem_unit_segment (hr e he) hp with rfl | rfl
      · exact hm.1
      · exact List.mem_of_mem_tail hm.2

/-- A rectangle containing every listed point also contains every integer point of the
continuous orthogonal support. -/
theorem point_bounds_of_mem_support {r : Route} (hr : IsOrthogonal r) {w h : ℤ}
    (hb : ∀ p ∈ r, 0 ≤ p.1 ∧ p.1 ≤ w ∧ 0 ≤ p.2 ∧ p.2 ≤ h)
    {p : Point} (hp : realPoint p ∈ support r) :
    0 ≤ p.1 ∧ p.1 ≤ w ∧ 0 ≤ p.2 ∧ p.2 ≤ h := by
  rw [realPoint_mem_support_iff hr] at hp
  rcases hp with hp | ⟨e, he, hp⟩
  · exact hb p hp
  · have hm := List.of_mem_zip he
    have ha := hb e.1 hm.1
    have hb' := hb e.2 (List.mem_of_mem_tail hm.2)
    omega

/-- Changing the sign only interchanges the two orientations of a straight neighborhood. -/
theorem StraightThrough.neg {r : Route} {p d : Point} (h : StraightThrough r p d) :
    StraightThrough r p (-d) := by
  simpa only [StraightThrough, sub_eq_add_neg, neg_neg, or_comm] using h

/-- A straight neighborhood remains consecutive inside any larger list containing the path. -/
theorem StraightThrough.infix {r s : Route} {p d : Point} (h : StraightThrough r p d)
    (hrs : r <:+: s) : StraightThrough s p d := by
  rcases h with h | h
  · exact Or.inl (h.trans hrs)
  · exact Or.inr (h.trans hrs)

private theorem infix_triple_neighbors {r : Route} (hn : r.Nodup) {a p b : Point}
    (ht : [a, p, b] <:+: r) {k : ℕ} (hk : k < r.length) (heq : r[k] = p) :
    0 < k ∧ k + 1 < r.length ∧ r.getD (k - 1) p = a ∧ r.getD (k + 1) p = b := by
  obtain ⟨start, hlen, hitems⟩ := List.infix_iff_getElem?.1 ht
  have hm : r[start + 1]? = some p := by
    have h := hitems 1 (by simp)
    change r[1 + start]? = some p at h
    simpa only [Nat.add_comm] using h
  have hlt : start + 1 < r.length := by
    simp only [List.length_cons, List.length_nil] at hlen
    omega
  have hmid : r[start + 1]'hlt = p := by
    rwa [List.getElem?_eq_getElem hlt, Option.some.injEq] at hm
  have hindex : k = start + 1 := hn.getElem_inj_iff.1 (heq.trans hmid.symm)
  subst k
  simp only [List.length_cons, List.length_nil] at hlen
  refine ⟨by omega, by omega, ?_, ?_⟩
  · have ha : r[start]? = some a := by
      have h := hitems 0 (by simp)
      change r[0 + start]? = some a at h
      simpa only [Nat.zero_add] using h
    simp only [Nat.add_sub_cancel, List.getD_eq_getElem?_getD, ha, Option.getD_some]
  · have hb : r[start + 1 + 1]? = some b := by
      have h := hitems 2 (by simp)
      change r[2 + start]? = some b at h
      simpa only [show start + 1 + 1 = 2 + start by omega] using h
    simp only [List.getD_eq_getElem?_getD, hb, Option.getD_some]

/-- The consecutive neighborhood gives the exact predecessor/successor lookups used by finite
wire compilers, at every valid occurrence index of the middle point. -/
theorem StraightThrough.getD_neighbors {r : Route} {p d : Point} (ht : StraightThrough r p d)
    (hn : r.Nodup) {k : ℕ} (hk : k < r.length) (heq : r[k] = p) :
    0 < k ∧ k + 1 < r.length ∧
      ((r.getD (k - 1) p = p - d ∧ r.getD (k + 1) p = p + d) ∨
        (r.getD (k - 1) p = p + d ∧ r.getD (k + 1) p = p - d)) := by
  rcases ht with ht | ht
  · obtain ⟨h0, hlast, ha, hb⟩ := infix_triple_neighbors hn ht hk heq
    exact ⟨h0, hlast, Or.inl ⟨ha, hb⟩⟩
  · obtain ⟨h0, hlast, ha, hb⟩ := infix_triple_neighbors hn ht hk heq
    exact ⟨h0, hlast, Or.inr ⟨ha, hb⟩⟩

private theorem range_triple {i k : ℕ} (hi : i + 2 ≤ k) :
    [i, i + 1, i + 2] <:+: List.range (k + 1) := by
  apply List.infix_iff_getElem?.2
  refine ⟨i, ?_, ?_⟩
  · simp only [List.length_cons, List.length_nil, List.length_range]
    omega
  · intro j hj
    have hj' : j < 3 := hj
    interval_cases j <;> rw [List.getElem?_range (by omega)] <;> simp [Nat.add_comm]

/-- Three successive steps of a finite walk form a consecutive sublist. -/
theorem walk_triple (a d : Point) {i k : ℕ} (hi : i + 2 ≤ k) :
    [a + i • d, a + (i + 1) • d, a + (i + 2) • d] <:+: walk a d k := by
  rw [walk_eq_map_range]
  simpa only [List.map_cons, List.map_nil] using (range_triple hi).map (fun j => a + j • d)

/-- Every non-endpoint index of a walk has its two immediately neighboring steps. -/
theorem walk_straight (a d : Point) {i k : ℕ} (hi : 0 < i) (hik : i < k) :
    StraightThrough (walk a d k) (a + i • d) d := by
  cases i with
  | zero => omega
  | succ i =>
    have hm : a + (i + 1) • d - d = a + i • d := by rw [add_smul, one_smul]; abel
    have hp : a + (i + 1) • d + d = a + (i + 2) • d := by
      simp only [add_smul, one_smul, two_nsmul]
      abel
    apply Or.inl
    rw [hm, hp]
    exact walk_triple a d (by omega)

/-- A strict interior integer point of an axis-aligned segment has both neighboring unit
points consecutively present in that segment's subdivision. -/
theorem segmentWalk_straight {a b p : Point} (haxis : a.1 = b.1 ∨ a.2 = b.2)
    (hp : realPoint p ∈ segment a b) (hpa : p ≠ a) (hpb : p ≠ b) :
    StraightThrough (segmentWalk a b) p (direction a b) := by
  have hb := (realPoint_mem_segment_iff haxis).1 hp
  have hap : a.1 = p.1 ∨ a.2 = p.2 := by
    rcases haxis with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  have hindex : 0 < length a p ∧ length a p < length a b := by
    rcases a with ⟨ax, ay⟩
    rcases b with ⟨bx, by'⟩
    rcases p with ⟨px, py⟩
    simp only [length, ne_eq, Prod.mk.injEq] at hpa hpb ⊢
    omega
  have hdir : direction a p = direction a b := by
    unfold direction
    simp only [ne_eq, Prod.ext_iff] at hpa hpb
    split_ifs <;> first | rfl | (exfalso; omega)
  have hpoint : a + length a p • direction a b = p := by
    rw [← hdir]
    exact add_length_direction hap
  have ht := walk_straight a (direction a b) hindex.1 hindex.2
  rw [hpoint] at ht
  exact ht

/-- A horizontal segment is traversed horizontally at every strict interior grid point. -/
theorem segmentWalk_horizontal {a b p : Point} (hab : a.2 = b.2) (hp : p.2 = a.2)
    (hx : min a.1 b.1 < p.1 ∧ p.1 < max a.1 b.1) :
    StraightThrough (segmentWalk a b) p (1, 0) := by
  have hm : realPoint p ∈ segment a b := (realPoint_mem_segment_iff (Or.inr hab)).2 (by omega)
  have hpa : p ≠ a := by intro h; subst p; omega
  have hpb : p ≠ b := by intro h; subst p; omega
  have ht := segmentWalk_straight (Or.inr hab) hm hpa hpb
  have hd : direction a b = (1, 0) ∨ direction a b = -(1, 0) := by
    unfold direction
    split_ifs <;> first | exact Or.inl rfl | exact Or.inr rfl | omega
  rcases hd with hd | hd
  · simpa only [hd] using ht
  · simpa only [hd, neg_neg] using ht.neg

/-- A vertical segment is traversed vertically at every strict interior grid point. -/
theorem segmentWalk_vertical {a b p : Point} (hab : a.1 = b.1) (hp : p.1 = a.1)
    (hy : min a.2 b.2 < p.2 ∧ p.2 < max a.2 b.2) :
    StraightThrough (segmentWalk a b) p (0, 1) := by
  have hm : realPoint p ∈ segment a b := (realPoint_mem_segment_iff (Or.inl hab)).2 (by omega)
  have hpa : p ≠ a := by intro h; subst p; omega
  have hpb : p ≠ b := by intro h; subst p; omega
  have ht := segmentWalk_straight (Or.inl hab) hm hpa hpb
  have hd : direction a b = (0, 1) ∨ direction a b = -(0, 1) := by
    unfold direction
    split_ifs <;> first | exact Or.inl rfl | exact Or.inr rfl | omega
  rcases hd with hd | hd
  · simpa only [hd] using ht
  · simpa only [hd, neg_neg] using ht.neg

/-- Every original segment's complete unit walk occurs consecutively in the subdivided route. -/
theorem segmentWalk_infix_subdivide {r : Route} (hr : IsOrthogonal r) {e : Point × Point}
    (he : e ∈ r.consecutivePairs) : segmentWalk e.1 e.2 <:+: subdivide r := by
  induction r with
  | nil => simp [List.consecutivePairs] at he
  | cons a r ih =>
    cases r with
    | nil => simp [List.consecutivePairs] at he
    | cons b r =>
      have hab := (hr (a, b) (by simp [List.consecutivePairs])).1
      have htail : IsOrthogonal (b :: r) := by
        intro f hf
        exact hr f (by simpa only [List.consecutivePairs, List.tail_cons,
          List.zip_cons_cons, List.mem_cons] using Or.inr hf)
      have hpairs : (a :: b :: r).consecutivePairs = (a, b) :: (b :: r).consecutivePairs := rfl
      rw [hpairs, List.mem_cons] at he
      rcases he with rfl | he
      · rw [subdivide]
        exact List.infix_append_left
      · have ht := ih htail he
        have hj : subdivide (b :: r) <:+: subdivide (a :: b :: r) := by
          obtain ⟨initial, hwalk⟩ := List.getLast?_eq_some_iff.1 (segmentWalk_last hab)
          obtain ⟨rest, hrest⟩ := List.head?_eq_some_iff.1 (subdivide_head (b :: r))
          rw [subdivide, hwalk, hrest]
          exact ⟨initial, [], by simp⟩
        exact ht.trans hj

/-- Horizontal strict interior neighborhoods survive subdivision of an entire route. -/
theorem subdivide_horizontal {r : Route} (hr : IsOrthogonal r) {e : Point × Point}
    (he : e ∈ r.consecutivePairs) {p : Point} (hab : e.1.2 = e.2.2) (hp : p.2 = e.1.2)
    (hx : min e.1.1 e.2.1 < p.1 ∧ p.1 < max e.1.1 e.2.1) :
    StraightThrough (subdivide r) p (1, 0) :=
  (segmentWalk_horizontal hab hp hx).infix (segmentWalk_infix_subdivide hr he)

/-- Vertical strict interior neighborhoods survive subdivision of an entire route. -/
theorem subdivide_vertical {r : Route} (hr : IsOrthogonal r) {e : Point × Point}
    (he : e ∈ r.consecutivePairs) {p : Point} (hab : e.1.1 = e.2.1) (hp : p.1 = e.1.1)
    (hy : min e.1.2 e.2.2 < p.2 ∧ p.2 < max e.1.2 e.2.2) :
    StraightThrough (subdivide r) p (0, 1) :=
  (segmentWalk_vertical hab hp hy).infix (segmentWalk_infix_subdivide hr he)

end Cslib.Orthogonal
