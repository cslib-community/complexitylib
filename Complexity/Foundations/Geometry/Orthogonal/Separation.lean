/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Foundations.Geometry.Orthogonal
import Mathlib.Tactic.Linarith

/-!
# Finite certificates for contacts of polygonal routes

Two axis-aligned closed segments have rectangular bounding boxes whose intersection is empty,
a singleton, or an overlapping segment. The Boolean checker accepts the first two cases when
the singleton is an allowed contact point. Its soundness refers to the entire real segments.
In fact, the sufficient bounding-box criterion is sound even for diagonal segments.

The route checker includes a degenerate segment for every listed point, so its soundness also
covers empty and singleton routes. In particular, checking against a singleton route certifies
that an incidence route avoids a nonincident vertex.

## Main definitions

* `Cslib.Orthogonal.segmentContactCheck`: check permitted contacts between two closed segments.
* `Cslib.Orthogonal.routeContactCheck`: check permitted contacts between continuous route supports.

## Main results

* `Cslib.Orthogonal.segmentContactCheck_sound`: every real intersection is an allowed grid point.
* `Cslib.Orthogonal.routeContactCheck_sound`: the corresponding certificate for route supports.
* `Cslib.Orthogonal.disjoint_support_of_routeContactCheck`: an empty contact list proves
  disjointness.
* `Cslib.Orthogonal.not_mem_support_of_routeContactCheck`: a singleton check excludes a vertex.

## References

This finite bounding-box certificate is an elementary geometric construction.
-/

@[expose] public section

namespace Cslib.Orthogonal

/-- A finite sufficient test that two segments meet only at listed grid points. It accepts
disjoint bounding boxes or a singleton intersection belonging to `allowed`. -/
def segmentContactCheck (allowed : List Point) (a b c d : Point) : Bool :=
  let lx := max (min a.1 b.1) (min c.1 d.1)
  let ux := min (max a.1 b.1) (max c.1 d.1)
  let ly := max (min a.2 b.2) (min c.2 d.2)
  let uy := min (max a.2 b.2) (max c.2 d.2)
  decide (ux < lx ∨ uy < ly ∨ lx = ux ∧ ly = uy ∧ (lx, ly) ∈ allowed)

private theorem mem_segment_int_bounds {a b : Point} {p : ℝ × ℝ} (hp : p ∈ segment a b) :
    ((min a.1 b.1 : ℤ) : ℝ) ≤ p.1 ∧ p.1 ≤ ((max a.1 b.1 : ℤ) : ℝ) ∧
    ((min a.2 b.2 : ℤ) : ℝ) ≤ p.2 ∧ p.2 ≤ ((max a.2 b.2 : ℤ) : ℝ) := by
  have h := mem_segment_bounds hp
  change (min (a.1 : ℝ) (b.1 : ℝ) ≤ p.1 ∧ p.1 ≤ max (a.1 : ℝ) (b.1 : ℝ)) ∧
    (min (a.2 : ℝ) (b.2 : ℝ) ≤ p.2 ∧ p.2 ≤ max (a.2 : ℝ) (b.2 : ℝ)) at h
  simpa only [Int.cast_min, Int.cast_max] using
    And.intro h.1.1 (And.intro h.1.2 (And.intro h.2.1 h.2.2))

/-- The finite checker controls every real intersection, not only lattice intersections. -/
theorem segmentContactCheck_sound {allowed : List Point} {a b c d : Point}
    (h : segmentContactCheck allowed a b c d = true) {p : ℝ × ℝ}
    (hab : p ∈ segment a b) (hcd : p ∈ segment c d) :
    ∃ q ∈ allowed, p = realPoint q := by
  have ha := mem_segment_int_bounds hab
  have hc := mem_segment_int_bounds hcd
  let lx := max (min a.1 b.1) (min c.1 d.1)
  let ux := min (max a.1 b.1) (max c.1 d.1)
  let ly := max (min a.2 b.2) (min c.2 d.2)
  let uy := min (max a.2 b.2) (max c.2 d.2)
  have hx : (lx : ℝ) ≤ p.1 ∧ p.1 ≤ (ux : ℝ) := by
    constructor
    · change ((max (min a.1 b.1) (min c.1 d.1) : ℤ) : ℝ) ≤ p.1
      rw [Int.cast_max, max_le_iff]
      exact ⟨ha.1, hc.1⟩
    · change p.1 ≤ ((min (max a.1 b.1) (max c.1 d.1) : ℤ) : ℝ)
      rw [Int.cast_min, le_min_iff]
      exact ⟨ha.2.1, hc.2.1⟩
  have hy : (ly : ℝ) ≤ p.2 ∧ p.2 ≤ (uy : ℝ) := by
    constructor
    · change ((max (min a.2 b.2) (min c.2 d.2) : ℤ) : ℝ) ≤ p.2
      rw [Int.cast_max, max_le_iff]
      exact ⟨ha.2.2.1, hc.2.2.1⟩
    · change p.2 ≤ ((min (max a.2 b.2) (max c.2 d.2) : ℤ) : ℝ)
      rw [Int.cast_min, le_min_iff]
      exact ⟨ha.2.2.2, hc.2.2.2⟩
  change decide (ux < lx ∨ uy < ly ∨ lx = ux ∧ ly = uy ∧ (lx, ly) ∈ allowed) = true at h
  rw [decide_eq_true_eq] at h
  rcases h with h | h | ⟨hxy, hyy, hmem⟩
  · have : (ux : ℝ) < (lx : ℝ) := by exact_mod_cast h
    exact False.elim (by linarith [hx.1, hx.2])
  · have : (uy : ℝ) < (ly : ℝ) := by exact_mod_cast h
    exact False.elim (by linarith [hy.1, hy.2])
  · refine ⟨(lx, ly), hmem, Prod.ext ?_ ?_⟩
    · change p.1 = (lx : ℝ)
      rw [← hxy] at hx
      exact le_antisymm hx.2 hx.1
    · change p.2 = (ly : ℝ)
      rw [← hyy] at hy
      exact le_antisymm hy.2 hy.1

/-- Segment pieces for a route, including degenerate pieces for isolated listed points. -/
def segmentPieces (r : Route) : List (Point × Point) :=
  r.map (fun p => (p, p)) ++ r.consecutivePairs

/-- Continuous route support is exactly the union of its finite segment pieces. -/
theorem mem_support_iff_segmentPieces {r : Route} {p : ℝ × ℝ} :
    p ∈ support r ↔ ∃ e ∈ segmentPieces r, p ∈ segment e.1 e.2 := by
  constructor
  · rintro (⟨a, ha, rfl⟩ | ⟨e, he, hp⟩)
    · exact ⟨(a, a), List.mem_append_left _ (List.mem_map_of_mem ha),
        _root_.left_mem_segment ℝ (realPoint a) (realPoint a)⟩
    · exact ⟨e, List.mem_append_right _ he, hp⟩
  · rintro ⟨e, he, hp⟩
    rcases List.mem_append.mp he with he | he
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
      have hpa : p = realPoint a := by simpa only [segment, _root_.segment_same,
        Set.mem_singleton_iff] using hp
      exact Or.inl ⟨a, ha, hpa⟩
    · exact Or.inr ⟨e, he, hp⟩

/-- Check all finite segment-piece pairs for permitted contacts. -/
def routeContactCheck (allowed : List Point) (r s : Route) : Bool :=
  (segmentPieces r).all fun e => (segmentPieces s).all fun f =>
    segmentContactCheck allowed e.1 e.2 f.1 f.2

/-- Every real intersection of the route supports is one of the allowed grid points. -/
theorem routeContactCheck_sound {allowed : List Point} {r s : Route}
    (h : routeContactCheck allowed r s = true) {p : ℝ × ℝ}
    (hr : p ∈ support r) (hs : p ∈ support s) : ∃ q ∈ allowed, p = realPoint q := by
  obtain ⟨e, he, hpe⟩ := mem_support_iff_segmentPieces.mp hr
  obtain ⟨f, hf, hpf⟩ := mem_support_iff_segmentPieces.mp hs
  exact segmentContactCheck_sound
    (List.all_eq_true.mp (List.all_eq_true.mp h e he) f hf) hpe hpf

/-- An empty permitted-contact list certifies disjoint continuous supports. -/
theorem disjoint_support_of_routeContactCheck {r s : Route}
    (h : routeContactCheck [] r s = true) : Disjoint (support r) (support s) := by
  rw [Set.disjoint_left]
  intro p hr hs
  obtain ⟨q, hq, _⟩ := routeContactCheck_sound h hr hs
  exact List.not_mem_nil hq

/-- Testing against a singleton route certifies that a route avoids a specified vertex. -/
theorem not_mem_support_of_routeContactCheck {r : Route} {q : Point}
    (h : routeContactCheck [] r [q] = true) : realPoint q ∉ support r := by
  intro hr
  obtain ⟨p, hp, _⟩ := routeContactCheck_sound h hr (Or.inl ⟨q, by simp, rfl⟩)
  exact List.not_mem_nil hp

end Cslib.Orthogonal
