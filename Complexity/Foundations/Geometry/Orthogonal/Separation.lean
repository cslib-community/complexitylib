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

* `Cslib.Orthogonal.consecutiveContact`: permitted shared bend between two segments.
* `Cslib.Orthogonal.segmentContactCheck`: check permitted contacts between two closed segments.
* `Cslib.Orthogonal.routeBoxDisjoint`: check whether two route bounding boxes are disjoint.
* `Cslib.Orthogonal.routeContactCheck`: check permitted contacts between continuous route supports.

## Main results

* `Cslib.Orthogonal.segmentContactCheck_sound`: every real intersection is an allowed grid point.
* `Cslib.Orthogonal.disjoint_support_of_routeBoxDisjoint`: disjoint route boxes have disjoint
  continuous supports.
* `Cslib.Orthogonal.routeContactCheck_sound`: the corresponding certificate for route supports.
* `Cslib.Orthogonal.disjoint_support_of_routeContactCheck`: an empty contact list proves
  disjointness.
* `Cslib.Orthogonal.not_mem_support_of_routeContactCheck`: a singleton check excludes a vertex.

## References

This finite bounding-box certificate is an elementary geometric construction.
-/

@[expose] public section

namespace Cslib.Orthogonal

/-- A pair of different segments may meet only at a consecutive shared bend. -/
def consecutiveContact (a b : Point × Point) : List Point :=
  if a.2 = b.1 then [a.2] else if b.2 = a.1 then [a.1] else []

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

private theorem mem_of_mem_segmentPieces {r : Route} {e : Point × Point}
    (he : e ∈ segmentPieces r) : e.1 ∈ r ∧ e.2 ∈ r := by
  rcases List.mem_append.mp he with he | he
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
    exact ⟨ha, ha⟩
  · have h := List.of_mem_zip he
    exact ⟨h.1, List.mem_of_mem_tail h.2⟩

/-- Minimum of a coordinate projection along a nonempty route `p :: r`. -/
def coordMin (f : Point → ℤ) (p : Point) : Route → ℤ
  | [] => f p
  | q :: r => min (f p) (coordMin f q r)

/-- Maximum of a coordinate projection along a nonempty route `p :: r`. -/
def coordMax (f : Point → ℤ) (p : Point) : Route → ℤ
  | [] => f p
  | q :: r => max (f p) (coordMax f q r)

private theorem coordMin_le (f : Point → ℤ) :
    ∀ {p : Point} {r : Route} {a : Point}, a ∈ p :: r → coordMin f p r ≤ f a
  | _, [], _, ha => by
    obtain rfl := List.mem_singleton.mp ha
    exact le_rfl
  | _, _ :: _, _, ha => by
    rcases List.mem_cons.mp ha with rfl | ha
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (coordMin_le f ha)

private theorem le_coordMax (f : Point → ℤ) :
    ∀ {p : Point} {r : Route} {a : Point}, a ∈ p :: r → f a ≤ coordMax f p r
  | _, [], _, ha => by
    obtain rfl := List.mem_singleton.mp ha
    exact le_rfl
  | _, _ :: _, _, ha => by
    rcases List.mem_cons.mp ha with rfl | ha
    · exact le_max_left _ _
    · exact (le_coordMax f ha).trans (le_max_right _ _)

private theorem mem_support_int_bounds {q : Point} {r : Route} {p : ℝ × ℝ}
    (hp : p ∈ support (q :: r)) :
    ((coordMin Prod.fst q r : ℤ) : ℝ) ≤ p.1 ∧ p.1 ≤ ((coordMax Prod.fst q r : ℤ) : ℝ) ∧
    ((coordMin Prod.snd q r : ℤ) : ℝ) ≤ p.2 ∧ p.2 ≤ ((coordMax Prod.snd q r : ℤ) : ℝ) := by
  obtain ⟨e, he, hpe⟩ := mem_support_iff_segmentPieces.mp hp
  obtain ⟨he1, he2⟩ := mem_of_mem_segmentPieces he
  have hb := mem_segment_int_bounds hpe
  have hxmin : ((coordMin Prod.fst q r : ℤ) : ℝ) ≤ ((min e.1.1 e.2.1 : ℤ) : ℝ) := by
    exact_mod_cast le_min (coordMin_le Prod.fst he1) (coordMin_le Prod.fst he2)
  have hxmax : ((max e.1.1 e.2.1 : ℤ) : ℝ) ≤ ((coordMax Prod.fst q r : ℤ) : ℝ) := by
    exact_mod_cast max_le (le_coordMax Prod.fst he1) (le_coordMax Prod.fst he2)
  have hymin : ((coordMin Prod.snd q r : ℤ) : ℝ) ≤ ((min e.1.2 e.2.2 : ℤ) : ℝ) := by
    exact_mod_cast le_min (coordMin_le Prod.snd he1) (coordMin_le Prod.snd he2)
  have hymax : ((max e.1.2 e.2.2 : ℤ) : ℝ) ≤ ((coordMax Prod.snd q r : ℤ) : ℝ) := by
    exact_mod_cast max_le (le_coordMax Prod.snd he1) (le_coordMax Prod.snd he2)
  exact ⟨hxmin.trans hb.1, hb.2.1.trans hxmax, hymin.trans hb.2.2.1, hb.2.2.2.trans hymax⟩

/-- Check whether the integer coordinate bounding boxes of two routes are disjoint.
Empty routes have empty support, so their bounding boxes are treated as disjoint. -/
def routeBoxDisjoint : Route → Route → Bool
  | [], _ => true
  | _, [] => true
  | a :: r, b :: s =>
    decide (coordMax Prod.fst a r < coordMin Prod.fst b s ∨
      coordMax Prod.fst b s < coordMin Prod.fst a r ∨
      coordMax Prod.snd a r < coordMin Prod.snd b s ∨
      coordMax Prod.snd b s < coordMin Prod.snd a r)

/-- Disjoint integer route bounding boxes certify disjoint continuous supports. -/
theorem disjoint_support_of_routeBoxDisjoint {r s : Route}
    (h : routeBoxDisjoint r s = true) : Disjoint (support r) (support s) := by
  rw [Set.disjoint_left]
  intro p hr hs
  cases r with
  | nil =>
    obtain ⟨e, he, _⟩ := mem_support_iff_segmentPieces.mp hr
    exact List.not_mem_nil he
  | cons a r =>
    cases s with
    | nil =>
      obtain ⟨e, he, _⟩ := mem_support_iff_segmentPieces.mp hs
      exact List.not_mem_nil he
    | cons b s =>
      have hrb := mem_support_int_bounds hr
      have hsb := mem_support_int_bounds hs
      simp only [routeBoxDisjoint, decide_eq_true_eq] at h
      rcases h with h | h | h | h
      · have : ((coordMax Prod.fst a r : ℤ) : ℝ) < ((coordMin Prod.fst b s : ℤ) : ℝ) := by
          exact_mod_cast h
        linarith [hrb.2.1, hsb.1]
      · have : ((coordMax Prod.fst b s : ℤ) : ℝ) < ((coordMin Prod.fst a r : ℤ) : ℝ) := by
          exact_mod_cast h
        linarith [hrb.1, hsb.2.1]
      · have : ((coordMax Prod.snd a r : ℤ) : ℝ) < ((coordMin Prod.snd b s : ℤ) : ℝ) := by
          exact_mod_cast h
        linarith [hrb.2.2.2, hsb.2.2.1]
      · have : ((coordMax Prod.snd b s : ℤ) : ℝ) < ((coordMin Prod.snd a r : ℤ) : ℝ) := by
          exact_mod_cast h
        linarith [hrb.2.2.1, hsb.2.2.2]

/-- Check whether two routes have disjoint bounding boxes or all finite segment-piece pairs
have only permitted contacts. -/
def routeContactCheck (allowed : List Point) (r s : Route) : Bool :=
  routeBoxDisjoint r s ||
    ((segmentPieces r).all fun e => (segmentPieces s).all fun f =>
      segmentContactCheck allowed e.1 e.2 f.1 f.2)

/-- Every real intersection of the route supports is one of the allowed grid points. -/
theorem routeContactCheck_sound {allowed : List Point} {r s : Route}
    (h : routeContactCheck allowed r s = true) {p : ℝ × ℝ}
    (hr : p ∈ support r) (hs : p ∈ support s) : ∃ q ∈ allowed, p = realPoint q := by
  rw [routeContactCheck, Bool.or_eq_true] at h
  rcases h with hbox | hpieces
  · exact False.elim (Set.disjoint_left.mp (disjoint_support_of_routeBoxDisjoint hbox) hr hs)
  · obtain ⟨e, he, hpe⟩ := mem_support_iff_segmentPieces.mp hr
    obtain ⟨f, hf, hpf⟩ := mem_support_iff_segmentPieces.mp hs
    exact segmentContactCheck_sound
      (List.all_eq_true.mp (List.all_eq_true.mp hpieces e he) f hf) hpe hpf

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
