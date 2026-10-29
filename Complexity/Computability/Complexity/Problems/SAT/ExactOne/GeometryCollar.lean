/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SAT.ExactOne.GeometryCollarData
public import Complexity.Foundations.Geometry.Orthogonal.Trim
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Linarith

/-!
# Certified annular routing for ordered clause ports

All 24 ordered injections into the four side midpoints have three mutually disjoint
simple orthogonal connector routes. Every connector meets the closed inner template square
only at its prescribed endpoint. The certificates control entire real supports.

## Main definitions

* `routeBoxContactCheck`: a finite route/closed-square contact certificate.
* `CollarCheck`: endpoint, simplicity, bounds, disjointness, and inner-square checks.

## Main results

* `collar_check`: complete finite certificates for every valid ordered assignment.
* `collar_core_contact`, `collar_disjoint`: full continuous isolation consequences.

## References

The finite annular routing certificates and proofs are original.
-/

@[expose] public section

namespace Cslib.Complexity.SAT.ExactOne

open Orthogonal

/-- A bounding-box contact test between every route segment and a closed square. -/
def routeBoxContactCheck (allowed : List Point) (r : Route) (c : Point) (radius : ℕ) : Bool :=
  (segmentPieces r).all fun e => segmentContactCheck allowed e.1 e.2
    (c.1 - radius, c.2 - radius) (c.1 + radius, c.2 + radius)

private theorem segment_box_contact_sound {allowed : List Point} {a b c : Point}
    {radius : ℕ}
    (h : segmentContactCheck allowed a b
      (c.1 - radius, c.2 - radius) (c.1 + radius, c.2 + radius) = true)
    {p : ℝ × ℝ} (hp : p ∈ segment a b) (hc : inPointBox c radius p) :
    ∃ q ∈ allowed, p = realPoint q := by
  have hab := mem_segment_bounds hp
  change (min (a.1 : ℝ) (b.1 : ℝ) ≤ p.1 ∧ p.1 ≤ max (a.1 : ℝ) (b.1 : ℝ)) ∧
    (min (a.2 : ℝ) (b.2 : ℝ) ≤ p.2 ∧ p.2 ≤ max (a.2 : ℝ) (b.2 : ℝ)) at hab
  let lx := max (min a.1 b.1) (c.1 - radius)
  let ux := min (max a.1 b.1) (c.1 + radius)
  let ly := max (min a.2 b.2) (c.2 - radius)
  let uy := min (max a.2 b.2) (c.2 + radius)
  have hx : (lx : ℝ) ≤ p.1 ∧ p.1 ≤ (ux : ℝ) := by
    dsimp only [lx, ux]
    simp only [Int.cast_max, Int.cast_min, Int.cast_sub, Int.cast_add, Int.cast_natCast]
    exact ⟨max_le hab.1.1 hc.1, le_min hab.1.2 hc.2.1⟩
  have hy : (ly : ℝ) ≤ p.2 ∧ p.2 ≤ (uy : ℝ) := by
    dsimp only [ly, uy]
    simp only [Int.cast_max, Int.cast_min, Int.cast_sub, Int.cast_add, Int.cast_natCast]
    exact ⟨max_le hab.2.1 hc.2.2.1, le_min hab.2.2 hc.2.2.2⟩
  have hlo₁ : c.1 - (radius : ℤ) ≤ c.1 + radius := by omega
  have hlo₂ : c.2 - (radius : ℤ) ≤ c.2 + radius := by omega
  simp only [segmentContactCheck, min_eq_left hlo₁, max_eq_right hlo₁,
    min_eq_left hlo₂, max_eq_right hlo₂] at h
  change decide (ux < lx ∨ uy < ly ∨ lx = ux ∧ ly = uy ∧ (lx, ly) ∈ allowed) = true at h
  rw [decide_eq_true_eq] at h
  rcases h with h | h | ⟨hx', hy', hm⟩
  · have h' : (ux : ℝ) < lx := by exact_mod_cast h
    exact False.elim (by linarith [hx.1, hx.2])
  · have h' : (uy : ℝ) < ly := by exact_mod_cast h
    exact False.elim (by linarith [hy.1, hy.2])
  · refine ⟨(lx, ly), hm, Prod.ext ?_ ?_⟩
    · change p.1 = (lx : ℝ)
      rw [← hx'] at hx
      exact le_antisymm hx.2 hx.1
    · change p.2 = (ly : ℝ)
      rw [← hy'] at hy
      exact le_antisymm hy.2 hy.1

/-- The finite square checker controls all real points of the route. -/
theorem routeBoxContactCheck_sound {allowed : List Point} {r : Route} {c : Point}
    {radius : ℕ} (h : routeBoxContactCheck allowed r c radius = true)
    {p : ℝ × ℝ} (hp : p ∈ support r) (hc : inPointBox c radius p) :
    ∃ q ∈ allowed, p = realPoint q := by
  obtain ⟨e, he, hp⟩ := mem_support_iff_segmentPieces.mp hp
  exact segment_box_contact_sound (List.all_eq_true.mp h e he) hp hc

/-- Complete finite conditions on the annular connector family. -/
def CollarCheck (s : PortAssignment) : Prop :=
  (collarRoutes s).length = 3 ∧
  ∀ i : Fin 3,
    let r := (collarRoutes s).getD i []
    r.head? = some (collarOuterPort (s.side i)) ∧
      r.getLast? = some (collarInnerPort (collarReflected s) i) ∧
      IsOrthogonal r ∧ LocalGeometry.SimpleCheck r ∧
      (∀ p ∈ r, 0 ≤ p.1 ∧ p.1 ≤ 540000 ∧ 0 ≤ p.2 ∧ p.2 ≤ 540000) ∧
      (∀ p ∈ r.tail, 0 < p.1 ∧ p.1 < 540000 ∧ 0 < p.2 ∧ p.2 < 540000) ∧
      routeBoxContactCheck [collarInnerPort (collarReflected s) i] r
        (270000, 270000) 90000 = true ∧
      ∀ j : Fin 3, i ≠ j →
        routeContactCheck [] r ((collarRoutes s).getD j []) = true

instance (s : PortAssignment) : Decidable (CollarCheck s) := by
  unfold CollarCheck
  refine @instDecidableAnd _ _ ?_ ?_
  all_goals infer_instance

/-- Every ordered injection has its complete annular routing certificate. -/
theorem collar_check : ∀ s : PortAssignment, s.Distinct → CollarCheck s := by
  decide +kernel

/-- Every collar route is continuously simple. -/
theorem collar_isSimple {s : PortAssignment} (hs : s.Distinct) (i : Fin 3) :
    IsSimple ((collarRoutes s).getD i []) :=
  LocalGeometry.isSimple_of_check ((collar_check s hs).2 i).2.2.2.1

/-- Distinct collar routes have disjoint full real supports. -/
theorem collar_disjoint {s : PortAssignment} (hs : s.Distinct) {i j : Fin 3} (hij : i ≠ j) :
    Disjoint (support ((collarRoutes s).getD i [])) (support ((collarRoutes s).getD j [])) :=
  disjoint_support_of_routeContactCheck (((collar_check s hs).2 i).2.2.2.2.2.2.2 j hij)

/-- A collar route meets the closed inner template square only at its prescribed endpoint. -/
theorem collar_core_contact {s : PortAssignment} (hs : s.Distinct) {i : Fin 3}
    {p : ℝ × ℝ} (hp : p ∈ support ((collarRoutes s).getD i []))
    (hc : inPointBox (270000, 270000) 90000 p) :
    p = realPoint (collarInnerPort (collarReflected s) i) := by
  obtain ⟨q, hq, hpq⟩ := routeBoxContactCheck_sound
    (((collar_check s hs).2 i).2.2.2.2.2.2.1) hp hc
  exact List.mem_singleton.mp hq ▸ hpq

/-- Each connector has at most seven segments and wire length at most 600000. -/
theorem collar_route_costs : ∀ s : PortAssignment, s.Distinct → ∀ i : Fin 3,
    ((collarRoutes s).getD i []).consecutivePairs.length ≤ 7 ∧
      wireLength ((collarRoutes s).getD i []) ≤ 600000 := by
  decide +kernel

/-- The entire three-connector family has wire length at most 1780000. -/
theorem collar_total_wireLength : ∀ s : PortAssignment, s.Distinct →
    ((collarRoutes s).map wireLength).sum ≤ 1780000 := by
  decide +kernel

end Cslib.Complexity.SAT.ExactOne
