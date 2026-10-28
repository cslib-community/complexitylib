/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SAT.ExactOne.GeometryCollar
public import Complexity.Foundations.Geometry.Orthogonal.Join
public import Complexity.Foundations.Geometry.Orthogonal.Mirror
public import Complexity.Foundations.Geometry.Orthogonal.Reverse
public import Complexity.Foundations.Geometry.Orthogonal.Macrocell
import Mathlib.Tactic.NormNum

/-!
# Gluing clause templates to ordered-port collars

Templates of side 180000 are translated, and optionally reflected, into the central square
of the side-540000 collar. A clause-to-inner-boundary prefix then extends along its reversed
collar route. The continuous certificates compose through their unique common endpoint.

## Main definitions

* `collarPoint`, `collarRoute`: the common affine placement of an inner template.
* `collarPrefixRoute`: a placed local prefix followed by its inner-to-outer collar.
* `collaredPrefixGeometry`: the actual finite placed template and its extended incidences.

## Main results

* `isSimple_collarPrefixRoute`, `isOrthogonal_collarPrefixRoute`.
* `support_collarPrefixRoute`, `wireLength_collarPrefixRoute`.

## References

These finite local-placement and gluing constructions are original.
-/

@[expose] public section

namespace Cslib.Complexity.SAT.ExactOne

open Orthogonal

/-- Translation part of the reflected or unreflected inner-template placement. -/
def collarOffset (reflected : Bool) : Point :=
  (if reflected then 360000 else 180000, 180000)

/-- Place a point of the side-180000 template inside the central collar square. -/
def collarPoint (reflected : Bool) (p : Point) : Point :=
  (if reflected then mirrorPoint p else p) + collarOffset reflected

/-- The corresponding placement in the real plane. -/
def collarReal (reflected : Bool) (p : ℝ × ℝ) : ℝ × ℝ :=
  (if reflected then mirrorReal p else p) + realPoint (collarOffset reflected)

/-- Place an entire local route. -/
def collarRoute (reflected : Bool) (r : Route) : Route :=
  translate (collarOffset reflected) (if reflected then mirrorRoute r else r)

/-- Route placement is pointwise placement of the finite list. -/
theorem collarRoute_eq_map (reflected : Bool) (r : Route) :
    collarRoute reflected r = r.map (collarPoint reflected) := by
  cases reflected <;> simp [collarRoute, collarPoint, translate, mirrorRoute,
    List.map_map, Function.comp_def]

/-- Placement commutes with inclusion of the integer lattice. -/
theorem realPoint_collarPoint (reflected : Bool) (p : Point) :
    realPoint (collarPoint reflected p) = collarReal reflected (realPoint p) := by
  cases reflected <;>
    simp [collarPoint, collarReal, realPoint_add, realPoint_mirrorPoint]

/-- The common affine placement does not identify real points. -/
theorem collarReal_injective (reflected : Bool) : Function.Injective (collarReal reflected) := by
  intro p q h
  cases reflected <;> simpa [collarReal, mirrorReal, Prod.ext_iff] using h

/-- The common affine placement does not identify integer vertices. -/
theorem collarPoint_injective (reflected : Bool) : Function.Injective (collarPoint reflected) := by
  intro p q h
  apply realPoint_injective
  apply collarReal_injective reflected
  simpa only [← realPoint_collarPoint] using congrArg realPoint h

/-- Placement maps the full continuous support. -/
theorem support_collarRoute (reflected : Bool) (r : Route) :
    support (collarRoute reflected r) = collarReal reflected '' support r := by
  unfold collarRoute
  rw [support_translate]
  cases reflected
  · rfl
  · change (fun p => p + realPoint (collarOffset true)) '' support (mirrorRoute r) = _
    rw [support_mirrorRoute, Set.image_image]
    rfl

/-- Membership in a placed support is exactly placed membership. -/
theorem mem_support_collarRoute_iff (reflected : Bool) (r : Route) (p : ℝ × ℝ) :
    collarReal reflected p ∈ support (collarRoute reflected r) ↔ p ∈ support r := by
  rw [support_collarRoute]
  exact (collarReal_injective reflected).mem_set_image

/-- Placement preserves proper orthogonality. -/
theorem isOrthogonal_collarRoute (reflected : Bool) {r : Route} (hr : IsOrthogonal r) :
    IsOrthogonal (collarRoute reflected r) := by
  unfold collarRoute
  rw [isOrthogonal_translate_iff]
  cases reflected
  · exact hr
  · exact (isOrthogonal_mirrorRoute_iff r).2 hr

/-- Placement preserves continuous simplicity. -/
theorem isSimple_collarRoute (reflected : Bool) {r : Route} (hr : IsSimple r) :
    IsSimple (collarRoute reflected r) := by
  unfold collarRoute
  rw [isSimple_translate_iff]
  cases reflected
  · exact hr
  · exact (isSimple_mirrorRoute_iff r).2 hr

/-- Placement preserves total Manhattan wire length. -/
theorem wireLength_collarRoute (reflected : Bool) (r : Route) :
    wireLength (collarRoute reflected r) = wireLength r := by
  unfold collarRoute
  rw [wireLength_translate]
  cases reflected
  · rfl
  · exact wireLength_mirrorRoute r

/-- Placement preserves the listed segment count. -/
theorem consecutivePairs_length_collarRoute (reflected : Bool) (r : Route) :
    (collarRoute reflected r).consecutivePairs.length = r.consecutivePairs.length := by
  simp only [collarRoute_eq_map, List.consecutivePairs, List.length_zip, List.length_tail,
    List.length_map]

/-- The fixed north/west/east ports of an unplaced inner template. -/
def innerTemplatePort (i : Fin 3) : Point :=
  if i = 0 then (90000, 0) else if i = 1 then (0, 90000) else (180000, 90000)

/-- Placement identifies the inner template ports with the collar's inner endpoints. -/
theorem collarPoint_innerTemplatePort : ∀ reflected i,
    collarPoint reflected (innerTemplatePort i) = collarInnerPort reflected i := by
  decide +kernel

/-- Pointwise box bounds extend to the full real polygonal support. -/
theorem support_inPointBox_of_points {r : Route} {c : Point} {radius : ℕ}
    (hr : ∀ q ∈ r, inPointBox c radius (realPoint q)) {p : ℝ × ℝ}
    (hp : p ∈ support r) : inPointBox c radius p := by
  rcases hp with ⟨q, hq, rfl⟩ | ⟨e, he, hp⟩
  · exact hr q hq
  · have hm := List.of_mem_zip he
    have ha := hr e.1 hm.1
    have hb := hr e.2 (List.mem_of_mem_tail hm.2)
    have hc := mem_segment_bounds hp
    change (min (e.1.1 : ℝ) (e.2.1 : ℝ) ≤ p.1 ∧ p.1 ≤ max (e.1.1 : ℝ) (e.2.1 : ℝ)) ∧
      (min (e.1.2 : ℝ) (e.2.2 : ℝ) ≤ p.2 ∧ p.2 ≤ max (e.1.2 : ℝ) (e.2.2 : ℝ)) at hc
    exact ⟨(le_min ha.1 hb.1).trans hc.1.1, hc.1.2.trans (max_le ha.2.1 hb.2.1),
      (le_min ha.2.2.1 hb.2.2.1).trans hc.2.1,
      hc.2.2.trans (max_le ha.2.2.2 hb.2.2.2)⟩

/-- Placed points of the original template lie in the collar's closed inner square. -/
theorem collarPoint_in_innerBox (reflected : Bool) {q : Point}
    (hq : 0 ≤ q.1 ∧ q.1 ≤ 180000 ∧ 0 ≤ q.2 ∧ q.2 ≤ 180000) :
    inPointBox (270000, 270000) 90000 (realPoint (collarPoint reflected q)) := by
  have hi : 180000 ≤ (collarPoint reflected q).1 ∧
      (collarPoint reflected q).1 ≤ 360000 ∧
      180000 ≤ (collarPoint reflected q).2 ∧ (collarPoint reflected q).2 ≤ 360000 := by
    cases reflected <;> dsimp [collarPoint, collarOffset, mirrorPoint] <;> omega
  norm_num [inPointBox, realPoint]
  exact_mod_cast hi

/-- A placed local route stays inside the collar's closed inner square. -/
theorem collarRoute_in_innerBox (reflected : Bool) {r : Route}
    (hr : ∀ q ∈ r, 0 ≤ q.1 ∧ q.1 ≤ 180000 ∧ 0 ≤ q.2 ∧ q.2 ≤ 180000)
    {p : ℝ × ℝ} (hp : p ∈ support (collarRoute reflected r)) :
    inPointBox (270000, 270000) 90000 p := by
  apply support_inPointBox_of_points (r := collarRoute reflected r) ?_ hp
  intro q hq
  rw [collarRoute_eq_map] at hq
  obtain ⟨q, hqr, rfl⟩ := List.mem_map.mp hq
  exact collarPoint_in_innerBox reflected (hr q hqr)

/-- Extend an inner clause-to-boundary prefix along the reversed annular connector. -/
def collarPrefixRoute (s : PortAssignment) (i : Fin 3) (r : Route) : Route :=
  collarRoute (collarReflected s) r ++ ((collarRoutes s).getD i []).reverse.tail

private theorem collarPrefix_join_endpoints {s : PortAssignment} (hs : s.Distinct)
    {i : Fin 3} {r : Route} (hr : r.getLast? = some (innerTemplatePort i)) :
    (collarRoute (collarReflected s) r).getLast? =
        some (collarInnerPort (collarReflected s) i) ∧
      ((collarRoutes s).getD i []).reverse.head? =
        some (collarInnerPort (collarReflected s) i) := by
  constructor
  · rw [collarRoute_eq_map, List.getLast?_map, hr]
    exact congrArg some (collarPoint_innerTemplatePort _ _)
  · simpa only [List.head?_reverse] using ((collar_check s hs).2 i).2.1

/-- Extending a local prefix preserves proper orthogonality. -/
theorem isOrthogonal_collarPrefixRoute {s : PortAssignment} (hs : s.Distinct)
    {i : Fin 3} {r : Route} (hr : r.getLast? = some (innerTemplatePort i))
    (ho : IsOrthogonal r) : IsOrthogonal (collarPrefixRoute s i r) := by
  have he := collarPrefix_join_endpoints hs hr
  exact isOrthogonal_join he.1 he.2 (isOrthogonal_collarRoute _ ho)
    ((isOrthogonal_reverse_iff _).2 (((collar_check s hs).2 i).2.2.1))

/-- The support of an extended prefix is precisely the union of its placed local support
and its annular connector. -/
theorem support_collarPrefixRoute {s : PortAssignment} (hs : s.Distinct)
    {i : Fin 3} {r : Route} (hr : r.getLast? = some (innerTemplatePort i)) :
    support (collarPrefixRoute s i r) = support (collarRoute (collarReflected s) r) ∪
      support ((collarRoutes s).getD i []) := by
  have he := collarPrefix_join_endpoints hs hr
  rw [collarPrefixRoute, support_join he.1 he.2, support_reverse]

/-- Local prefix and annular connector glue to a continuously simple route. -/
theorem isSimple_collarPrefixRoute {s : PortAssignment} (hs : s.Distinct)
    {i : Fin 3} {r : Route} (hr : r.getLast? = some (innerTemplatePort i))
    (hsr : IsSimple r)
    (hb : ∀ q ∈ r, 0 ≤ q.1 ∧ q.1 ≤ 180000 ∧ 0 ≤ q.2 ∧ q.2 ≤ 180000) :
    IsSimple (collarPrefixRoute s i r) := by
  have he := collarPrefix_join_endpoints hs hr
  refine isSimple_join he.1 he.2 (isSimple_collarRoute _ hsr)
    ((isSimple_reverse_iff _).2 (collar_isSimple hs i)) ?_
  intro p hp hq
  rw [support_reverse] at hq
  exact collar_core_contact hs hq (collarRoute_in_innerBox _ hb hp)

/-- Extending a prefix adds exactly the annular connector's wire length. -/
theorem wireLength_collarPrefixRoute {s : PortAssignment} (hs : s.Distinct)
    {i : Fin 3} {r : Route} (hr : r.getLast? = some (innerTemplatePort i)) :
    wireLength (collarPrefixRoute s i r) =
      wireLength r + wireLength ((collarRoutes s).getD i []) := by
  have he := collarPrefix_join_endpoints hs hr
  rw [collarPrefixRoute, wireLength_join he.1 he.2, wireLength_collarRoute, wireLength_reverse]

/-- Extending a prefix adds exactly the annular connector's listed segments. -/
theorem consecutivePairs_length_collarPrefixRoute {s : PortAssignment} (hs : s.Distinct)
    {i : Fin 3} {r : Route} (hr : r.getLast? = some (innerTemplatePort i)) :
    (collarPrefixRoute s i r).consecutivePairs.length =
      r.consecutivePairs.length + ((collarRoutes s).getD i []).consecutivePairs.length := by
  have he := collarPrefix_join_endpoints hs hr
  rw [collarPrefixRoute, consecutivePairs_join he.1 he.2, List.length_append,
    consecutivePairs_length_collarRoute, consecutivePairs_length_reverse]

/-- A placed core route avoiding an inner port is disjoint from that port's annular connector.
-/
theorem disjoint_collarRoute_connector {s : PortAssignment} (hs : s.Distinct)
    {i : Fin 3} {r : Route}
    (hb : ∀ q ∈ r, 0 ≤ q.1 ∧ q.1 ≤ 180000 ∧ 0 ≤ q.2 ∧ q.2 ≤ 180000)
    (hi : realPoint (innerTemplatePort i) ∉ support r) :
    Disjoint (support (collarRoute (collarReflected s) r))
      (support ((collarRoutes s).getD i [])) := by
  rw [Set.disjoint_left]
  intro p hp hq
  have hport := collar_core_contact hs hq (collarRoute_in_innerBox _ hb hp)
  have he : collarReal (collarReflected s) (realPoint (innerTemplatePort i)) =
      realPoint (collarInnerPort (collarReflected s) i) := by
    rw [← realPoint_collarPoint, collarPoint_innerTemplatePort]
  rw [hport, ← he] at hp
  exact hi ((mem_support_collarRoute_iff _ r _).1 hp)

/-- Intersections between two distinct extended prefixes come entirely from intersections
of their original local routes. The two local routes must avoid each other's inner port. -/
theorem collarPrefixRoute_contact {s : PortAssignment} (hs : s.Distinct)
    {i j : Fin 3} (hij : i ≠ j) {r t : Route}
    (hr : r.getLast? = some (innerTemplatePort i))
    (ht : t.getLast? = some (innerTemplatePort j))
    (hbr : ∀ q ∈ r, 0 ≤ q.1 ∧ q.1 ≤ 180000 ∧ 0 ≤ q.2 ∧ q.2 ≤ 180000)
    (hbt : ∀ q ∈ t, 0 ≤ q.1 ∧ q.1 ≤ 180000 ∧ 0 ≤ q.2 ∧ q.2 ≤ 180000)
    (hri : realPoint (innerTemplatePort j) ∉ support r)
    (htj : realPoint (innerTemplatePort i) ∉ support t)
    {p : ℝ × ℝ} (hp : p ∈ support (collarPrefixRoute s i r))
    (hq : p ∈ support (collarPrefixRoute s j t)) :
    ∃ q ∈ support r, q ∈ support t ∧ p = collarReal (collarReflected s) q := by
  rw [support_collarPrefixRoute hs hr] at hp
  rw [support_collarPrefixRoute hs ht] at hq
  rcases hp with hp | hp <;> rcases hq with hq | hq
  · rw [support_collarRoute] at hp hq
    obtain ⟨x, hx, hxp⟩ := hp
    obtain ⟨y, hy, hyp⟩ := hq
    have hxy := collarReal_injective (collarReflected s) (hxp.trans hyp.symm)
    subst y
    exact ⟨x, hx, hy, hxp.symm⟩
  · exact False.elim (Set.disjoint_left.mp (disjoint_collarRoute_connector hs hbr hri) hp hq)
  · exact False.elim (Set.disjoint_left.mp (disjoint_collarRoute_connector hs hbt htj) hq hp)
  · exact False.elim (Set.disjoint_left.mp (collar_disjoint hs hij) hp hq)

/-- An extended prefix avoids a placed inner-template vertex when its local route avoids
that vertex and it is not the prefix's own boundary terminal. -/
theorem collarPrefixRoute_not_mem_corePoint {s : PortAssignment} (hs : s.Distinct)
    {i : Fin 3} {r : Route} (hr : r.getLast? = some (innerTemplatePort i))
    {q : Point} (hq : 0 ≤ q.1 ∧ q.1 ≤ 180000 ∧ 0 ≤ q.2 ∧ q.2 ≤ 180000)
    (hqi : q ≠ innerTemplatePort i) (hn : realPoint q ∉ support r) :
    realPoint (collarPoint (collarReflected s) q) ∉ support (collarPrefixRoute s i r) := by
  intro hp
  rw [support_collarPrefixRoute hs hr] at hp
  rcases hp with hp | hp
  · rw [realPoint_collarPoint] at hp
    exact hn ((mem_support_collarRoute_iff _ _ _).1 hp)
  · have he := collar_core_contact hs hp (collarPoint_in_innerBox _ hq)
    rw [← collarPoint_innerTemplatePort] at he
    exact hqi (collarPoint_injective _ (realPoint_injective he))

/-- The perimeter of the outer collar square. -/
def collarBoundaryRoute : Route :=
  [(0, 0), (540000, 0), (540000, 540000), (0, 540000), (0, 0)]

private theorem collar_boundary_check : ∀ s : PortAssignment, s.Distinct → ∀ i : Fin 3,
    routeContactCheck [collarOuterPort (s.side i)] ((collarRoutes s).getD i [])
      collarBoundaryRoute = true := by
  decide +kernel

private theorem collar_boundary_inner_check :
    routeBoxContactCheck [] collarBoundaryRoute (270000, 270000) 90000 = true := by
  decide +kernel

/-- The collar's full support meets its outer perimeter only at its own assigned port. -/
theorem collar_outer_boundary_contact {s : PortAssignment} (hs : s.Distinct) {i : Fin 3}
    {p : ℝ × ℝ} (hp : p ∈ support ((collarRoutes s).getD i []))
    (hb : p ∈ support collarBoundaryRoute) : p = realPoint (collarOuterPort (s.side i)) := by
  obtain ⟨q, hq, hpq⟩ := routeContactCheck_sound (collar_boundary_check s hs i) hp hb
  exact List.mem_singleton.mp hq ▸ hpq

/-- The full support of an extended prefix meets the outer perimeter only at its assigned
source port. -/
theorem collarPrefixRoute_outer_boundary_contact {s : PortAssignment} (hs : s.Distinct)
    {i : Fin 3} {r : Route} (hr : r.getLast? = some (innerTemplatePort i))
    (hbr : ∀ q ∈ r, 0 ≤ q.1 ∧ q.1 ≤ 180000 ∧ 0 ≤ q.2 ∧ q.2 ≤ 180000)
    {p : ℝ × ℝ} (hp : p ∈ support (collarPrefixRoute s i r))
    (hb : p ∈ support collarBoundaryRoute) : p = realPoint (collarOuterPort (s.side i)) := by
  rw [support_collarPrefixRoute hs hr] at hp
  rcases hp with hp | hp
  · obtain ⟨q, hq, _⟩ := routeBoxContactCheck_sound collar_boundary_inner_check hb
      (collarRoute_in_innerBox _ hbr hp)
    exact False.elim (List.not_mem_nil hq)
  · exact collar_outer_boundary_contact hs hp hb

/-- Position of an exposed variable in the ordered terminal list, with an irrelevant default
for malformed local data containing more than three terminals. -/
def terminalIndex (g : LocalGeometry) (v : ℕ) : Fin 3 :=
  ⟨g.terminalVariables.idxOf v % 3, Nat.mod_lt _ (by decide)⟩

/-- Place a finite prefix template and extend its source incidences to arbitrary ordered
outer sides. Source ghost positions follow those same outer ports; actual internal vertices
and all clause positions receive the common affine placement. -/
def collaredPrefixGeometry (g : LocalGeometry) (s : PortAssignment) : LocalGeometry where
  size := 540000
  variablePositions := g.variablePositions.zipIdx.map fun pi =>
    if pi.2 ∈ g.terminalVariables then collarOuterPort (s.side (terminalIndex g pi.2))
    else collarPoint (collarReflected s) pi.1
  clausePositions := g.clausePositions.map (collarPoint (collarReflected s))
  incidenceRoutes := g.incidenceRoutes.map fun e =>
    (e.1, e.2.1,
      if e.2.1 ∈ g.terminalVariables then collarPrefixRoute s (terminalIndex g e.2.1) e.2.2
      else collarRoute (collarReflected s) e.2.2)
  terminalVariables := g.terminalVariables
  boundaryPorts := g.terminalVariables.zipIdx.map fun vi =>
    collarOuterPort (s.side ⟨vi.2 % 3, Nat.mod_lt _ (by decide)⟩)
  accessRoutes := []

end Cslib.Complexity.SAT.ExactOne
