/-
Copyright (c) 2026 Erik Demaine, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SAT.ExactOne.Geometry
public import Complexity.Foundations.Geometry.Orthogonal.Subdivision

/-!
# Source-boundary prefixes for local clause replacements

Each source placeholder is moved from its private local position to the corresponding boundary
port. Its sole incidence is extended through the reversed access route. The old placeholder is
then an ordinary interior bend, rather than a graph vertex. The finite certificates check the
actual resulting prefixes, including simplicity and the restriction that a route can touch the
box boundary only at its own variable endpoint.

## Main definitions

* `LocalGeometry.toPrefix`: move source placeholders to boundary ports and extend their incidences.
* `LocalGeometry.PrefixCheck`: finite continuous certificates for such route prefixes.

## Main results

* `LocalGeometry.prefix_boundary_contact`: only the variable endpoint can touch the boundary.

## References

These are original geometric certificates for the cited exact-one clause constructions.
-/

@[expose] public section

namespace Cslib.Complexity.SAT.ExactOne

open Orthogonal

namespace LocalGeometry

/-- Check only consecutive segment pairs for two proper routes after a bounding-box precheck.
Listed points already belong to such segments, so including their separate degenerate pieces
would duplicate this work. -/
def segmentRouteContactCheck (allowed : List Point) (r s : Route) : Bool :=
  routeBoxDisjoint r s ||
    (r.consecutivePairs.all fun e => s.consecutivePairs.all fun f =>
      segmentContactCheck allowed e.1 e.2 f.1 f.2)

/-- Consecutive-segment checking controls the full real support of proper routes. -/
theorem segmentRouteContactCheck_sound {allowed : List Point} {r s : Route}
    (hr : 2 ≤ r.length) (hs : 2 ≤ s.length)
    (h : segmentRouteContactCheck allowed r s = true) {p : ℝ × ℝ}
    (hp : p ∈ support r) (hq : p ∈ support s) :
    ∃ q ∈ allowed, p = realPoint q := by
  rw [segmentRouteContactCheck, Bool.or_eq_true] at h
  rcases h with hbox | hseg
  · exact False.elim (Set.disjoint_left.mp (disjoint_support_of_routeBoxDisjoint hbox) hp hq)
  · obtain ⟨e, he, hp⟩ := mem_support_segment hr hp
    obtain ⟨f, hf, hq⟩ := mem_support_segment hs hq
    exact segmentContactCheck_sound
      (List.all_eq_true.mp (List.all_eq_true.mp hseg e he) f hf) hp hq

/-- The closed polygonal boundary of a local cell. -/
def boundaryRoute (g : LocalGeometry) : Route :=
  [(0, 0), (g.size, 0), (g.size, g.size), (0, g.size), (0, 0)]

/-- Move each source placeholder to its boundary port and extend its unique incidence through
the old placeholder position. `terminalVariables` retains the boundary placeholders' indices. -/
def toPrefix (g : LocalGeometry) : LocalGeometry where
  size := g.size
  variablePositions := g.variablePositions.zipIdx.map fun (p, i) =>
    if i ∈ g.terminalVariables then
      g.boundaryPorts.getD (g.terminalVariables.idxOf i) (0, 0) else p
  clausePositions := g.clausePositions
  incidenceRoutes := g.incidenceRoutes.map fun e =>
    (e.1, e.2.1, if e.2.1 ∈ g.terminalVariables then
      e.2.2 ++ (g.accessRoutes.getD (g.terminalVariables.idxOf e.2.1) []).reverse.tail
      else e.2.2)
  terminalVariables := g.terminalVariables
  boundaryPorts := g.boundaryPorts
  accessRoutes := []

/-- A finite certificate for local incidence routes whose source ends lie on the cell boundary.
Full route contacts, nonincident vertices and the complete cell boundary are checked. -/
def PrefixCheck (g : LocalGeometry) : Prop :=
  (g.variablePositions ++ g.clausePositions).Nodup ∧
  (g.incidenceRoutes.map fun e => (e.1, e.2.1)).Nodup ∧
  (∀ e ∈ g.incidenceRoutes,
    e.1 < g.clausePositions.length ∧ e.2.1 < g.variablePositions.length ∧
      e.2.2.head? = some (g.clausePosition e.1) ∧
      e.2.2.getLast? = some (g.variablePosition e.2.1) ∧
      IsOrthogonal e.2.2 ∧ SimpleCheck e.2.2 ∧ 2 ≤ e.2.2.length ∧
      (∀ p ∈ e.2.2, 0 ≤ p.1 ∧ p.1 ≤ g.size ∧ 0 ≤ p.2 ∧ p.2 ≤ g.size) ∧
      ∀ p ∈ e.2.2.dropLast, 0 < p.1 ∧ p.1 < g.size ∧ 0 < p.2 ∧ p.2 < g.size) ∧
  (∀ e ∈ g.incidenceRoutes, ∀ f ∈ g.incidenceRoutes, e ≠ f →
    segmentRouteContactCheck (g.commonEndpoints e f) e.2.2 f.2.2 = true) ∧
  (∀ e ∈ g.incidenceRoutes, ∀ v : Fin g.variablePositions.length, v.val ≠ e.2.1 →
    routeContactCheck [] e.2.2 [g.variablePosition v] = true) ∧
  (∀ e ∈ g.incidenceRoutes, ∀ i : Fin g.clausePositions.length, i.val ≠ e.1 →
    routeContactCheck [] e.2.2 [g.clausePosition i] = true) ∧
  ∀ e ∈ g.incidenceRoutes,
    segmentRouteContactCheck [g.variablePosition e.2.1] e.2.2 g.boundaryRoute = true

instance (g : LocalGeometry) : Decidable (PrefixCheck g) := by
  unfold PrefixCheck
  repeat' refine @instDecidableAnd _ _ ?_ ?_
  all_goals infer_instance

/-- Every checked prefix has its prescribed clause and variable endpoints. -/
theorem prefix_incidence_endpoints {g : LocalGeometry} (h : PrefixCheck g)
    {e : LocalIncidence} (he : e ∈ g.incidenceRoutes) :
    e.1 < g.clausePositions.length ∧ e.2.1 < g.variablePositions.length ∧
      e.2.2.head? = some (g.clausePosition e.1) ∧
      e.2.2.getLast? = some (g.variablePosition e.2.1) := by
  have h' := h.2.2.1 e he
  exact ⟨h'.1, h'.2.1, h'.2.2.1, h'.2.2.2.1⟩

/-- Every checked prefix is properly orthogonal. -/
theorem prefix_incidence_orthogonal {g : LocalGeometry} (h : PrefixCheck g)
    {e : LocalIncidence} (he : e ∈ g.incidenceRoutes) : IsOrthogonal e.2.2 :=
  (h.2.2.1 e he).2.2.2.2.1

/-- Every checked prefix is simple on its full continuous support. -/
theorem prefix_incidence_isSimple {g : LocalGeometry} (h : PrefixCheck g)
    {e : LocalIncidence} (he : e ∈ g.incidenceRoutes) : IsSimple e.2.2 :=
  isSimple_of_check ((h.2.2.1 e he).2.2.2.2.2.1)

/-- Every point listed in a checked prefix lies in its closed cell. -/
theorem prefix_incidence_bounds {g : LocalGeometry} (h : PrefixCheck g)
    {e : LocalIncidence} (he : e ∈ g.incidenceRoutes) :
    ∀ p ∈ e.2.2, 0 ≤ p.1 ∧ p.1 ≤ g.size ∧ 0 ≤ p.2 ∧ p.2 ≤ g.size :=
  (h.2.2.1 e he).2.2.2.2.2.2.2.1

/-- Every checked prefix has at least one proper consecutive segment. -/
theorem prefix_incidence_length {g : LocalGeometry} (h : PrefixCheck g)
    {e : LocalIncidence} (he : e ∈ g.incidenceRoutes) : 2 ≤ e.2.2.length :=
  (h.2.2.1 e he).2.2.2.2.2.2.1

/-- Checked prefixes meet only at shared graph endpoints. -/
theorem prefix_routes_contact {g : LocalGeometry} (h : PrefixCheck g)
    {e f : LocalIncidence} (he : e ∈ g.incidenceRoutes) (hf : f ∈ g.incidenceRoutes)
    (hne : e ≠ f) {p : ℝ × ℝ} (hp : p ∈ support e.2.2) (hq : p ∈ support f.2.2) :
    ∃ q ∈ g.commonEndpoints e f, p = realPoint q :=
  segmentRouteContactCheck_sound (prefix_incidence_length h he)
    (prefix_incidence_length h hf) (h.2.2.2.1 e he f hf hne) hp hq

/-- A checked prefix avoids every nonincident variable vertex. -/
theorem prefix_variable_not_mem_support {g : LocalGeometry} (h : PrefixCheck g)
    {e : LocalIncidence} (he : e ∈ g.incidenceRoutes)
    {v : Fin g.variablePositions.length} (hv : v.val ≠ e.2.1) :
    realPoint (g.variablePosition v) ∉ support e.2.2 :=
  not_mem_support_of_routeContactCheck (h.2.2.2.2.1 e he v hv)

/-- A checked prefix avoids every nonincident clause vertex. -/
theorem prefix_clause_not_mem_support {g : LocalGeometry} (h : PrefixCheck g)
    {e : LocalIncidence} (he : e ∈ g.incidenceRoutes)
    {i : Fin g.clausePositions.length} (hi : i.val ≠ e.1) :
    realPoint (g.clausePosition i) ∉ support e.2.2 :=
  not_mem_support_of_routeContactCheck (h.2.2.2.2.2.1 e he i hi)

/-- The variable endpoint is the only permitted contact with the full cell boundary. -/
theorem prefix_boundary_contact {g : LocalGeometry} (h : PrefixCheck g)
    {e : LocalIncidence} (he : e ∈ g.incidenceRoutes)
    {p : ℝ × ℝ} (hp : p ∈ support e.2.2) (hq : p ∈ support g.boundaryRoute) :
    p = realPoint (g.variablePosition e.2.1) := by
  obtain ⟨q, hq, hpq⟩ := segmentRouteContactCheck_sound (prefix_incidence_length h he)
    (by simp [boundaryRoute]) (h.2.2.2.2.2.2 e he) hp hq
  exact List.mem_singleton.mp hq ▸ hpq

end LocalGeometry

end Cslib.Complexity.SAT.ExactOne
