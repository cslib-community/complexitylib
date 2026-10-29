/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SAT.Planar.PairedCrossoverLayoutChecks
public import Complexity.Foundations.Geometry.Orthogonal.Simple
import Mathlib.Data.List.Zip
import Mathlib.Tactic.Linarith

/-!
# Certified continuous orthogonal paired-port crossover

The finite checks for the fixed degree-three CNF template certify entire real supports.
Its 57 variable vertices and 78 clause vertices are distinct. Its 162 incidence routes are simple,
orthogonal, avoid nonincident vertices, and meet only at common graph endpoints. Their total
wire length is 2192. Eight mutually disjoint access routes connect degree-two terminals to the
boundary of `[0,240]²`, and meet the core only at the corresponding terminal. Each terminal
therefore accommodates exactly one external clause occurrence.

## Main definitions

This module uses the fixed table from `PairedCrossoverLayoutData` and the shared `Orthogonal` route
and continuous support semantics.

## Main results

* `Cslib.Logic.PL.CNF.PairedCrossover.incidence_simple`: continuous segment simplicity.
* `Cslib.Logic.PL.CNF.PairedCrossover.routes_contact`: intersections are common endpoints.
* `Cslib.Logic.PL.CNF.PairedCrossover.access_contact`: access meets the core only at its terminal.
* `Cslib.Logic.PL.CNF.PairedCrossover.access_boundary_isolation`: only ports touch the boundary.

## References

* David Lichtenstein, *Planar Formulae and Their Uses*, Figs. 4–5 [Lichtenstein1982].
* MIT–ULB CompGeom Group, *Undecidability of Tiling with a Tromino*, Fig. 8(b) [Tromino2025].

The paired-terminal modification and its continuous orthogonal certificates are original.
-/

@[expose] public section

namespace Cslib.Logic.PL.CNF.PairedCrossover

open Orthogonal

/-- Every real point of the core drawing is strictly inside the outer 240-by-240 box. -/
theorem core_support_interior {e : ℕ × Variable × Route} (he : e ∈ incidenceRoutes)
    {p : ℝ × ℝ} (hp : p ∈ support e.2.2) :
    0 < p.1 ∧ p.1 < 240 ∧ 0 < p.2 ∧ p.2 < 240 := by
  have h := support_bounds_of_points (x₀ := 20) (x₁ := 220) (y₀ := 20) (y₁ := 220)
    (core_bounds e he) hp
  norm_num at h
  exact ⟨by linarith [h.1], by linarith [h.2.1], by linarith [h.2.2.1], by linarith [h.2.2.2]⟩

/-- Distinct segments of a route intersect only at their consecutive shared bend. -/
theorem incidence_simple {e : ℕ × Variable × Route} (he : e ∈ incidenceRoutes)
    {a b : Point × Point} (ha : a ∈ e.2.2.consecutivePairs)
    (hb : b ∈ e.2.2.consecutivePairs) (hne : a ≠ b)
    {p : ℝ × ℝ} (hp : p ∈ segment a.1 a.2) (hq : p ∈ segment b.1 b.2) :
    ∃ q ∈ consecutiveContact a b, p = realPoint q :=
  segmentContactCheck_sound (incidence_simple_check e he a ha b hb hne) hp hq

/-- Every incidence route is simple in the shared continuous polygonal-route semantics. -/
theorem incidence_isSimple {e : ℕ × Variable × Route} (he : e ∈ incidenceRoutes) :
    IsSimple e.2.2 := by
  refine ⟨incidence_points_nodup e he, ?_⟩
  intro a ha b hb hne p hp hq
  obtain ⟨q, hq, hpq⟩ := incidence_simple he ha hb hne hp hq
  unfold consecutiveContact at hq
  split_ifs at hq with h h'
  · have hqa : q = a.2 := List.mem_singleton.mp hq
    subst q
    exact ⟨Or.inr hpq, Or.inl (hpq.trans (congrArg realPoint h))⟩
  · have hqa : q = a.1 := List.mem_singleton.mp hq
    subst q
    exact ⟨Or.inl hpq, Or.inr (hpq.trans (congrArg realPoint h'.symm))⟩
  · exact False.elim (List.not_mem_nil hq)

/-- Every continuous intersection of distinct incidence routes is a shared graph endpoint. -/
theorem routes_contact {e f : ℕ × Variable × Route}
    (he : e ∈ incidenceRoutes) (hf : f ∈ incidenceRoutes) (hne : e ≠ f)
    {p : ℝ × ℝ} (hp : p ∈ support e.2.2) (hq : p ∈ support f.2.2) :
    ∃ q ∈ commonEndpoints e f, p = realPoint q :=
  routeContactCheck_sound (routes_contact_check e he f hf hne) hp hq

/-- Continuous incidence routes avoid every nonincident variable vertex. -/
theorem variable_not_mem_support {e : ℕ × Variable × Route}
    (he : e ∈ incidenceRoutes) {v : Variable} (hv : v ≠ e.2.1) :
    realPoint (variablePosition v) ∉ support e.2.2 :=
  not_mem_support_of_routeContactCheck (variable_avoidance_check e he v hv)

/-- Continuous incidence routes avoid every nonincident clause vertex. -/
theorem clause_not_mem_support {e : ℕ × Variable × Route}
    (he : e ∈ incidenceRoutes) {i : Fin 78} (hi : i.val ≠ e.1) :
    realPoint (clausePosition i) ∉ support e.2.2 :=
  not_mem_support_of_routeContactCheck (clause_avoidance_check e he i hi)

/-- Every literal incidence appears exactly once in the route list. -/
theorem incidenceEndpoints_nodup :
    (incidenceRoutes.map fun e => (e.1, e.2.1)).Nodup := by decide +kernel

/-- Every variable vertex lies in the core rectangle. -/
theorem variable_bounds : ∀ v, 20 ≤ (variablePosition v).1 ∧ (variablePosition v).1 ≤ 220 ∧
    20 ≤ (variablePosition v).2 ∧ (variablePosition v).2 ≤ 220 := by decide +kernel

/-- Every clause vertex lies in the core rectangle. -/
theorem clause_bounds : ∀ p ∈ clausePositions,
    20 ≤ p.1 ∧ p.1 ≤ 220 ∧ 20 ≤ p.2 ∧ p.2 ≤ 220 := by decide +kernel

/-- Each of the 57 variable names is genuinely used by the fixed formula. -/
theorem variables_used : ∀ v, v ∈ formula.vars := by decide +kernel

/-- No access route visits any other variable vertex. -/
theorem access_variable_avoidance_check : ∀ s l v, v ≠ terminal s l →
    routeContactCheck [] (accessRoute s l) [variablePosition v] = true := by decide +kernel

/-- No access route visits a clause vertex. -/
theorem access_clause_avoidance_check : ∀ s l, ∀ p ∈ clausePositions,
    routeContactCheck [] (accessRoute s l) [p] = true := by decide +kernel

/-- The full real access route avoids every other variable vertex. -/
theorem access_variable_not_mem {s : Fin 4} {l : Fin 2} {v : Variable}
    (hv : v ≠ terminal s l) :
    realPoint (variablePosition v) ∉ support (accessRoute s l) :=
  not_mem_support_of_routeContactCheck (access_variable_avoidance_check s l v hv)

/-- The full real access route avoids every clause vertex. -/
theorem access_clause_not_mem {s : Fin 4} {l : Fin 2} {p : Point}
    (hp : p ∈ clausePositions) :
    realPoint p ∉ support (accessRoute s l) :=
  not_mem_support_of_routeContactCheck (access_clause_avoidance_check s l p hp)

/-- Each access route has one segment and 20 units of wire length. -/
theorem access_route_sizes : ∀ s l, (accessRoute s l).consecutivePairs.length = 1 ∧
    wireLength (accessRoute s l) = 20 := PairedPorts.access_route_sizes

/-- Including all eight accesses gives 415 segments and total wire length 2352. -/
theorem full_route_sizes :
    (incidenceRoutes.map fun e => e.2.2.consecutivePairs.length).sum +
      ((List.finRange 4).flatMap fun s => (List.finRange 2).map fun l =>
        (accessRoute s l).consecutivePairs.length).sum = 415 ∧
    (incidenceRoutes.map fun e => wireLength e.2.2).sum +
      ((List.finRange 4).flatMap fun s => (List.finRange 2).map fun l =>
        wireLength (accessRoute s l)).sum = 2352 := by
  rw [route_sizes.1, route_sizes.2]
  decide +kernel

/-- Each straight access is simple over its full real support. -/
theorem access_isSimple (s : Fin 4) (l : Fin 2) : IsSimple (accessRoute s l) :=
  PairedPorts.access_isSimple s l

/-- Distinct accesses have disjoint full real support. -/
theorem access_disjoint {p q : PairedPorts.Port} (h : p ≠ q) :
    Disjoint (support (accessRoute p.1 p.2)) (support (accessRoute q.1 q.2)) :=
  PairedPorts.access_disjoint h

/-- Every continuous contact between an access and the core is its associated port. -/
theorem access_contact {s : Fin 4} {l : Fin 2} {e : ℕ × Variable × Route}
    (he : e ∈ incidenceRoutes) {p : ℝ × ℝ}
    (hp : p ∈ support (accessRoute s l)) (hq : p ∈ support e.2.2) :
    e.2.1 = terminal s l ∧ p = realPoint (variablePosition (terminal s l)) := by
  obtain ⟨q, hq, hpq⟩ := routeContactCheck_sound (access_contact_check s l e he) hp hq
  split_ifs at hq with h
  · have hq' : q = variablePosition (terminal s l) := List.mem_singleton.mp hq
    exact ⟨h, hq' ▸ hpq⟩
  · exact False.elim (List.not_mem_nil hq)

/-- Only the designated boundary point of an access lies on the outer box boundary. -/
theorem access_boundary_isolation {s : Fin 4} {l : Fin 2} {p : ℝ × ℝ}
    (hp : p ∈ support (accessRoute s l)) :
    0 ≤ p.1 ∧ p.1 ≤ 240 ∧ 0 ≤ p.2 ∧ p.2 ≤ 240 ∧
      (p.1 = 0 ∨ p.1 = 240 ∨ p.2 = 0 ∨ p.2 = 240 → p = realPoint (boundaryPort s l)) :=
  PairedPorts.access_boundary_isolation hp

end Cslib.Logic.PL.CNF.PairedCrossover
